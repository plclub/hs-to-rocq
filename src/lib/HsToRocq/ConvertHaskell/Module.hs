{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns, LambdaCase, RecordWildCards, TypeApplications, FlexibleContexts, DeriveDataTypeable, OverloadedLists, OverloadedStrings, ScopedTypeVariables, MultiWayIf, RankNTypes  #-}

#include "ghc-compat.h"

module HsToRocq.ConvertHaskell.Module (
  -- * Convert whole module graphs and modules
  ConvertedModule(..),
  convertModules, convertModule,
  -- ** Extract all the declarations from a module
  ModuleDeclarations(..), moduleDeclarations,
) where

import Control.Lens

import Data.Foldable
import Data.Traversable
import HsToRocq.Util.Monad
import Data.Function
import Data.Maybe
import qualified Data.List.NonEmpty
import Data.List.NonEmpty (NonEmpty (..), fromList)
import Data.List (partition, sortBy)
import HsToRocq.Util.List
import HsToRocq.Util.Containers

import Data.Generics (Data, everywhere, mkT, toConstr, showConstr)

import Control.Monad.Reader

import Control.Exception (SomeException)
import qualified Data.Set as S
import qualified Data.Map as M

import qualified Data.Text as T

import HsToRocq.Util.FVs
import HsToRocq.Rocq.FreeVars
import HsToRocq.Rocq.Gallina
import HsToRocq.Rocq.Gallina.Util

import GHC hiding (Name)
#if __GLASGOW_HASKELL__ >= 806
import HsToRocq.Util.GHC.HsTypes (noExtCon)
#endif
import HsToRocq.Util.GHC.Module
#if __GLASGOW_HASKELL__ >= 900
import GHC.Data.Bag (bagToList)
#else
import Bag
#endif

import HsToRocq.Edits.Types
import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.TypeInfo (lookupConstructorType)
import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import System.IO (hPutStrLn, stderr)
import HsToRocq.ConvertHaskell.InfixNames
import HsToRocq.ConvertHaskell.Variables
import HsToRocq.ConvertHaskell.Definitions
import HsToRocq.ConvertHaskell.Expr
import HsToRocq.ConvertHaskell.Sigs
import HsToRocq.ConvertHaskell.Declarations.TyCl
import HsToRocq.ConvertHaskell.Declarations.Instances
import HsToRocq.ConvertHaskell.Declarations.Notations
import HsToRocq.ConvertHaskell.Axiomatize
import HsToRocq.ConvertHaskell.TypeEnv.Instances
import HsToRocq.Rocq.Preamble
import HsToRocq.Rocq.Pretty (textP)

-- GHC 9.x: Exception module's gcatch replaced by MonadCatch;
-- getLoc replaced by getLocA for GenLocated SrcSpanAnn.
#if __GLASGOW_HASKELL__ >= 900
import qualified Control.Monad.Catch as MC
gcatch :: (MC.MonadCatch m, MC.Exception e) => m a -> (e -> m a) -> m a
gcatch = MC.catch

#define getLoc getLocA
#endif

--------------------------------------------------------------------------------

data ConvertedModuleDeclarations =
  ConvertedModuleDeclarations { convertedTyClDecls    :: ![Sentence]
                              , convertedValDecls     :: ![Sentence]
                              , convertedClsInstDecls :: ![Sentence]
                              , convertedAddedTyCls   :: ![Sentence]
                              , convertedAddedDecls   :: ![Sentence]
                              }
  deriving (Eq, Ord, Show, Data)


annotateFixpoint :: [Binder] -> Maybe Term -> [Binder]
annotateFixpoint [] _ = []
annotateFixpoint (ExplicitBinder n:tl) (Just (Arrow x y)) =
  Typed Generalizable Explicit (fromList [n]) x:annotateFixpoint tl (Just y)
annotateFixpoint (ImplicitBinders ns:tl) (Just (Arrow x y)) =
  Typed Generalizable Implicit ns x:annotateFixpoint tl (Just y)
annotateFixpoint (a:tl) (Just (Arrow _ y)) = a:annotateFixpoint tl (Just y)
annotateFixpoint x _ = x

convertedBindingName :: ConvertedBinding -> Maybe Qualid
convertedBindingName cb = case cb of
  ConvertedDefinitionBinding cd -> Just (_convDefName cd)
  ConvertedPatternBinding _ _ -> Nothing
  ConvertedAxiomBinding name _ -> Just name
  RedefinedBinding name _ -> Just name
  SkippedBinding name -> Just name

convertBinding
  :: ConversionMonad r m
  => M.Map Qualid Signature -> ConvertedBinding -> m [Sentence]
convertBinding sigs (ConvertedDefinitionBinding cdef@ConvertedDefinition{_convDefName = name}) =
  withCurrentDefinition name $ do
    t  <- view (edits.termination.at name)
    obl <- view (edits.obligations.at name)
    useEqs <- view (edits.equations.contains name)
    useProgram <- useProgramHere
    if | useEqs                           -- turn into Equations definition
       -> (++ [ NotationSentence n | n <- buildInfixNotations sigs name ]) <$> toEquationsSentence cdef t
       | Just (WellFoundedTA order) <- t  -- turn into Program Fixpoint
       ->  pure <$> toProgramFixpointSentence cdef (fromWFOrder order) obl
       | otherwise                   -- no edit
       -> let def = DefinitionDef Global (cdef^.convDefName)
                                         (cdef^.convDefArgs)
                                         (cdef^.convDefType)
                                         (cdef^.convDefBody) NotExistingClass
          in pure $
             (case cdef^.convDefBody of
                 Fix (FixOne (FixBody qual bind ord mterm term))
                   -> FixpointSentence (Fixpoint [FixBody qual (fromList $ (cdef^.convDefArgs) ++ annotateFixpoint (toList bind) (cdef^.convDefType)) ord mterm term] [])
                 _ -> if useProgram
                      then ProgramSentence (DefinitionSentence def) obl
                      else DefinitionSentence def)
             : [ NotationSentence n | n <- buildInfixNotations sigs (cdef^.convDefName) ]

convertBinding _ (ConvertedPatternBinding _ _) =
  -- Already skipped with a warning in 'HsToRocq.ConvertnHaskell.Expr.withHsBindName'
  pure [] -- convUnsupported' "top-level pattern bindings"

convertBinding _ (ConvertedAxiomBinding ax ty) = do
  useEqs <- view (edits.equations.contains ax)
  when useEqs $
    editFailure $ "equations edit for " ++ show ax ++ " conflicts with axiomatize (remove one)"
  pure [typedAxiom ax ty]

convertBinding _ (RedefinedBinding name def) = do
  useEqs <- view (edits.equations.contains name)
  when useEqs $
    editFailure $ "equations edit for " ++ show name ++ " conflicts with redefine (remove one)"
  [definitionSentence def] <$ case def of
    RocqInductiveDef _   -> editFailure   "cannot redefine a value definition into an Inductive"
    RocqInstanceDef  _   -> editFailure   "cannot redefine a value definition into an Instance"
    RocqAssertionDef apf -> editFailure $ "cannot redefine a value definition into " ++ anAssertionVariety apf
    RocqDefinitionDef _  -> pure ()
    RocqFixpointDef   _  -> pure ()
    RocqAxiomDef      _  -> pure ()

convertBinding _ (SkippedBinding name) = do
  useEqs <- view (edits.equations.contains name)
  when useEqs $
    editFailure $ "equations edit for " ++ show name ++ " conflicts with skip (remove one)"
  pure [CommentSentence . Comment $ "Skipping definition `" <> textP name <> "'"]

-- | Convert a function definition to use Coq Equations syntax.
-- Extracts match equations from the body and emits them as Equations clauses.
-- When the body has no match (direct expression), emits a single equation.
toEquationsSentence :: ConversionMonad r m
                    => ConvertedDefinition -> Maybe TerminationArgument -> m [Sentence]
toEquationsSentence cdef mterm = do
  let name = cdef^.convDefName
  -- Reject incompatible edits before inspecting the transformed recursive body.
  case mterm of
    Just Deferred ->
      editFailure $ "equations edit for " ++ show name ++ " is incompatible with deferred termination (use deferredFix instead)"
    Just Corecursive ->
      editFailure $ "equations edit for " ++ show name ++ " is incompatible with corecursive termination"
    _ -> pure ()
  let args = cdef^.convDefArgs
      mty  = cdef^.convDefType
      body = cdef^.convDefBody
      -- Decompose the body: extract binders and the inner expression.
      -- decomposeFixpoint handles both Fix (FixOne ...) and App wfFix [...].
      (allBinders, innerBody) = case decomposeFixpoint body of
        Just (_fixName, fixBinders, _fixTy, matchBody) ->
          (args ++ Data.List.NonEmpty.toList fixBinders, matchBody)
        Nothing ->
          let (funBinders, inner) = stripFun body
          in  (args ++ funBinders, inner)
      eqns = extractEqns innerBody
      whereClauses = extractWheres innerBody :: [EquationsWhere]
      matchEqns | null eqns = varPatternEqn allBinders innerBody
                | otherwise = eqns
      -- Annotate bare binders with types from the function signature.
      -- Equations requires explicit types on pattern-matching arguments.
      annotatedBinders = case mty of
        Just ty -> fst (annotateAndStrip allBinders ty)
        Nothing -> allBinders
      retTy = (snd . annotateAndStrip allBinders) =<< mty  -- flatten Maybe (Maybe Term)
  -- Substitute binder names → pattern variable names in each clause's RHS.
  -- When extractEqns extracts equations from an inner Match, the patterns may use
  -- different names than the Equations binders (e.g., an inner Match binds 'n'
  -- while the Equations binder is 'arg_0__').  In Equations syntax only the
  -- pattern-bound names are in scope, so binder-name references in the RHS must
  -- be replaced with the corresponding pattern variable name.
  when (null eqns && not (null matchEqns)) $
    liftIO $ hPutStrLn stderr $ "Note: equations edit for " ++ show name ++ " could not extract multi-clause equations from body (inner term is " ++ showConstr (toConstr innerBody) ++ "); emitting single equation"
  when (any isUnderscoredBinder annotatedBinders) $
    liftIO $ hPutStrLn stderr $ "Note: equations edit for " ++ show name ++ " has binders with inferred types (_); type signature may be incomplete"
  let binderNameList = [ n | b <- annotatedBinders
                           , not (isImplicitBinder b)
                           , Bare n <- toListOf binderIdents b ]
      -- Per-clause substitution: replace binder names with corresponding pattern
      -- variable names where they differ.
      renameClause cl =
        let subst = M.fromList
              [ (bn, pn) | (bn, QualidPat (Bare pn)) <- zip binderNameList (Data.List.NonEmpty.toList (ecPats cl))
                         , bn /= pn ]
            substTerm (Qualid (Bare n))
              | Just pn <- M.lookup n subst = Qualid (Bare pn)
            substTerm t = t
            substInTerm :: Term -> Term
            substInTerm = everywhere (mkT substTerm)
        in EquationsClause (ecPats cl) (substInTerm (ecRHS cl))
  -- Warn when binder count and pattern count disagree (zip truncation risk).
  forM_ matchEqns $ \cl -> do
    let nPats = Data.List.NonEmpty.length (ecPats cl)
    when (length binderNameList /= nPats) $
      liftIO $ hPutStrLn stderr $ "Warning: equations edit for " ++ show name
        ++ ": binder count (" ++ show (length binderNameList) ++ ") differs from pattern count ("
        ++ show nPats ++ ") in a clause; substitution may be incomplete"
  let renamedEqns = map renameClause matchEqns
  -- Annotate where-clause binder types from: set type edits, let type
  -- annotations, or constructor pattern inference via lookupConstructorType.
  renamedWheres <- forM whereClauses $ \ew -> do
    overrideTy <- view (edits.replacedTypes.at (ewName ew))
    (finalBs, finalTy) <- case overrideTy of
      Just (Just fullTy) ->
        pure (annotateAndStrip (ewBinders ew) fullTy)
      _ -> case ewRetType ew of
        Just ty -> pure (annotateAndStrip (ewBinders ew) ty)
        Nothing -> do
          annBs <- annotateFromPatterns (ewBinders ew) (map (Data.List.NonEmpty.toList . ecPats) (Data.List.NonEmpty.toList (ewClauses ew)))
          pure (annBs, Nothing)
    pure $ ew { ewBinders = finalBs, ewRetType = finalTy }
  when (null renamedEqns) $
    editFailure $ "equations edit for " ++ show name ++ " produced no equations (body may have only implicit binders or unsupported structure)"
  case annotatedBinders of
    [] -> editFailure "equations edit requires a function with at least one argument"
    (b:bs) -> do
      -- Convert termination argument to by-wf annotation.
      -- MeasureOrder uses lt (measure maps to nat; lt is the wf relation on nat).
      -- WFOrder uses the user-specified relation directly.
      mwf <- case mterm of
            Just (WellFoundedTA (MeasureOrder_ expr mrel)) -> do
              case mrel of
                Just _ -> liftIO $ hPutStrLn stderr $ "Note: equations edit for " ++ show name ++ " ignores custom relation in measure (Equations measure always uses lt)"
                Nothing -> pure ()
              pure $ Just (WfAnnotation expr (Bare "lt"))
            Just (WellFoundedTA (WFOrder_ expr rel)) ->
              pure $ Just (WfAnnotation expr rel)
            Just (StructOrderTA _) ->
              -- Note, not error: Equations handles structural recursion automatically
              Nothing <$ liftIO (hPutStrLn stderr $ "Note: equations edit for " ++ show name ++ " ignores structural termination hint (Equations infers structural recursion automatically)")
            _ -> pure Nothing
      neClauses <- case Data.List.NonEmpty.nonEmpty renamedEqns of
                     Just ne -> pure ne
                     Nothing -> editFailure "INTERNAL: equations edit produced no clauses (this is a bug in hs-to-rocq)"
      pure [EquationsSentence EquationsDef
              { eqnName    = name
              , eqnBinders = b :| bs
              , eqnRetType = retTy
              , eqnWf      = mwf
              , eqnClauses = neClauses
              , eqnWheres  = renamedWheres }]
  where
    -- Annotate ExplicitBinder names from an Arrow/Forall-chain type, returning
    -- the annotated binders and the remaining (return) type.
    annotateAndStrip :: [Binder] -> Term -> ([Binder], Maybe Term)
    annotateAndStrip [] ty = ([], Just ty)
    annotateAndStrip (ExplicitBinder (Ident n) : bs) ty
      | (argTy, restTy) <- splitArrow ty =
        let (bs', ret) = annotateAndStrip bs restTy
        in (Typed Ungeneralizable Explicit (Ident n :| []) argTy : bs', ret)
    annotateAndStrip (b:bs) ty =
      let ty' = if isImplicitBinder b then dropForall ty else dropArrow ty
          (bs', ret) = annotateAndStrip bs ty'
      in (b : bs', ret)

    splitArrow (Arrow a rest) = (a, rest)
    splitArrow (Forall _ rest) = splitArrow rest
    splitArrow t = (Underscore, t)  -- type exhausted: use _ for binder, preserve remaining
    dropArrow (Arrow _ rest) = rest
    dropArrow (Forall _ rest) = dropArrow rest
    dropArrow t = t
    -- Skip a Forall (for implicit binders that correspond to forall quantifiers, not arrows)
    dropForall (Forall _ rest) = rest
    dropForall t = t

    -- Infer binder types from constructor patterns in the equations.
    annotateFromPatterns :: ConversionMonad r m => [Binder] -> [[Pattern]] -> m [Binder]
    annotateFromPatterns [] _ = pure []
    annotateFromPatterns (ExplicitBinder (Ident n) : bs) patSets = do
      let firstPats = [ p | (p:_) <- patSets ]
          tailPats  = [ ps | (_:ps) <- patSets, not (null ps) ]
      mty <- inferTypeFromPats firstPats
      rest <- annotateFromPatterns bs tailPats
      case mty of
        Just ty -> pure $ Typed Ungeneralizable Explicit (Ident n :| []) (Qualid ty) : rest
        Nothing -> pure $ ExplicitBinder (Ident n) : rest
    annotateFromPatterns (b:bs) patSets =
      (b :) <$> annotateFromPatterns bs patSets

    inferTypeFromPats :: ConversionMonad r m => [Pattern] -> m (Maybe Qualid)
    inferTypeFromPats [] = pure Nothing
    inferTypeFromPats (QualidPat con : _) = lookupConstructorType con
    inferTypeFromPats (ArgsPat con _ : _) = lookupConstructorType con
    inferTypeFromPats (InfixPat _ op _ : _) = lookupConstructorType (Bare op)
    inferTypeFromPats (_ : rest) = inferTypeFromPats rest

    stripFun (Fun bs inner) = (Data.List.NonEmpty.toList bs, inner)
    stripFun t = ([], t)

    -- Expand each Equation's alternatives (NonEmpty MultPattern) into
    -- separate Equations clauses.  Most equations have a single alternative;
    -- multi-pattern alternatives (| pat1 | pat2 => rhs) are expanded.
    extractEqns (HsToRocq.Rocq.Gallina.Match _ _ eqns) =
      [EquationsClause pats rhs | Equation mpats rhs <- eqns
                                , MultPattern pats <- Data.List.NonEmpty.toList mpats ]
    -- Look through common wrappers to find a Match inside
    extractEqns (Parens t)       = extractEqns t
    extractEqns (HasType t _)    = extractEqns t
    extractEqns _ = []

    -- Extract a where clause from nested let bindings: look through each Let
    -- to find one whose value is a function with pattern matching.  Returns
    -- at most one where clause (the first pattern-matching let found).
    -- hs-to-rocq's convertLocalBinds (Expr.hs) uses foldrM to build nested Coq
    -- Lets from binding groups, so a simple let (e.g., y = x) may appear outermost
    -- even when a pattern-matching helper was written first in the source.
    -- Recursing into the outer body handles this (see applyAndKeep test case).
    extractWheres (Parens t)     = extractWheres t
    extractWheres (HasType t _)  = extractWheres t
    extractWheres (Let localName _localBinders localTy localVal outerBody) =
      let (localFunBinders, localInner) = stripFun localVal
          localEqns = extractEqns localInner
          (annotatedWhereBinders, whereRetTy) = case localTy of
            Just ty -> annotateAndStrip localFunBinders ty
            Nothing -> (localFunBinders, Nothing)
      in case localEqns of
           [] -> extractWheres outerBody  -- recurse: this let has no patterns, check inner lets
           (e:es) -> [EquationsWhere { ewName = localName, ewBinders = annotatedWhereBinders
                                       , ewRetType = whereRetTy, ewClauses = e :| es }]
    extractWheres _ = []

    -- Generate a single equation with variable patterns for all explicit binders.
    -- If a where clause was extracted, strip that specific let binding from the
    -- body (it may be nested behind non-pattern-matching lets).
    varPatternEqn binders inner =
      let explicitNames = [ n | b <- binders, not (isImplicitBinder b)
                              , Bare n <- toListOf binderIdents b ]
          hasWheres = not (null (extractWheres inner :: [EquationsWhere]))
          rhs | hasWheres = stripWhereLet inner
              | otherwise = inner
      in case Data.List.NonEmpty.nonEmpty explicitNames of
           Nothing -> []
           Just names -> [EquationsClause (fmap (QualidPat . Bare) names) rhs]

    -- Remove the let binding that was extracted as a where clause from the body.
    -- Walks through nested lets to find the pattern-matching one.
    stripWhereLet (Parens t)    = Parens (stripWhereLet t)
    stripWhereLet (HasType t k) = HasType (stripWhereLet t) k
    stripWhereLet (Let n bs ty val outerBody)
      | not (null (extractEqns (snd (stripFun val)))) = outerBody  -- this is the where-clause let; remove it
      | otherwise = Let n bs ty val (stripWhereLet outerBody)      -- keep this let, recurse into body
    stripWhereLet t = t

    isUnderscoredBinder (Typed _ _ _ Underscore) = True
    isUnderscoredBinder _ = False

    isImplicitBinder (ImplicitBinders _) = True
    isImplicitBinder (Generalized Implicit _) = True
    isImplicitBinder (Typed _ Implicit _ _) = True
    isImplicitBinder _ = False

convertHsGroup :: ConversionMonad r m => HsGroup GhcRn -> m ConvertedModuleDeclarations
convertHsGroup HsGroup{..} = do
  mod                 <- view (currentModule . modName)
  isModuleAxiomatized <- view currentModuleAxiomatized

  let catchIfAxiomatizing | isModuleAxiomatized = const
                          | otherwise           = gcatch
  handler             <- whenPermissive axiomatizeBinding

  promotions          <- view (edits.promotions)

  convertedTyClDeclsTmp <- convertModuleTyClDecls
                     .  map unLoc
                     $  concatMap group_tyclds hs_tyclds
                         -- Ignore roles
  (convertedValDecls, promotedDecls)  <- -- TODO RENAMER merge with convertLocalBinds / convertModuleValDecls
    case hs_valds of
#if __GLASGOW_HASKELL__ >= 806
      ValBinds{} ->
        convUnsupported' "pre-renaming `ValBinds' construct post renaming"
      XValBindsLR (NValBinds binds lsigs) -> do
#else
      ValBindsIn{} ->
        convUnsupported' "pre-renaming `ValBindsIn' construct post renaming"
      ValBindsOut binds lsigs -> do
#endif
        sigs  <- convertLSigs lsigs `catchIfAxiomatizing` const @_ @SomeException (pure M.empty)
        let convertBinding' !b = (,) (convertedBindingName b) <$> convertBinding sigs b
        defns <- (convertTypedModuleBindings (concatMap (bagToList . snd) binds) sigs
                   ??
                   handler)
                 convertBinding'
        let unnamedSentences = concat [ sentences | (Nothing, sentences) <- defns ]
        let namedSentences   = [ (name, sentences) | (Just name, sentences) <- defns ]
        let defnsMap = M.fromList namedSentences

        -- defnsMap    :: Map Qualid [Sentence]
        -- sentenceBVs :: Map Qualid (Set Qualid)
        let sentenceBVs = S.unions . fmap (getFreeVars' . bvOf @Qualid) <$> defnsMap

        -- transitiveClosure :: Ord a => Reflexivity -> Map a (Set a) -> Map a (Set a)
        let tc = transitiveClosure Reflexive sentenceBVs                -- :: Map Qualid (Set Qualid)
        let depsList = map (`M.lookup` tc) (S.toList promotions)        -- :: [Maybe (Set Qualid)]
        let depsSet = S.unions $ map (fromMaybe S.empty) depsList       -- :: Set Qualid
                
        let (promotedSentences, namedSentences') =
              partition (\(name, _) -> name `S.member` depsSet) namedSentences

        pure (unnamedSentences ++ concatMap snd namedSentences', concatMap snd promotedSentences)

  -- Derived instances have an UnhelpfulSpan, we put those to the top because
  -- they tend to be self-contained and everything else depends on them.
  let compareSpan (UnhelpfulSpan _) (UnhelpfulSpan _) = EQ
      compareSpan (UnhelpfulSpan _) RealSrcSpan{} = LT
      compareSpan RealSrcSpan{} (UnhelpfulSpan _) = GT
      compareSpan (RealSrcSpan p GHC_900(_)) (RealSrcSpan q GHC_900(_)) = compare p q

  instEnv <- view (currentModule.modDetails) >>= instancesOfModDetails
  
  convertedClsInstDecls <- convertClsInstDecls instEnv . map unLoc $ sortBy (compareSpan `on` getLoc)
    [L l cid | grp <- hs_tyclds, L l (ClsInstD NOEXTP cid) <- group_instds grp]

  (convertedAddedTyCls,convertedAddedDecls) <- view (edits.additions.at mod.non ([],[]))

  let convertedTyClDecls = convertedTyClDeclsTmp ++ promotedDecls

  pure ConvertedModuleDeclarations{..}
  where
    -- TODO: factor this out?
    axiomatizeBinding :: ConversionMonad r m => HsBind GhcRn -> GhcException -> m (Maybe Qualid, [Sentence])
    axiomatizeBinding FunBind{..} exn = do
      name <- var ExprNS (unLoc fun_id)
      pure (Just name, [translationFailedComment (qualidBase name) exn, axiom name])
    axiomatizeBinding _ exn =
      pure (Nothing, [CommentSentence $ Comment $
        "While translating non-function binding: " <> T.pack (show exn)])

#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertHsGroup (XHsGroup v) = noExtCon v
#endif

--------------------------------------------------------------------------------

data ConvertedModule =
  ConvertedModule { convModName         :: !ModuleName
                  , convModImports      :: ![Sentence]
                  , convModTyClDecls    :: ![Sentence]
                  , convModValDecls     :: ![Sentence]
                  , convModClsInstDecls :: ![Sentence]
                  , convModAddedTyCls   :: ![Sentence]
                  , convModAddedDecls   :: ![Sentence]
                  }
  deriving (Eq, Ord, Show, Data)

renameModule :: GlobalMonad r m => ModuleName -> m ModuleName
renameModule mod = view $ edits.renamedModules.at mod.non mod

-- Assumes module renaming has been accomplished
convertModule :: GlobalMonad r m => ModuleData -> HsGroup GhcRn -> m (ConvertedModule, [ModuleName])
convertModule convModData group = do
  withCurrentModule convModData $ do
    ConvertedModuleDeclarations { convertedTyClDecls    = convModTyClDecls
                                , convertedValDecls     = convModValDecls
                                , convertedClsInstDecls = convModClsInstDecls
                                , convertedAddedTyCls   = convModAddedTyCls
                                , convertedAddedDecls   = convModAddedDecls
                                }
      <- convertHsGroup group
    let convModName = convModData ^. modName
    let allSentences = convModTyClDecls ++ convModValDecls ++ convModClsInstDecls ++ convModAddedTyCls ++ convModAddedDecls
    let freeVars = toList $ foldMap getFreeVars' allSentences
    let modules = filter (/= convModName)
                     . map (mkModuleName . T.unpack)
                     . mapMaybe qualidModule $ freeVars
    let needsNotation qualid
            = qualidIsOp qualid || qualid == "GHC.Num.fromInteger"

    let notationModules
                     = filter (/= convModName)
                     . map (mkModuleName . T.unpack)
                     . mapMaybe qualidModule
                     . filter needsNotation $ freeVars

    modules         <- skipModules $ S.toList $ S.fromList modules
    notationModules <- skipModules $ S.toList $ S.fromList notationModules
    imported_modules <- view $ edits.importedModules

    let needsEquations = any isEquationsSentence allSentences
        isEquationsSentence (EquationsSentence {}) = True
        isEquationsSentence _ = False

    let convModImports =
            [ ModuleSentence (Require (Just "Equations") (Just Import) ["Equations"])
            | needsEquations
            ] ++
            [ ModuleSentence (Require Nothing imp [moduleNameText mn])
            | mn <- modules
            , let imp | mn `S.member` imported_modules = Just Import
                      | otherwise                      = Nothing
            ] ++
            [ ModuleSentence (ModuleImport Import [moduleNameText mn <> ".Notations"])
            | mn <- notationModules
            , mn `S.notMember` imported_modules
            ]

    pure (ConvertedModule{..}, modules)

-- Module-local
data ConvertModuleMode = ModeInitial
                         | ModeAxiomatize
                         | ModeConvert
                         | ModeBoth
                         deriving (Eq, Ord, Show, Read)

instance Semigroup ConvertModuleMode where
  ModeInitial    <> mode2           = mode2
  mode1           <> ModeInitial    = mode1
  ModeAxiomatize <> ModeAxiomatize = ModeAxiomatize
  ModeConvert    <> ModeConvert    = ModeConvert
  _               <> _               = ModeBoth

instance Monoid ConvertModuleMode where
  mempty = ModeInitial

  

convertModules :: GlobalMonad r m => [(ModuleData, HsGroup GhcRn)] -> m [NonEmpty ConvertedModule]
convertModules sources = do
  -- Collect modules with the same post-`rename module` name
  mergedModulesNELs <-  traverse (foldrM buildGroups (emptyRnGroup, emptyRnGroup, mempty, mempty, mempty))
                    .   M.fromListWith (<>)
                    =<< traverse (renameModule . _modName . fst <&&&> pure . pure @NonEmpty) sources

  cmods <- for (M.toList mergedModulesNELs) $ \(name, (axGrp, convGrp, mode, combinedExports, combinedDetails)) -> 
            let modData = ModuleData {_modName = name, _modExports = combinedExports, _modDetails = combinedDetails} in 
              case mode of
                ModeAxiomatize -> axiomatizeModule' modData (axGrp `appendGroups` convGrp)
                ModeConvert    -> convertModule modData convGrp
                ModeBoth       -> combineModules <$> axiomatizeModule' modData axGrp <*> convertModule modData convGrp
                ModeInitial    -> error "INTERNAL ERROR: impossible, `foldrM` over a `NonEmpty`"

  pure $ stronglyConnCompNE [(cmod, convModName cmod, imps) | (cmod, imps) <- cmods]

  where
    buildGroups (modData, modGrp) (axGrp, convGrp, mode, combinedExports, combinedDetails) =
      view (edits.axiomatizedOriginalModuleNames.contains (modData^.modName)) <&> \case
        True  -> ( modGrp{hs_tyclds = []}                     `appendGroups` axGrp
                 , emptyRnGroup{hs_tyclds = hs_tyclds modGrp} `appendGroups` convGrp
                 , ModeAxiomatize <> mode
                 , (modData^.modExports) <> combinedExports
                 , (modData^.modDetails) <> combinedDetails )
        False -> ( axGrp
                 , modGrp `appendGroups` convGrp
                 , ModeConvert <> mode
                 , (modData^.modExports) <> combinedExports
                 , (modData^.modDetails) <> combinedDetails )

    combineModules (ConvertedModule name  imports1 tyClDecls1 valDecls1 clsInstDecls1 addedTyCls1 addedDecls1, imps1)
                   (ConvertedModule _name imports2 tyClDecls2 valDecls2 clsInstDecls2 _addedTyCls2 _addedDecls2, imps2) =
      ( ConvertedModule name
                        (ordNub                     $ imports1      <> imports2)
                        (                             tyClDecls1    <> tyClDecls2)
                        (                             valDecls1     <> valDecls2)
                        (                             clsInstDecls1 <> clsInstDecls2)
                                                      addedTyCls1     -- only need one copy of the added components
                                                      addedDecls1     --
      , S.toList $ ((<>) `on` S.fromList) imps1 imps2 )
      -- It's OK not to worry about ordering the declarations
      -- because we 'topoSortByVariablesBy' them in 'moduleDeclarations'.

    axiomatizeModule' modData = local (edits.axiomatizedModules %~ S.insert (modData ^. modName)) . convertModule modData

data ModuleDeclarations = ModuleDeclarations { moduleTypeDeclarations  :: ![Sentence]
                                             , moduleValueDeclarations :: ![Sentence] }
                        deriving (Eq, Ord, Show, Read, Data)

moduleDeclarations :: GlobalMonad r m => ConvertedModule -> m ModuleDeclarations
moduleDeclarations ConvertedModule{..} = do
  let thisModule = moduleNameText convModName
      localInfixNames qid | maybe True (== thisModule) $ qualidModule qid
                          , Just op <- identToOp $ qualidBase qid
                            = S.fromList $ Bare <$> [op, infixToPrefix op]
                          | otherwise
                            = S.empty
      addLocalInfixNamesExcept del (BVs bvs fvs) =
        BVs bvs $ fvs <> (foldMap localInfixNames fvs S.\\ del)

      unused = S.singleton . Bare

      unusedNotations (NotationSentence (NotationBinding (NotationIdentBinding op _))) =
        unused op <> foldMap unused (prefixOpToInfix op)
      unusedNotations (NotationSentence (InfixDefinition op _ _ _)) =
        unused op
      unusedNotations _ =
        mempty

      bvWithInfix = addLocalInfixNamesExcept <$> unusedNotations <*> bvOf
  -- Make sure that @f = … op_zpzp__ …@ depends on @++@ and @_++_@ as well
  -- as @op_zpzp__@.  But don't produce cycles by depending on yourself.
  -- This feels like a hack, and like we could use the 'RawQualid'
  -- constructor, but we don't have the right module information in 'bvOf'
  -- to do this properly.

  orders <- view $ edits.orders
  let sortedDecls = topoSortByVariablesBy bvWithInfix orders $
        convModClsInstDecls ++ convModValDecls ++ convModAddedDecls
  let ax_decls = usedAxioms sortedDecls
  let sortedTyCls = topoSortByVariablesBy bvWithInfix orders $
        convModTyClDecls ++ convModAddedTyCls ++ ax_decls
  not_decls <- qualifiedNotations convModName (convModTyClDecls ++ sortedDecls)
  imported_modules <- view $ edits.importedModules
  pure . deQualifyLocalNames (convModName `S.insert` imported_modules)
       $ ModuleDeclarations { moduleTypeDeclarations  = sortedTyCls
                            , moduleValueDeclarations = sortedDecls ++ not_decls }

-- | This un-qualifies all variable names in the current module.
-- It should be called very late, just before pretty-printing.
deQualifyLocalNames :: Data a => S.Set ModuleName -> a -> a
deQualifyLocalNames modNames = everywhere (mkT localize)
  where
    modNameTexts = S.map moduleNameText modNames

    localize :: Qualid -> Qualid
    localize (Qualified m b) | m `S.member` modNameTexts = Bare b
    localize qid = qid

usedAxioms :: [Sentence] -> [Sentence]
usedAxioms decls = comment ++ ax_decls
  where
    ax_decls =
      [ AssumptionSentence (Assumption Axiom (Assums [i] t))
      | i <- toList (foldMap getFreeVars' decls)
      , Just t <- return $ M.lookup i builtInAxioms
      ]

    comment =
      [ CommentSentence (Comment
          "The Haskell code containes partial or untranslateable code, which needs the following")
      | not (null ax_decls)
      ]

qualifiedNotations :: GlobalMonad r m => ModuleName -> [Sentence] -> m [Sentence]
qualifiedNotations mod decls = do
    hmn <- view (edits . hasManualNotation . contains mod)
    return $ wrap $
        extra hmn ++
        [ NotationSentence qn
        | NotationSentence n <- decls, Just qn <- pure $ qualifyNotation mod n ]
  where
    wrap :: [Sentence] -> [Sentence]
    wrap []        = []
    wrap sentences = [ LocalModuleSentence (LocalModule "Notations" sentences) ]

    extra :: Bool -> [Sentence]
    extra True  = [ ModuleSentence (ModuleImport Export ["ManualNotations"]) ]
    extra False = []
