{-# LANGUAGE CPP, RecordWildCards, LambdaCase, ViewPatterns, FlexibleContexts, OverloadedStrings, OverloadedLists, ScopedTypeVariables, MultiParamTypeClasses #-}

#include "ghc-compat.h"

module HsToRocq.ConvertHaskell.Declarations.Class (ClassBody(..), convertClassDecl, getImplicitBindersForClassMember, classSentences, directClassSentences, cpsClassSentences, convertAssociatedType, convertAssociatedTypeDefault) where

import Control.Lens hiding (rewrite)

import Data.Bifunctor
import Data.Traversable
import qualified Data.List.NonEmpty as NE
import Data.Maybe

import Control.Monad

import Data.Generics

import qualified Data.Text as T

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import GHC hiding (Name)
import HsToRocq.Util.GHC
import qualified GHC

#if __GLASGOW_HASKELL__ >= 900
import GHC.Data.Bag (bagToList)
import GHC.Utils.Outputable (Outputable())
import GHC.Types.Name (occNameString, nameOccName)
#else
import Outputable (Outputable())
import Bag
import Class
#endif

import HsToRocq.Rocq.Gallina as Coq
import HsToRocq.Rocq.Gallina.Util
import HsToRocq.Rocq.Gallina.Rewrite
import HsToRocq.Rocq.Pretty
import HsToRocq.Util.FVs
#if __GLASGOW_HASKELL__ >= 806
import HsToRocq.Util.GHC.HsTypes (noExtCon)
#endif

import HsToRocq.ConvertHaskell.TypeInfo
import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.Variables
import HsToRocq.ConvertHaskell.Definitions
import HsToRocq.ConvertHaskell.HsType
import HsToRocq.ConvertHaskell.Expr
import HsToRocq.Edits.Types
import HsToRocq.ConvertHaskell.Sigs
import HsToRocq.ConvertHaskell.Declarations.Notations
import HsToRocq.ConvertHaskell.TypeEnv.TyCl

data ClassBody = ClassBody ClassDefinition [Notation]
               deriving (Eq, Ord, Read, Show)

instance HasBV Qualid ClassBody where
  bvOf (ClassBody cls nots) = bvOf cls `telescope` foldMap bvOf nots

-- lookup the signature of a class member and return the list of its
-- implicit binders
getImplicitBindersForClassMember  :: ConversionMonad r m => Qualid -> Qualid -> m [Binder]
getImplicitBindersForClassMember className memberName = do
  classDef <- lookupClassDefn className
  case classDef of
    (Just (ClassDefinition _ _ _ sigs)) ->
        case lookup memberName sigs of
          Just sigType -> return $ getImplicits sigType
          Nothing -> return []
    Nothing -> return []

-- strip off any implicit binders at the beginning of a (Coq) type
getImplicits :: Term -> [Binder]
getImplicits (Forall bs t) = if length bs == length imps then imps ++ getImplicits t else imps where
    imps = NE.takeWhile (\case
                                 ImplicitBinders _ -> True
                                 Generalized Implicit _ -> True
                                 Typed _ Implicit _ _ -> True
                                 _ -> False) bs
getImplicits _ = []

-- Module-local
convUnsupportedInLname :: (ConversionMonad r m, Outputable nm) => String -> String -> GenLocated l nm -> m a
convUnsupportedInLname what whatFam lname = do
  name <- T.unpack <$> ghcPpr (unLoc lname)
  convUnsupportedIn what whatFam name

convertAssociatedType :: ConversionMonad r m => [Qualid] -> FamilyDecl GhcRn -> m (Qualid, Term)
convertAssociatedType classArgs FamilyDecl{..} = do
  let badAssociation what whatFam = convUnsupportedInLname what whatFam fdLName
        
  case fdInfo of
    OpenTypeFamily     -> pure ()
    DataFamily         -> badAssociation "associated data types"           "data family"
    ClosedTypeFamily _ -> badAssociation "associated closed type families" "closed type family"
  -- Skipping 'fdFixity'
  unless (null fdInjectivityAnn) $ badAssociation "injective associated type families" "associated type"
  
  name   <- var TypeNS $ unLoc fdLName
  args   <- withCurrentDefinition name (convertLHsTyVarBndrs Coq.Explicit $ hsq_explicit fdTyVars)
  -- Could losen this in future?
  unless (classArgs == foldMap (toListOf binderIdents) args) $
    badAssociation "associated type families with argument lists that differ from the class's" "associated type"
  storeExplicitMethodArguments name args

  result <- case unLoc fdResultSig of
    NoSig NOEXTP                     -> pure $ Sort Type
    KindSig NOEXTP k                 -> withCurrentDefinition name $ convertLHsType k
    TyVarSig NOEXTP (L _ (UserTyVar{}))
      -> pure $ Sort Type -- Maybe not a thing inside type classes?
    TyVarSig NOEXTP (L _ (KindedTyVar NOEXTP GHC_900(_) _ k))
      -> withCurrentDefinition name $ convertLHsType k   -- Maybe not a thing inside type classes?
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
    TyVarSig _ (L _ (XTyVarBndr v)) -> noExtCon v
    XFamilyResultSig v -> noExtCon v
#endif
  
  pure (name, result)

#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertAssociatedType _ (XFamilyDecl v) = noExtCon v
#endif

#if __GLASGOW_HASKELL__ < 810
type TyFamDefltDecl pass = TyFamDefltEqn pass
type LTyFamDefltDecl pass = LTyFamDefltEqn pass
#endif

convertAssociatedTypeDefault
  :: ConversionMonad r m
  => [Qualid]
  -> TyFamDefltDecl GhcRn
  -> m (Qualid, Term)
convertAssociatedTypeDefault classArgs
#if __GLASGOW_HASKELL__ >= 900
    (TyFamInstDecl { tfid_eqn = FamEqn{..} })
      | let params = case feqn_bndrs of
              HsOuterExplicit { hso_bndrs = b } -> b
              _ -> [] = do
#elif __GLASGOW_HASKELL__ >= 810
    (TyFamInstDecl { tfid_eqn = HsIB { hsib_body = FamEqn{..} } })
      | let params = fromMaybe [] feqn_bndrs = do
#else
    FamEqn{..} | let params = hsq_explicit feqn_pats = do
#endif
  n <- var TypeNS (unLoc feqn_tycon)
  args <- withCurrentDefinition n (convertLHsTyVarBndrs Coq.Explicit params)
  unless (classArgs == foldMap (toListOf binderIdents) args) $
    convUnsupportedInLname "associated type family defaults with argument lists that differ from the class's"
                            "associated type equation"
                            feqn_tycon
  ty <- withCurrentDefinition n $ convertLHsType feqn_rhs
  pure (n, ty)
  -- Skipping feqn_fixity

#if __GLASGOW_HASKELL__ >= 900 && __GLASGOW_HASKELL__ < 910
convertAssociatedTypeDefault _ (TyFamInstDecl _ (XFamEqn v)) = noExtCon v
#elif __GLASGOW_HASKELL__ >= 810 && __GLASGOW_HASKELL__ < 900
convertAssociatedTypeDefault _ (TyFamInstDecl (HsIB { hsib_body = XFamEqn v })) = noExtCon v
convertAssociatedTypeDefault _ (TyFamInstDecl (XHsImplicitBndrs v)) = noExtCon v
#elif __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 810
convertAssociatedTypeDefault _ (XFamEqn v) = noExtCon v
#endif

convertClassDecl :: ConversionMonad r m
                 => ConvertedTyClEnv
                 -> LHsContext GhcRn                      -- ^@tcdCtxt@    Context
                 -> GenLocated l GHC.Name                      -- ^@tcdLName@   name of the class
                 -> [LHsTyVarBndr GHC_900(flag) GhcRn]                  -- ^@tcdTyVars@  class type variables
#if __GLASGOW_HASKELL__ >= 900
                 -> [GenLocated l' (FunDep GhcRn)] -- ^@tcdFDs@     functional dependencies
#else
                 -> [GenLocated l (FunDep (GenLocated l GHC.Name))] -- ^@tcdFDs@     functional dependencies
#endif
                 -> [LSig GhcRn]                          -- ^@tcdSigs@    method signatures
                 -> LHsBinds GhcRn                        -- ^@tcdMeths@   default methods
                 -> [LFamilyDecl GhcRn]                   -- ^@tcdATs@     associated types
                 -> [LTyFamDefltDecl GhcRn]               -- ^@tcdATDefs@  associated types defaults
                 -> m ClassBody
convertClassDecl env (L _ hsCtx) (L _ hsName) ltvs fds lsigs defaults types typeDefaults = do
  name <- var TypeNS hsName
  let tycl = convertedTyCl name env
  
  let convUnsupportedHere what = convUnsupportedIn what "type class" (showP name)
  -- GHC has already used functional dependencies for inference, improvement and
  -- instance consistency in the checked class environment. They add no dictionary
  -- fields: both encodings below retain every parameter, checked method type and
  -- superclass. Erasing dependencies asserts neither type equality nor uniqueness
  -- for arbitrary Gallina dictionaries. Require checked information rather than
  -- falling back to renamed syntax for a class with functional dependencies.
  unless (null fds || isJust tycl) $
    convUnsupportedHere "functional dependencies without GHC-checked class information"

  let aux x = withCurrentDefinition name $ convertLHsType x
  ctx' <- traverse (fmap (Generalized Coq.Implicit) . aux) hsCtx
  let ctx = maybe ctx' (fmap (Generalized Coq.Implicit) . convertedTyClPredTypes) tycl

  storeSuperclassCount name . sum <=< for ctx $ \case
    Generalized _ (termHead -> Just super) -> maybe 1 (+ 1) <$> lookupSuperclassCount super
    _                                      -> pure 1

  args <- fromMaybe <$> withCurrentDefinition name (convertLHsTyVarBndrs Coq.Explicit ltvs) <*> pure (convertedTyClBinderArgs <$> tycl)
  
  let argNames = foldMap (toListOf binderIdents) args

  type_sigs  <- M.fromList . map (second $ Signature ?? Nothing)
                  <$> traverse (convertAssociatedType argNames . unLoc) types
  value_sigs_from_sigs <- convertLSigs lsigs
  let value_sigs_from_typs = M.mapWithKey
        (\k t -> Signature (unpeelTyClVars t name) (sigFixity =<< M.lookup k value_sigs_from_sigs)) .
        (M.fromList . convertedTyClMethods) <$> tycl
  let value_sigs = fromMaybe value_sigs_from_sigs value_sigs_from_typs
  storeClassTypes name $ M.keysSet type_sigs
  -- We don't use 'lookupSig' here because type classes depend on the exact list
  -- of signatures.  This also means all the signatures should be present, so
  -- just using the result of `convertLSigs` shouldn't pose a problem.
  
  hideTypeArgs <- for (M.keys type_sigs) $ \meth -> do
    count <- maybe 0 length <$> lookupExplicitMethodArguments meth
    let vars = map (\i -> T.pack $ "subst" ++ show i ++ "__") [1..count]
    pure $ Rewrite { patternVars = vars
                   , lhs         = Qualid meth `appList` map (PosArg . Var) vars
                   , rhs         = Qualid meth }
  let all_sigs = everywhere (mkT $ rewrite hideTypeArgs) <$> (type_sigs <> value_sigs)

  -- implement the class part of "skip method"
  skippedMethodsS <- view (edits.skippedMethods)
  let sigs = (`M.filterWithKey` all_sigs) $ \meth _ ->
        (name,qualidBase meth) `S.notMember` skippedMethodsS

  -- ugh! doesnt work for operators
  -- memberSigs.at name ?= sigs

  type_defs  <- M.fromList <$> traverse (convertAssociatedTypeDefault argNames . unLoc) typeDefaults
  -- GHC 9.10: bagToList defaults includes default bindings for ALL class
  -- methods, including those marked `skip method`. Attempting to convert
  -- a skipped method's default body causes conversion errors (e.g., references
  -- to skipped types/functions). Filter them out before conversion.
  let isSkippedDefault lbind =
        let bindName = case unLoc lbind of
              FunBind { fun_id = L _ n } -> Just (T.pack (occNameString (nameOccName n)))
              _                          -> Nothing
        in case bindName of
             Just bname -> (name, bname) `S.member` skippedMethodsS
             Nothing    -> False
      filteredDefaults = filter (not . isSkippedDefault) (bagToList defaults)
  value_defs <- fmap (M.fromList . catMaybes) $ for filteredDefaults $
                convertTypedModuleBinding Nothing . unLoc >=> \case
                  Just (ConvertedDefinitionBinding cd) -> do
--                      typeArgs <- getImplicitBindersForClassMember name convDefName
                      -- We have a tough time handling recursion (including mutual
                      -- recursion) here because of name overloading
                      pure $ Just (cd^.convDefName, maybe id Fun (NE.nonEmpty $ cd^.convDefArgs) $ cd^.convDefBody)
                  Just (ConvertedPatternBinding    _ _)                     ->
                      convUnsupportedHere "pattern bindings in class declarations"
                  Just (ConvertedAxiomBinding      _ _)                     ->
                      convUnsupportedHere "axiom bindings in class declarations"
                  Just (RedefinedBinding           rname (RocqDefinitionDef (DefinitionDef _ _ rargs _ rbody _))) ->
                      -- `redefine` on a class default method: replaces the GHC-derived
                      -- default body with a user-provided Coq definition. The method
                      -- stays in the class Dict with its original signature. Use case:
                      -- the Haskell default uses constructs hs-to-rocq can't convert
                      -- (e.g., unsupported patterns or functions from skipped modules)
                      -- but an equivalent Coq term can be written by hand.
                      pure $ Just (rname, maybe id Fun (NE.nonEmpty rargs) rbody)
                  Just (RedefinedBinding           _ _)                     ->
                      convUnsupportedHere "redefining class method declarations (only Definition form supported)"
                  Just (SkippedBinding _) ->
                      -- `skip` on a class default method body (not `skip method`):
                      -- keeps the method in the class Dict type (instances must still
                      -- provide it) but omits the default implementation. Returns
                      -- Nothing so no default is stored. Use case: the Haskell default
                      -- body can't be converted, but every concrete instance provides
                      -- its own implementation so no default is needed.
                      pure Nothing
                  Nothing                                                   ->
                      convUnsupportedHere "skipping a type class method (use `skip method`)"
  let defs = type_defs <> value_defs
  unless (null defs) $ storeDefaultMethods name defs

  let classDefn = ClassDefinition name (args ++ ctx) Nothing (second sigType <$> M.toList sigs)

  storeClassDefn name classDefn

  let nots = concatMap (buildInfixNotations sigs) $ M.keys sigs

  pure $ ClassBody classDefn nots

directClassSentences :: ConversionMonad r m => ClassBody -> m [Sentence]
directClassSentences (ClassBody clsDef@(ClassDefinition name args _ _) nots) = do
  supers <- fromMaybe 0      <$> lookupSuperclassCount name
  types  <- fromMaybe mempty <$> lookupClassTypes      name
  let argCount = length $ filter (\b -> binderExplicitness b == Explicit) args
  pure $  ClassSentence clsDef
       :  map NotationSentence nots
       ++ map (\ty -> ArgumentsSentence . Arguments Nothing ty
                   .  map (\ie -> ArgumentSpec ie UnderscoreName Nothing)
                   $ replicate argCount ArgExplicit ++ replicate (1+supers) ArgMaximal)
              (S.toList types)

cpsClassSentences :: ConversionMonad r m => ClassBody -> m [Sentence]
cpsClassSentences (ClassBody (ClassDefinition name args ty methods) nots) = do
  -- TODO: These should probably be created with 'gensym'/'genqid', but then I
  -- have to be within a 'LocalConvMonad' and then I have to think exactly about
  -- what that means here.
  let result_ty, cont_name :: Qualid
      result_ty = "r__"
      cont_name = "g__0__" -- Can't use `g__` because it could collide with a CPSed class method
  -- result_ty <- genqid "r"
  -- cont_name <- genqid "g"
  let class_ty = Forall [ ExplicitBinder $ Ident result_ty ] $
                   (app_args_im dict_name `Arrow` Qualid result_ty) `Arrow` Qualid result_ty
  
  let wholeClassSentences =
        [ RecordSentence dict_record
        , DefinitionSentence (DefinitionDef Global name args Nothing class_ty ExistingClass)
        ]

      notations = map NotationSentence nots
  
  methods <- traverse (fmap DefinitionSentence . uncurry (method_def cont_name)) methods

  pure $ wholeClassSentences ++ methods ++ notations
  where
    dict_name = qualidExtendBase "__Dict" name
    dict_build = qualidExtendBase "__Dict_Build" name
    dict_methods = [ (qualidExtendBase "__" name, ty) | (name, ty) <- methods ]
    dict_record  = RecordDefinition dict_name dict_args ty (Just dict_build) dict_methods
    
    dict_args     = filter (\b -> binderGeneralizability b == Ungeneralizable) args
    impl_args     = filter (\b -> binderExplicitness b == Explicit) args
    app_args_ex f = foldl App1 (Qualid f) (map Qualid (foldMap (toListOf binderIdents) args))
    app_args_im f = foldl App1 (Qualid f) (map Qualid (foldMap (toListOf binderIdents) impl_args))
    
    method_def g meth ty = do
      explicitArgs <- fromMaybe [] <$> lookupExplicitMethodArguments meth
      pure $ DefinitionDef
               Global
               meth
               (explicitArgs ++ [Typed Generalizable Implicit [Ident g] $ app_args_ex name])
               (Just ty)
               (App2 (Qualid g) Underscore . app_args_im $ qualidExtendBase "__" meth)
               NotExistingClass

classSentences :: ConversionMonad r m => ClassBody -> m [Sentence]
classSentences cls@(ClassBody (ClassDefinition name _ _ _) _) =
  view (edits.simpleClasses.contains name) >>= \case
    True  -> directClassSentences cls
    False -> cpsClassSentences    cls
