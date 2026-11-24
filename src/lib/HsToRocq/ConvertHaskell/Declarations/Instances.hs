{-# LANGUAGE CPP,
             TupleSections,
             LambdaCase,
             RecordWildCards,
             OverloadedStrings,
             ScopedTypeVariables,
             FlexibleContexts #-}
#include "ghc-compat.h"

module HsToRocq.ConvertHaskell.Declarations.Instances (
  convertClsInstDecls, convertInstanceNameAndTy
) where

import Control.Lens
import Control.Monad (filterM, forM_, unless, when)

import Data.Semigroup (Semigroup(..), (<>))
import Data.Traversable
import HsToRocq.Util.Traversable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Bifunctor
import Data.Generics (everything, mkQ)
import Data.List (partition, sortBy)
import Data.Monoid
import Data.Ord (comparing)
import qualified Data.Text as T
import Control.Monad.Reader.Class

import Control.Monad.State
import Control.Monad.Writer.Strict (runWriterT, tell)

import qualified Data.Map.Strict as M

import GHC hiding (Name, Match)
#if __GLASGOW_HASKELL__ >= 900
import GHC.Data.Bag (bagToList)
import GHC.Core.TyCon (isAlgTyCon, isNewTyCon, tyConDataCons, tyConName)
import GHC.Core.DataCon (isVanillaDataCon, dataConName, dataConSourceArity, dataConTagZ)
import GHC.Types.TypeEnv (typeEnvTyCons)
import GHC.Unit.Module.ModDetails (md_types)
#else
import Bag
import TyCon (isAlgTyCon, isNewTyCon, tyConDataCons, tyConName)
import DataCon (isVanillaDataCon, dataConName, dataConSourceArity, dataConTagZ)
import HscTypes (typeEnvTyCons, md_types)
#endif
#if __GLASGOW_HASKELL__ >= 806
import HsToRocq.Util.GHC.HsTypes (noExtCon)
#endif
import HsToRocq.Util.GHC.Module
import HsToRocq.Util.Monad (ErrorString)

import HsToRocq.Rocq.Gallina

import HsToRocq.Rocq.Subst
import HsToRocq.Rocq.SubstTy
import HsToRocq.Rocq.FreeVars (getFreeVars)
import HsToRocq.Rocq.Pretty
import HsToRocq.Rocq.Gallina.Util
import HsToRocq.Rocq.Gallina.UseTypeInBinders

import HsToRocq.Edits.Types
import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.Variables
import HsToRocq.ConvertHaskell.TypeInfo
import HsToRocq.ConvertHaskell.Definitions
import HsToRocq.ConvertHaskell.HsType
import HsToRocq.ConvertHaskell.Expr
import HsToRocq.ConvertHaskell.Axiomatize
import HsToRocq.ConvertHaskell.Declarations.Class
import HsToRocq.ConvertHaskell.TypeEnv.TyCl
import HsToRocq.ConvertHaskell.TypeEnv.Instances

import qualified Data.Set as S

--------------------------------------------------------------------------------

-- | Check if a type name is a single-constructor, single-field type (newtype).
-- Returns (constructor, accessor) if so.
lookupNewtypeInfo :: ConversionMonad r m
                  => Qualid -> m (Maybe (Qualid, Qualid))
lookupNewtypeInfo typeName = do
    mcons <- lookupConstructors typeName
    case mcons of
      Just [con] -> do
        mfields <- lookupConstructorFields con
        case mfields of
          Just (RecordFields [field]) -> pure $ Just (con, field)
          Just (NonRecordFields 1)    -> pure $ Just (con, con) -- no accessor
          _                           -> pure Nothing
      _ -> pure Nothing

-- | Extract the head type constructor from a Gallina type term.
-- e.g. (Min inst_a) -> Just "Min", (list a) -> Just "list"
-- Recurses through nested App to handle partially applied constructors
-- like (Const inst_m) applied to further args: App (App (Qualid "Const") [m]) [a]
typeHead :: Term -> Maybe Qualid
typeHead (Qualid q)                      = Just q
typeHead (App f _)                       = typeHead f
typeHead (Parens t)                      = typeHead t
typeHead (InScope t _)                   = typeHead t
typeHead _                               = Nothing

-- Constructor tags are GHC's zero-based source ordinals, not positions in our
-- target metadata (which can be built in, renamed, skipped or redefined).
isConstructorTag :: Qualid -> Bool
isConstructorTag q = q `elem` [Qualified "GHC.Magic" "op_dataToTagzh__",
                              Qualified "GHC.Prim" "op_dataToTagzh__"]

hasConstructorTag :: Term -> Bool
hasConstructorTag = everything (||) (mkQ False isTagTerm)
  where
    isTagTerm (Qualid q) = isConstructorTag q
    isTagTerm (RawQualid q) = isConstructorTag q
    isTagTerm _ = False

bindTagTypes :: M.Map Qualid Term -> [Binder] -> M.Map Qualid Term
bindTagTypes = foldl extend
  where
    extend env b =
      let cleared = foldr M.delete env (toListOf binderIdents b)
      in case b of
        Typed _ _ names ty -> foldr (\n e -> case n of
          Ident q -> M.insert q ty e
          _ -> e) cleared names
        _ -> cleared

constructorTagMatch :: ConversionMonad r m => Term -> Term -> m Term
constructorTagMatch receiver ty = do
  q <- maybe (throwProgramError "dataToTag#: operand has no known type constructor")
             pure (typeHead ty)
  tcs <- views (currentModule.modDetails) (typeEnvTyCons . md_types)
  matches <- filterM (\tc -> (== q) <$> var TypeNS (tyConName tc)) tcs
  tc <- case matches of
    [tc] | isAlgTyCon tc && not (isNewTyCon tc) -> pure tc
    _ -> throwProgramError $ "dataToTag#: no unique local source ADT for " ++ showP ty
  redef <- view (edits.redefinitions.at q)
  when (isJust redef) $
    throwProgramError "dataToTag#: redefined datatype is unsupported"
  let dcs = tyConDataCons tc
  unless (all isVanillaDataCon dcs) $
    throwProgramError "dataToTag#: non-vanilla constructors are unsupported"
  source <- forM dcs $ \dc -> do
    cn <- var ExprNS (dataConName dc)
    pure (cn, dataConSourceArity dc, dataConTagZ dc)
  let names = [cn | (cn, _, _) <- source]
  actual <- lookupConstructors q
  unless (actual == Just names && S.size (S.fromList names) == length names) $
    throwProgramError "dataToTag#: target constructor list differs from source"
  forM_ source $ \(cn, arity, _) -> do
    fields <- lookupConstructorFields cn
    let count = case fields of
          Just (NonRecordFields n) -> Just n
          Just (RecordFields fs) -> Just (length fs)
          _ -> Nothing
    unless (count == Just arity) $
      throwProgramError "dataToTag#: field arity differs from source"
  pure $ Match (MatchItem receiver Nothing Nothing :| []) Nothing
    [ Equation (MultPattern (ArgsPat cn (replicate arity UnderscorePat) :| []) :| [])
        (InScope (Num (fromIntegral tag)) "Z")
    | (cn, arity, tag) <- source ]

-- This is a bounded analysis of the receiver's own type, not an inference pass
-- or a guess from the instance head. Primitive-free terms remain byte-identical.
-- Untyped shadowing loses information; unsupported binding forms fail closed.
lowerConstructorTags :: ConversionMonad r m
                     => M.Map Qualid Term -> Maybe Term -> Term -> m Term
lowerConstructorTags env expected term
  | not (hasConstructorTag term) = pure term
  | otherwise = do
      lowered <- lower env expected term
      when (hasConstructorTag lowered) $
        throwProgramError "dataToTag#: unsupported primitive in a type or binder"
      pure lowered
  where
    strip (Parens t) = strip t
    strip (InScope t _) = strip t
    strip t = t
    operandType e t = case strip t of
      Qualid q -> M.lookup q e
      HasType _ ty -> Just ty
      CheckType _ ty -> Just ty
      _ -> Nothing
    -- Removing constructor names too is conservative and cannot invent a type.
    maskPattern e p = foldr M.delete e $
      everything (++) (mkQ [] (\q -> [q :: Qualid])) p
    go = lowerConstructorTags
    lower e ty t = case t of
      App f (PosArg x :| []) | Qualid q <- strip f, isConstructorTag q -> do
        xty <- maybe (throwProgramError $ "dataToTag#: unknown operand type: " ++ showP x)
                     pure (operandType e x)
        x' <- go e Nothing x
        constructorTagMatch x' xty
      Fun bs body -> do
        (typed, resultTy) <- case ty of
          Nothing -> pure (bs, Nothing)
          Just t' | Forall{} <- strip t' ->
            throwProgramError "dataToTag#: polymorphic lambda alignment is unsupported"
          Just t' -> case useTypeInBinders (strip t') bs of
            Right (ret, bs', UTIBIsTypeTooShort False) -> pure (bs', Just ret)
            _ -> throwProgramError "dataToTag#: cannot align lambda with method type"
        Fun bs <$> go (bindTagTypes e (NE.toList typed)) resultTy body
      LetTick p val body -> LetTick p <$> go e Nothing val
        <*> go (maskPattern e p) ty body
      Let q bs oty val body -> Let q bs oty
        <$> go (bindTagTypes (M.delete q e) bs) oty val
        <*> go (M.delete q e) ty body
      Match items Nothing eqns | all simpleItem items -> do
        items' <- forM items $ \(MatchItem scr as inside) ->
          MatchItem <$> go e Nothing scr <*> pure as <*> pure inside
        eqns' <- forM eqns $ \(Equation pats body) -> do
          let e' = foldl maskPattern e
                [p | MultPattern ps <- NE.toList pats, p <- NE.toList ps]
          Equation pats <$> go e' ty body
        pure $ Match items' Nothing eqns'
      App f args -> App <$> go e Nothing f <*> traverse (\case
        PosArg x -> PosArg <$> go e Nothing x
        NamedArg n x -> NamedArg n <$> go e Nothing x) args
      If style c Nothing a b -> If style <$> go e Nothing c <*> pure Nothing
        <*> go e ty a <*> go e ty b
      Parens x -> Parens <$> go e ty x
      InScope x s -> (`InScope` s) <$> go e ty x
      HasType x xty -> (`HasType` xty) <$> go e (Just xty) x
      CheckType x xty -> (`CheckType` xty) <$> go e (Just xty) x
      _ -> throwProgramError $ "dataToTag#: unsupported context: " ++ showP t
    simpleItem (MatchItem _ Nothing Nothing) = True
    simpleItem _ = False

-- | Decompose an arrow type into arguments and result, skipping forall binders.
-- Returns ([argTypes], resultType)
decomposeArrowType :: Term -> ([Term], Term)
decomposeArrowType (Forall _ t)  = decomposeArrowType t
decomposeArrowType (Arrow a b)   = let (args, ret) = decomposeArrowType b
                                   in (a : args, ret)
decomposeArrowType (Parens t)    = decomposeArrowType t
decomposeArrowType t             = ([], t)

-- | Constant for the GHC.Prim.coerce qualid, used throughout coerce expansion.
ghcPrimCoerce :: Qualid
ghcPrimCoerce = Qualified "GHC.Prim" "coerce"

-- | Expand a coerce-based definition body using explicit newtype wrapping.
-- If the body contains GHC.Prim.coerce and we can determine the newtype
-- constructors from the declared type, replace coerce with explicit
-- pattern matching (unwrap arguments, apply function, wrap result).
expandCoerce :: ConversionMonad r m
             => Maybe Term  -- ^ The declared type (if available)
             -> Term        -- ^ The definition body
             -> m Term
expandCoerce mDeclType body = case stripFunBinders body of
    -- Strip any leading fun binders (implicit or explicit) from body
    -- and work on the inner coerce expression
    (outerBinders, innerBody) -> case innerBody of

      -- Pattern: GHC.Prim.coerce applied to an argument (with optional Parens/HasType wrappers)
      App (Qualid q) (PosArg arg :| [])
        | q == ghcPrimCoerce, Just declType <- mDeclType
        -> rewrap outerBinders <$> expandCoerceWithTypes declType (stripCoerceArg arg)

      -- Pattern: bare GHC.Prim.coerce used as a function
      Qualid q
        | q == ghcPrimCoerce, Just declType <- mDeclType
        -> rewrap outerBinders <$> expandBareCoerce declType

      -- Pattern: GHC.Prim.coerce (f : srcType) :: dstType (old GHC 8.x pattern)
      HasType app@(App (Qualid q)
                       (PosArg (Parens (Qualid _)) :| [])) _
        | q == ghcPrimCoerce
        -> pure $ rewrap outerBinders app  -- existing hack: just strip type ascription

      _ -> pure body
  where
    -- Strip Parens and HasType wrappers from a coerce argument
    stripCoerceArg :: Term -> Term
    stripCoerceArg (Parens (HasType fn _)) = fn
    stripCoerceArg (HasType fn _)          = fn
    stripCoerceArg (Parens fn)             = fn
    stripCoerceArg fn                      = fn

    -- Strip leading Fun binders to expose the inner coerce body
    stripFunBinders :: Term -> ([NonEmpty Binder], Term)
    stripFunBinders (Fun bs inner) =
      let (rest, core) = stripFunBinders inner
      in (bs : rest, core)
    stripFunBinders t = ([], t)

    -- Re-wrap an expanded body with the stripped binders
    rewrap :: [NonEmpty Binder] -> Term -> Term
    rewrap [] t     = t
    rewrap (bs:rest) t = Fun bs (rewrap rest t)

-- | Expand coerce when we have a typed inner function and a declared type.
expandCoerceWithTypes :: ConversionMonad r m
                      => Term -> Term -> m Term
expandCoerceWithTypes declType innerFn = do
    let (argTypes, retType) = decomposeArrowType declType
    -- Try to find newtype info for argument and return types
    argInfos <- mapM getNewtypeWrap argTypes
    retInfo  <- getNewtypeWrap retType
    -- If at least one argument or the return type is a newtype, expand
    if any isNewtype argInfos || isNewtype retInfo
      then buildExpandedBody argInfos retInfo innerFn
      else do
        liftIO $ putStrLn "hs-to-rocq: warning: could not expand GHC.Prim.coerce (no newtype info)"
        pure $ App (Qualid ghcPrimCoerce)
                    (PosArg (Parens innerFn) :| [])

-- | Expand bare coerce (used as identity-like function between newtype and base type).
-- For bare coerce, we generate an explicit lambda that unwraps newtype args,
-- applies any function args, and wraps the result.
expandBareCoerce :: ConversionMonad r m
                 => Term -> m Term
expandBareCoerce declType = do
    let (argTypes, retType) = decomposeArrowType declType
    argInfos <- mapM getNewtypeWrap argTypes
    retInfo  <- getNewtypeWrap retType
    if any isNewtype argInfos || isNewtype retInfo
      then do
        let varNames = [ Bare (T.pack ("arg_" ++ show i ++ "__"))
                       | i <- [0 :: Int .. length argTypes - 1] ]
            indexed = zip3 [0::Int ..] argInfos varNames
            innerExpr = buildInnerExpr indexed retInfo
            explicitArgs = [ExplicitBinder (Ident v) | v <- varNames]
        case NE.nonEmpty explicitArgs of
          Just binders -> pure $ Fun binders innerExpr
          Nothing -> do
            liftIO $ putStrLn "hs-to-rocq: warning: could not expand GHC.Prim.coerce (no newtype info)"
            pure $ Qualid ghcPrimCoerce
      else do
        liftIO $ putStrLn "hs-to-rocq: warning: could not expand GHC.Prim.coerce (no newtype info)"
        pure $ Qualid ghcPrimCoerce
  where
    -- Build the inner expression for bare coerce
    -- For single arg: wrap(unwrap(arg))
    -- For multi arg like (a->b->c) -> F a -> F b -> F c:
    --   apply first non-newtype arg to remaining unwrapped args, then wrap
    buildInnerExpr :: [(Int, NewtypeWrap, Qualid)] -> NewtypeWrap -> Term
    buildInnerExpr indexed retInfo =
      let (fnArgs, dataArgs) = partition (\(_, nw, _) -> not (isNewtype nw)) indexed
          unwrapped = [(i, unwrapArg nw (Qualid v)) | (i, nw, v) <- dataArgs]
          fnTerms = [(i, Qualid v) | (i, _, v) <- fnArgs]
          allTerms = map snd $ sortBy (comparing fst) (unwrapped ++ fnTerms)
          applied = case allTerms of
            []     -> Qualid ghcPrimCoerce
            [x]    -> x
            (f:xs) -> foldl (\acc a -> App acc (PosArg a :| [])) f xs
      in wrapResult retInfo applied

-- | Describes how a type in a coerce-expanded method signature relates to newtypes.
-- GHC 9.10 uses @coerce@ extensively in derived instance methods. Coq can't resolve
-- @Coercible@ for newtypes, so we expand coerce into explicit wrap/unwrap operations.
-- Each constructor handles a different shape of newtype occurrence in the type:
data NewtypeWrap = IsNewtype Qualid Qualid  -- ^ Direct newtype: constructor, accessor (e.g. @Last a@)
                 | ListNewtype Qualid       -- ^ Newtype inside list: accessor to map over elements (e.g. @list (Last a)@ in mconcat)
                 | FnNewtype [NewtypeWrap] NewtypeWrap  -- ^ Newtype in function result: arg wraps, result wrap (e.g. @a -> Last b@ in >>=)
                 | NotNewtype
                 deriving (Eq)

isNewtype :: NewtypeWrap -> Bool
isNewtype (IsNewtype _ _)  = True
isNewtype (ListNewtype _)  = True
isNewtype (FnNewtype _ _)  = True
isNewtype NotNewtype       = False

getNewtypeWrap :: ConversionMonad r m => Term -> m NewtypeWrap
getNewtypeWrap ty = case ty of
    -- Handle function types: a -> b where the result is a newtype
    Arrow a b -> do
      aWrap <- getNewtypeWrap a
      bWrap <- getNewtypeWrap b
      if isNewtype bWrap || isNewtype aWrap
        then pure $ FnNewtype [aWrap] bWrap
        else pure NotNewtype
    _ -> case typeHead ty of
      Just q  -> do
        minfo <- lookupNewtypeInfo q
        case minfo of
          Just (con, acc) -> pure $ IsNewtype con acc
          Nothing
            -- Check for list (Newtype) pattern: unwrap by mapping accessor
            | q == Bare "list" || q == Qualified "GHC.Base" "list"
            , App _ args <- ty
            , PosArg innerTy :| [] <- args
            -> do innerInfo <- getNewtypeWrap innerTy
                  case innerInfo of
                    IsNewtype _ acc -> pure $ ListNewtype acc
                    _               -> pure NotNewtype
            | otherwise -> pure NotNewtype
      Nothing -> pure NotNewtype

unwrapArg :: NewtypeWrap -> Term -> Term
unwrapArg (IsNewtype _con acc) var = App (Qualid acc) (PosArg var :| [])
unwrapArg (ListNewtype acc)    var = App (App (Qualid (Qualified "GHC.Base" "map"))
                                              (PosArg (Qualid acc) :| []))
                                         (PosArg var :| [])
unwrapArg (FnNewtype argWraps retWrap) var =
    -- Generate: fun v0 v1 ... => unwrapRet (var (wrapArg v0) (wrapArg v1) ...)
    let varNames = [Bare (T.pack ("v_" ++ show i ++ "__"))
                   | i <- [0 :: Int .. length argWraps - 1]]
        wrappedArgs = zipWith wrapArg argWraps (map Qualid varNames)
        appliedFn = foldl (\f a -> App f (PosArg a :| [])) var wrappedArgs
        unwrappedRet = unwrapRet retWrap appliedFn
        binders = [ExplicitBinder (Ident v) | v <- varNames]
    in case NE.nonEmpty binders of
         Just bs -> Fun bs unwrappedRet
         Nothing -> unwrappedRet
  where
    wrapArg (IsNewtype con _) v = App (Qualid con) (PosArg v :| [])
    wrapArg _                 v = v
    unwrapRet (IsNewtype _ acc) inner = App (Qualid acc) (PosArg inner :| [])
    unwrapRet (FnNewtype _ _)   inner = inner  -- nested FnNewtype: don't recurse
    unwrapRet _                 inner = inner
unwrapArg NotNewtype            var = var

wrapResult :: NewtypeWrap -> Term -> Term
wrapResult (IsNewtype con _acc) inner = App (Qualid con) (PosArg inner :| [])
wrapResult (ListNewtype _)      inner = inner  -- list result stays as-is
wrapResult (FnNewtype _ _)      inner = inner  -- fn result stays as-is
wrapResult NotNewtype            inner = inner

-- | Build the expanded function body with explicit wrapping/unwrapping.
buildExpandedBody :: ConversionMonad r m
                  => [NewtypeWrap] -> NewtypeWrap -> Term -> m Term
buildExpandedBody argInfos retInfo innerFn = do
    let varNames = [ Bare (T.pack ("arg_" ++ show i ++ "__"))
                   | i <- [0 :: Int .. length argInfos - 1] ]
        unwrappedArgs = zipWith unwrapArg argInfos (map Qualid varNames)
        innerApp = foldl (\f a -> App f (PosArg a :| [])) innerFn unwrappedArgs
        wrappedResult = wrapResult retInfo innerApp
        binders = [ExplicitBinder (Ident v) | v <- varNames]
    case NE.nonEmpty binders of
      Just bs -> pure $ Fun bs wrappedResult
      Nothing -> pure wrappedResult

--------------------------------------------------------------------------------

-- Take the instance head and make it into a valid identifier.
convertInstanceNameAndTy :: ConversionMonad r m => LHsType GhcRn -> m (Qualid, Qualid)
convertInstanceNameAndTy n = do
    coqType <- withCurrentDefinition (Bare "") $ convertLHsType n -- revisit if needed
    qual <- views (currentModule.modName) $ Qualified . moduleNameText
    case skip coqType of
        Left err -> throwProgramError $ "Cannot derive instance name from `" ++ showP coqType ++ "': " ++ err
        Right (name, ty) -> return (qual name, ty)
  where
    -- Skip type variables and constraints
    skip (Forall _ t)  = skip t
    skip (Arrow _ t)   = skip t
    skip (InScope t _) = skip t
    skip t             = do
      t' <- bfTerm t
      -- The pattern match below will not be correct with multi-param type classes
      case t' of
        (_:x:_) -> pure (bfToName t', x)
        _       -> error "bfTerm returned fewer than 2 elements"

    bfToName :: [Qualid] -> T.Text
    bfToName qids | isVanilla = name
                  | otherwise = name <> "__" <> T.pack (show shapeNum)
      where
        tyCons = mapMaybe unTyCon qids
        name = T.intercalate "__" tyCons
        shapeNum = bitsToInt $ map isTyCon qids

        -- A vanilla header is when all tyCons appear before all
        -- type variables. In this case, do not add the shapeNum
        isVanilla = not $ any isTyCon $ dropWhile isTyCon qids

        isTyCon = isJust . unTyCon

        unTyCon :: Qualid -> Maybe T.Text
        unTyCon (Qualified _ base)  = Just base
        unTyCon (Bare "bool")       = Just "bool"
        unTyCon (Bare "comparison") = Just "comparison"
        unTyCon (Bare "list")       = Just "list"
        unTyCon (Bare "option")     = Just "option"
        unTyCon (Bare "op_zt__")    = Just "op_zt__"
        unTyCon (Bare "unit")       = Just "unit"
        unTyCon (Bare "nat")        = Just "nat"
        unTyCon _                   = Nothing

        bitsToInt :: [Bool] -> Integer
        bitsToInt []         = 0
        bitsToInt (True:xs)  = 2*bitsToInt xs + 1
        bitsToInt (False:xs) = 2*bitsToInt xs

    -- Breadth-first traversal listing all variables and type constructors
    bfTerm :: Term -> Either ErrorString [Qualid]
    bfTerm = fmap concat . go
      where
        go :: Term -> Either ErrorString [[Qualid]]
        go t = do
            (f, args) <- collectArgs t
            subtrees <- mapM go args
            return $ [f] : foldr merge [] subtrees

    merge :: [[a]] -> [[a]] -> [[a]]
    merge xs     []     = xs
    merge []     ys     = ys
    merge (x:xs) (y:ys) = (x ++ y) : merge xs ys

--------------------------------------------------------------------------------
{- Haskell:
      instance Functor ((->) r)
   InstanceInfo
      Name = "Functor__arr_r___"
      Head = "Functor (_(->)_ r)" as a Coq term, with free variable
      Class = "Functor"

   Haskell:
      instance Eq a => Eq [a]
   InstanceInfo
      Name = "Eq_list____"
      Head = "forall `{Eq a}, Eq (list a)"
      Class = "Eq"

-}
data InstanceInfo = InstanceInfo { instanceName       :: !Qualid
                                 , instanceHead       :: !Term
                                 , instanceClass      :: !Qualid
                                 , instanceTy         :: !Qualid
                                 }
                  deriving (Eq, Ord, Show, Read)

-- TODO use LocalConvMonad instead?
convertClsInstDeclInfo :: ConversionMonad r m => ClsInstDecl GhcRn -> m InstanceInfo
convertClsInstDeclInfo ClsInstDecl{..} = do
  -- GHC 9.10: cid_poly_ty is LHsSigType (located HsSigType) instead of
  -- HsImplicitBndrs; extract the body type via sig_body instead of hsib_body
#if __GLASGOW_HASKELL__ >= 900
  let unwrapSigType = sig_body . unLoc
#else
  let unwrapSigType = hsib_body
#endif
  (instanceName, instanceTy)  <- convertInstanceNameAndTy $ unwrapSigType cid_poly_ty
  utvm                        <- unusedTyVarModeFor instanceName
  instanceHead                <- withCurrentDefinition instanceName $ convertLHsSigType utvm cid_poly_ty
  instanceClass               <- termHead instanceHead
                                 & maybe (convUnsupportedIn "strangely-formed instance heads"
                                           "type class instance"
                                           (showP instanceName))
                                 pure

  pure InstanceInfo{..}
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertClsInstDeclInfo (XClsInstDecl v) = noExtCon v
#endif

--------------------------------------------------------------------------------

noClassError :: MonadIO m => Qualid -> String -> m a
noClassError cls extra = throwProgramError $  "Could not find information for the class " ++ quoteQualid cls
                                             ++ if null extra then [] else ' ':extra

noClassInstanceError :: MonadIO m => Qualid -> Qualid -> m a
noClassInstanceError cls inst = noClassError cls $ "when defining the instance " ++ quoteQualid inst

noClassMethodError :: MonadIO m => Qualid -> Qualid -> m a
noClassMethodError cls meth = noClassError cls $ "when defining the method " ++ quoteQualid meth


quoteQualid :: Qualid -> String
quoteQualid qid = "`" ++ showP qid ++ "'"

--------------------------------------------------------------------------------

unlessSkippedClass :: ConversionMonad r m => InstanceInfo -> m [Sentence] -> m [Sentence]
unlessSkippedClass InstanceInfo{..} act = do
  view (edits.skippedClasses.contains instanceClass) >>= \case
    True ->
      pure [CommentSentence . Comment $
              "Skipping all instances of class `" <> textP instanceClass
                <> "', including `" <> textP instanceName <> "'"]
    False ->
      act

bindsToMap :: ConversionMonad r m => [HsBindLR GhcRn GhcRn] -> m (M.Map Qualid (HsBind GhcRn))
bindsToMap binds = fmap M.fromList $ forM binds $ \hs_bind -> do
    name <- hsBindName hs_bind
    return (name, hs_bind)

clsInstFamiliesToMap :: ConversionMonad r m => [LTyFamInstDecl GhcRn] -> m (M.Map Qualid (HsType GhcRn))
clsInstFamiliesToMap assocTys =
  -- GHC 9.10: TyFamInstDecl has a direct FamEqn field instead of wrapping in HsIB
  fmap M.fromList . for assocTys $
#if __GLASGOW_HASKELL__ >= 900
    \(L _ (TyFamInstDecl _ FamEqn{..})) ->
#else
    \(L _ (TyFamInstDecl HsIB {hsib_body = FamEqn{..}})) ->
#endif
    (, unLoc feqn_rhs) <$> var TypeNS (unLoc feqn_tycon)

-- Module-local
data ConvMethod = CMRenamed            Sentence
                 | CMDefined ConvLevel Term
                 deriving (Eq, Ord, Show, Read)

-- Module-local
data ConvLevel = CLTerm | CLType deriving (Eq, Ord, Enum, Bounded, Show, Read)

-- Return exactly the original method bodies that conversion used. Keeping this
-- record inside conversion avoids predicting class interfaces or scoped edits
-- during deriving recovery; failed or replaced instances contribute no bodies.
convertClsInstDecl :: forall r m. ConversionMonad r m => ConvertedInstanceEnv -> ClsInstDecl GhcRn -> m ([Sentence], [HsBind GhcRn])
convertClsInstDecl env cid@ClsInstDecl{..} = runWriterT $ do
  ii@InstanceInfo{..} <- convertClsInstDeclInfo cid
  let convUnsupportedHere what = convUnsupportedIn what "type class instance" (showP instanceName)

  let err_handler exn = pure [ translationFailedComment ("instance " <> qualidBase instanceName) exn ]
  unlessSkippedClass ii . handleIfPermissive err_handler $ definitionTask instanceName >>= \case
    SkipIt ->
      pure [CommentSentence . Comment $
              "Skipping instance `" <> textP instanceName <> "' of class `" <> textP instanceClass <> "'"]

    RedefineIt def ->
      [definitionSentence def] <$ case def of
        RocqInductiveDef        _   -> editFailure   "cannot redefine an instance definition into an Inductive"
        RocqDefinitionDef       _   -> editFailure   "cannot redefine an instance definition into a Definition"
        RocqFixpointDef         _   -> editFailure   "cannot redefine an instance definition into a Fixpoint"
        RocqInstanceDef         _   -> pure ()
        RocqAxiomDef            _   -> editFailure   "cannot redefine an instance definition into an Axiom"
        RocqAssertionDef        apf -> editFailure $ "cannot redefine an instance definition into " ++ anAssertionVariety apf

    AxiomatizeIt axMode ->
      lookupClassDefn instanceClass >>= \case
        Just (ClassDefinition _ _ _ methods)
          | null methods ->
            pure [ InstanceSentence $ InstanceDefinition instanceName [] instanceHead [] Nothing]
          | otherwise ->
            pure [ InstanceSentence $ InstanceProof instanceName [] instanceHead $ ProofAdmitted ""]
        Nothing -> case axMode of
          GeneralAxiomatize  -> pure []
          SpecificAxiomatize -> noClassInstanceError instanceClass instanceName

    TranslateIt -> do
      cid_binds_map <- bindsToMap (map unLoc $ bagToList cid_binds)
      cid_types_map <- clsInstFamiliesToMap cid_tyfam_insts

      let (binds', classTy) = decomposeForall instanceHead

      -- decomposeClassTy can fail, so run it in the monad so that
      -- failure will be caught and cause the instance to be skipped
      (className, instTys) <- either convUnsupportedHere pure $ decomposeClassTy classTy
      
      _inst@ConvertedInstance{..} <- lookupInstance instTys className env
      let binds = convertedInstanceBinds ++ filter (\b -> binderGeneralizability b == Generalizable) binds'

      -- Get the methods of this class (this should already exclude skipped ones)
      (classMethods, classArgs) <- lookupClassDefn className >>= \case
        Just (ClassDefinition _ args _ sigs) -> pure (map fst sigs, args)
        _ -> noClassInstanceError className instanceName

      -- Associated types for this class
      classTypes <- fromMaybe mempty <$> lookupClassTypes className

      classDefaults <- fromMaybe M.empty <$> lookupDefaultMethods className

      let localNameFor :: Qualid -> Qualid
          localNameFor meth = qualidMapBase (<> ("_" <> qualidBase meth)) instanceName

      -- Build inverse of renamedModules (old->new) to get (new->[old]).
      -- This lets envFor also register pre-module-rename keys, so that
      -- GHC.Internal.* references match before renameModule runs.
      inverseModRenames <- do
          rmMap <- view (edits.renamedModules)
          pure $ M.fromListWith (++)
            [ (moduleNameText newM, [moduleNameText oldM])
            | (oldM, newM) <- M.toList rmMap, oldM /= newM ]

      let preRenameVariants :: Qualid -> [Qualid]
          preRenameVariants (Qualified modName ident) =
            case M.lookup modName inverseModRenames of
              Just oldMods -> [Qualified om ident | om <- oldMods]
              Nothing      -> []
          preRenameVariants _ = []

      -- In the translation of meth1, we want all _other_ methods to be renamed
      -- to the concrete methods of the current instance (because type class methods
      -- usually refer to each other).
      -- We don’t do this for the current method (because type class methods are usually
      -- not recursive.)
      -- This is a heuristic, and the user can override it using `rewrite` rules.
      -- Note: we register both post-rename and pre-rename module names so that
      -- GHC.Internal.* references are caught before renameModule runs.
      let envFor :: Qualid -> r -> r
          envFor meth = appEndo $ foldMap Endo $
            [ edits.renamings.at (NamespacedIdent ns m) ?~ localNameFor m
            | m <- classMethods
            , m /= meth
            , let ns = if m `elem` classTypes then TypeNS else ExprNS
            ] ++
            [ edits.renamings.at (NamespacedIdent ns preM) ?~ localNameFor m
            | m <- classMethods
            , m /= meth
            , let ns = if m `elem` classTypes then TypeNS else ExprNS
            , preM <- preRenameVariants m
            ]

      let allLocalNames = M.fromList $  [ (m, Qualid (localNameFor m)) | m <- classMethods ]

      let quantify sub meth body = (maybeFun ?? body) . subst sub <$> getImplicitBindersForClassMember className meth
          -- Like quantify, but makes binders explicit (not implicit).
          -- Used inside record literals where {a : Type} is meaningless and triggers warnings.
          quantifyExplicit sub meth body = (maybeFun ?? body) . map toExplicitBinder . subst sub <$> getImplicitBindersForClassMember className meth

      -- For each method, look for
      --  * explicit definitions
      --  * default definitions
      -- in that order
      methodSentences <- forM classMethods $ \meth -> do
        let localMeth = localNameFor meth

        methBody <- case (M.lookup meth cid_binds_map, M.lookup meth cid_types_map, M.lookup meth classDefaults) of
          (Just bind, _, _) ->
            local (envFor meth) $ convertMethodBinding localMeth bind >>= \case
              ConvertedDefinitionBinding cd -> do
                tell [bind]
                pure . CMDefined CLTerm $ maybeFun (cd^.convDefArgs) (cd^.convDefBody)
              -- Hard errors (not convUnsupported): these indicate edit misconfiguration,
              -- not missing hs-to-rocq features, so we fail immediately.
              ConvertedPatternBinding {} ->
                throwProgramError "pattern bindings in instances"
              ConvertedAxiomBinding {} ->
                throwProgramError "axiom bindings in instances"
              RedefinedBinding _ def ->
                CMRenamed (definitionSentence def) <$ case def of
                  RocqInductiveDef        _   -> editFailure   "cannot redefine an instance method definition into an Inductive"
                  RocqDefinitionDef       _   -> pure ()
                  RocqFixpointDef         _   -> pure ()
                  RocqInstanceDef         _   -> editFailure   "cannot redefine an instance method definition into an Instance"
                  RocqAxiomDef            _   -> pure ()
                  RocqAssertionDef        apf -> editFailure $ "cannot redefine an instance method definition into " ++ anAssertionVariety apf
              -- Hard error: skip on instance methods is an edit misconfiguration
              SkippedBinding _ -> throwProgramError "skipping binding in instance"

          (Nothing, Just assoc, _) ->
            let convertedType = withCurrentDefinition meth $ convertHsType assoc in

            CMDefined CLType <$> local (envFor meth) convertedType
            -- TODO: Permit rewriting or renaming or similar here

          (Nothing, Nothing, Just term) ->
            let extraSubst
                  | meth `elem` classTypes =
                    let names = foldMap (^..binderIdents) . filter (\b -> binderExplicitness b == Explicit)
                    in M.fromList $ zip (names classArgs) instTys
                  | otherwise =
                    mempty
            in -- In the body of the default definition, make methods names
               -- refer to their local version
               -- TODO: Associated type defaults should remember that they're types
               pure . CMDefined CLTerm $ subst (allLocalNames <> extraSubst) term

          (Nothing, Nothing, Nothing) ->
            throwProgramError $ "The method `" <> showP meth <> "' has no definition and no default definition"

        case methBody of
          CMRenamed renamed ->
            pure renamed
          CMDefined level body    -> do

            let (params, sub') = (case level of
                                    CLTerm -> makeInstanceMethodSubst
                                    CLType -> makeAssociatedTypeSubst) binds

            -- Why the nested substitution?  The only place the per-instance variable name
            -- can show up is in the specific instance type!  It can't show up in the
            -- signature of the method, that's the whole point
            let sub = (fmap $ subst sub') convertedInstanceSubst
            
            -- We've converted the method, now sentenceify it
            ty    <- makeTy sub className meth
            -- Expand GHC.Prim.coerce into explicit newtype wrapping/unwrapping
            -- to avoid Coq Coercible/Unpeel resolution loops
            expandedBody <- case level of
              CLTerm -> expandCoerce (Just ty) body
              _       -> pure body
            let args = subst allLocalNames <$> params
                methodTy = subst allLocalNames ty
                peel (Forall bs t) = first (NE.toList bs ++) (peel t)
                peel t = ([], t)
                (methodArgs, resultTy) = peel methodTy
                sentence cd = DefinitionSentence $ DefinitionDef Local
                  (cd^.convDefName) (cd^.convDefArgs) (cd^.convDefType)
                  (cd^.convDefBody) NotExistingClass
            tagBody <- withCurrentDefinition localMeth $
              lowerConstructorTags (bindTagTypes M.empty (args ++ methodArgs))
                (Just resultTy) (substTy sub' expandedBody)
            qbody <- quantify sub meth tagBody
            if level == CLTerm && localMeth `S.member` getFreeVars qbody
              then withCurrentDefinition localMeth $ do
                -- Recursion needs the instantiated method signature. Put its
                -- quantified parameters alongside the instance parameters, as
                -- for ordinary bindings, so polyrec controls which enter fix.
                let cd = ConvertedDefinition localMeth (args ++ methodArgs)
                           (Just resultTy) tagBody
                -- Process only this method's self-recursion. Cross-method calls
                -- retain their existing ordering and dictionary behavior.
                fixed <- addRecursion [Right (ConvertedDefinitionBinding cd)]
                case fixed of
                  [Right (ConvertedDefinitionBinding cd')] -> do
                    termination <- view (edits.termination.at localMeth)
                    case termination of
                      Just (WellFoundedTA order) -> do
                        obl <- view (edits.obligations.at localMeth)
                        toProgramFixpointSentence cd' (fromWFOrder order) obl
                      _ -> pure $ sentence cd'
                  _ -> throwProgramError "internal error: lost recursive instance method"
              else pure $ sentence (ConvertedDefinition localMeth args (Just methodTy) qbody)

      let instHeadTy = appList (Qualid className)
            (PosArg <$> filterVisibleVars convertedInstanceClass convertedInstanceTypes)
      -- Use quantifyExplicit (not quantify) for the instance record/definition
      -- body: Coq 8.20 warns about implicit binders {a : Type} inside record
      -- literals, where they have no meaning.  toExplicitBinder converts them.
      instance_sentence <- view (edits.simpleClasses.contains className) >>= \case
        True  -> do
          methods <- traverse (\m -> (m,) <$> quantifyExplicit M.empty m (Qualid $ localNameFor m)) classMethods
          pure $ ProgramSentence
                   (InstanceSentence $ InstanceDefinition instanceName binds instHeadTy methods Nothing)
                   Nothing
        False -> do
          -- Assemble the actual record
          instRHS <- fmap Record $ forM classMethods $ \m -> do
                       method_body <- subst convertedInstanceSubst $ quantifyExplicit M.empty m $ Qualid (localNameFor m)
                       return (qualidMapBase (<> "__") m, method_body)
          -- TODO: This should probably be created with 'gensym'/'genqid', but then I
          -- have to be within a 'LocalConvMonad' and then I have to think exactly about
          -- what that means here.
          let cont_name :: Qualid
              cont_name = "k__"
          -- cont_name <- genqid "k"
          let instBody = Fun (ExplicitBinder UnderscoreName NE.:| [ExplicitBinder (Ident cont_name)])
                             (App1 (Qualid cont_name) instRHS)
          let instTerm = InstanceTerm instanceName binds instHeadTy instBody Nothing

          pure $ ProgramSentence (InstanceSentence instTerm) Nothing

      pure $ methodSentences ++ [instance_sentence]
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertClsInstDecl _env (XClsInstDecl v) = noExtCon v
#endif

--------------------------------------------------------------------------------

convertClsInstDecls :: ConversionMonad r m => ConvertedInstanceEnv -> [ClsInstDecl GhcRn] -> m ([Sentence], [HsBind GhcRn])
convertClsInstDecls env = foldTraverse (convertClsInstDecl env)

-- Look up the type class variable and the type of the class member without
-- postprocessing.
lookupInstanceMethodTy :: ConversionMonad r m => Qualid -> Qualid -> m Term
lookupInstanceMethodTy className memberName =
  lookupClassDefn className >>= \case
    Just (ClassDefinition _ _ _ sigs) ->
      case lookup memberName sigs of
        Just sigType -> pure sigType
        Nothing      -> throwProgramError $ "Cannot find signature for " ++ quoteQualid memberName
    _ -> noClassMethodError className memberName

makeTy :: ConversionMonad r m => M.Map Qualid Term -> Qualid -> Qualid -> m Term
makeTy instSub className memberName = subst instSub <$> lookupInstanceMethodTy className memberName

makeAssociatedTypeSubst :: [Binder] -> ([Binder], M.Map Qualid Term)
makeAssociatedTypeSubst params = (params, M.empty)

-- lookup the type of the class member
-- add extra quantifiers from the class & instance definitions
makeInstanceMethodSubst :: [Binder] -> ([Binder], M.Map Qualid Term)
makeInstanceMethodSubst params = 
  -- GOAL: Consider
  -- @
  --     class Functor f where
  --       fmap :: (a -> b) -> f a -> f b
  --     instance Functor (Either a) where fmap = ...
  -- @
  -- When desugared naïvely into Coq, this will result in a term with type
  -- @
  --     forall {a₁}, forall {a₂ b},
  --       (a₂ -> b) -> Either a₁ a₂ -> Either a₁ b
  -- @
  -- Except without the subscripts!  So we have to rename either
  -- the per-instance variables (here, @a₁@) or the type class
  -- method variables (here, @a₂@ and @b@).  We pick the
  -- per-instance variables, and rename @a₁@ to @inst_a₁@.
  --
  -- ASSUMPTION: type variables don't show up in terms.  Broken
  -- by ScopedTypeVariables.
  let renameInst UnderscoreName =
        pure UnderscoreName
      renameInst (Ident x) =
        let inst_x = qualidMapBase ("inst_" <>) x
        in Ident inst_x <$ modify' (M.insert x (Qualid inst_x))

      sub ty = gets (($ ty) . subst)

      (instBnds, instSubst) = (runState ?? M.empty) $ for params $ \case
        ExplicitBinder  x      -> ExplicitBinder  <$> renameInst x
        ImplicitBinders xs     -> ImplicitBinders <$> traverse renameInst xs
        Typed       g ei xs ty -> Typed       g ei <$> traverse renameInst xs <*> sub ty
        Generalized ei tm      -> Generalized   ei <$> sub tm in
  (instBnds, instSubst)

-- Recover all visible arguments of "instance C t1 ... tn where".
decomposeClassTy :: Term -> Either String (Qualid, [Term])
decomposeClassTy ty = case normalizeType ty of
  Qualid cn -> Right (cn, [])
  App (Qualid cn) args -> (cn,) <$> traverse positionalArg (NE.toList args)
  _ -> unsupported
  where
    positionalArg (PosArg t) = Right (normalizeType t)
    positionalArg _ = unsupported
    unsupported = Left $ "type class instance head `" ++ showP ty ++ "'"

decomposeForall :: Term -> ([Binder], Term)
decomposeForall (Forall bnds ty) = first (NE.toList bnds ++) (decomposeForall ty)
decomposeForall t                = ([], t)
