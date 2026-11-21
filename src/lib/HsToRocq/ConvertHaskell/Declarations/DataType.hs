{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase,
             OverloadedStrings,
             FlexibleContexts #-}
-- GHC 9.10 TTG extension-point constructors (XTyVarBndr, XHsOuterTyVarBndrs)
-- are DataConCantHappen (uninhabited), so cases on them are "overlapping" yet
-- required by -Wincomplete-patterns.  Suppress the former to keep the latter.
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

#include "ghc-compat.h"

module HsToRocq.ConvertHaskell.Declarations.DataType (
  convertDataDecl,
  ) where

import Control.Lens

import HsToRocq.Util.Function
import Control.Applicative
import Data.Bifunctor
import Data.Semigroup (Semigroup(..))
import Data.Foldable
import Data.Traversable
import Data.Maybe
import HsToRocq.Util.Monad (failEither)
import HsToRocq.Util.Traversable

import qualified Data.Set        as S
import qualified Data.Map.Strict as M
import HsToRocq.Util.Containers

import Control.Monad
import Control.Monad.Trans.Maybe

import GHC hiding (Name)
import qualified GHC

import HsToRocq.Util.GHC.HsTypes (selectorFieldOcc_, noExtCon)
#if __GLASGOW_HASKELL__ >= 910
import Language.Haskell.Syntax.Extension (dataConCantHappen)
#endif

import HsToRocq.Rocq.Gallina as Coq
import HsToRocq.Rocq.Gallina.Util

import HsToRocq.Edits.Types
import HsToRocq.ConvertHaskell.TypeInfo
import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.Variables
import HsToRocq.ConvertHaskell.HsType

import qualified Data.List.NonEmpty as NE

--------------------------------------------------------------------------------

type Constructor = (Qualid, [Binder], Maybe Term)

--------------------------------------------------------------------------------

addAdditionalConstructorScope :: ConversionMonad r m => Constructor -> m Constructor
addAdditionalConstructorScope ctor@(_, _, Nothing) =
  pure ctor
addAdditionalConstructorScope ctor@(name, bs, Just resTy) =
  view (edits.additionalScopes.at (SPConstructor,name)) <&> \case
    Just scope -> (name, bs, Just $ resTy `InScope` scope)
    Nothing    -> ctor

--------------------------------------------------------------------------------

conNameOrSkip :: (ConversionMonad r m, Alternative m) => GHC.Name -> m Qualid
conNameOrSkip name = do
  con <- var ExprNS name
  guard =<< view (edits.skippedConstructors.notContains con)
  pure con

------------------------------------------------------------------------------------------

convertConDecl :: ConversionMonad r m
               => Term -> [Binder]
               -> ConDecl GhcRn
               -> m [Constructor]
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertConDecl _ _ (XConDecl v) = noExtCon v
#endif
#if __GLASGOW_HASKELL__ >= 806
convertConDecl curType extraArgs (ConDeclH98
    { con_name = lname, con_ex_tvs = lqvs, con_mb_cxt = mlcxt, con_args = details }) =
#else
convertConDecl curType extraArgs (ConDeclH98 lname mlqvs mlcxt details _doc)
 | let lqvs = maybe [] hsq_explicit mlqvs =
#endif
 fmap fold . runMaybeT $ do
  unless (maybe True (null . unLoc) mlcxt) $ convUnsupported' "constructor contexts"

  con <- conNameOrSkip $ unLoc lname

  -- Only the explicit tyvars are available before renaming, so they're all we
  -- need to consider
  params <- withCurrentDefinition con $ convertLHsTyVarBndrs Coq.Implicit lqvs
  -- GHC 9.0+ wraps constructor arg types in HsScaled for linear types;
  -- extract the type via hsScaledThing, discarding the multiplicity annotation.
#if __GLASGOW_HASKELL__ >= 900
  let hsConDeclArgTys (PrefixCon _ tys)  = hsScaledThing <$> tys
      hsConDeclArgTys (InfixCon ty1 ty2) = hsScaledThing <$> [ty1,ty2]
      hsConDeclArgTys (RecCon flds)      = map (cd_fld_type . unLoc) (unLoc flds)
#endif
  args   <- withCurrentDefinition con (traverse convertLHsType $ hsConDeclArgTys details)

  case details of
    RecCon (L _ fields) ->
      do
       let qualids =  traverse
                      (var ExprNS . selectorFieldOcc_ . unLoc)
                      (concatMap (cd_fld_names . unLoc) fields)
       fieldInfo <- fmap RecordFields qualids
       storeConstructorFields con fieldInfo
       qualids <- qualids
       let namedBinders = (\(x,y) -> mkBinders Explicit ( Ident x  NE.:| [] ) y) <$> zip qualids args
       pure [(con, params ++ namedBinders , Just . maybeForall extraArgs $ curType)]
    _ ->
     do
      fieldInfo <- pure . NonRecordFields $ length args
      storeConstructorFields con fieldInfo
      pure [(con, params , Just . maybeForall extraArgs $ foldr Arrow curType args)]

#if __GLASGOW_HASKELL__ >= 806
#if __GLASGOW_HASKELL__ >= 900
#define con_qvars con_bndrs
#define con_args con_g_args
#endif
convertConDecl curType extraArgs (ConDeclGADT
    { con_names = lnames, con_qvars = qvars, con_mb_cxt = mcxt
    , con_args = args, con_res_ty = res_ty }) = do
#else
convertConDecl curType extraArgs (ConDeclGADT lnames sigTy _doc) = do
#endif
#if __GLASGOW_HASKELL__ >= 910
  fmap catMaybes . for (toList lnames) $ \(L _ hsName) -> runMaybeT $ do
#else
  fmap catMaybes . for lnames $ \(L _ hsName) -> runMaybeT $ do
#endif
    conName         <- conNameOrSkip hsName
    utvm            <- unusedTyVarModeFor conName
    (_, curTypArgs) <- failEither (collectArgs curType)
    conTy           <- withCurrentDefinition conName $
      -- GHC 9.0+ changed GADT quantified type variables from HsQTvs to
      -- HsOuterImplicit/HsOuterExplicit.  Convert back to HsQTvs and replace
      -- the specificity flag with HsBndrRequired (9.10) or () (9.0-9.8) so
      -- convertHsSigType_ can process them uniformly.
#if __GLASGOW_HASKELL__ >= 910
      let fqvars (L _ (HsOuterImplicit qvs))  = HsQTvs qvs []
          fqvars (L _ (HsOuterExplicit _ qvs)) = HsQTvs [] ((fmap . fmap) unanno qvs)
          fqvars (L _ (XHsOuterTyVarBndrs v))  = dataConCantHappen v
          unanno (UserTyVar x _ i)      = UserTyVar x (HsBndrRequired noExtField) i
          unanno (KindedTyVar x _ i j)  = KindedTyVar x (HsBndrRequired noExtField) i j
          unanno (XTyVarBndr v)         = dataConCantHappen v in
#elif __GLASGOW_HASKELL__ >= 900
      let fqvars (L _ (HsOuterImplicit qvs)) = HsQTvs qvs []
          fqvars (L _ (HsOuterExplicit _ qvs)) = HsQTvs [] ((fmap . fmap) unanno qvs)
          unanno (UserTyVar x _ i) = UserTyVar x () i
          unanno (KindedTyVar x _ i j) = KindedTyVar x () i j in
#else
      let fqvars = id in
#endif
#if __GLASGOW_HASKELL__ >= 806
      let mktm = convertHsSigType_ utvm (fqvars qvars) mcxt args res_ty in
#else
      let mktm = convertLHsSigTypeWithExcls utvm sigTy in
#endif
      maybeForall extraArgs <$> mktm (mapMaybe termHead curTypArgs)
    storeConstructorFields conName $ NonRecordFields 0   -- This is a hack
    pure (conName, [], Just conTy)

--------------------------------------------------------------------------------

rewriteDataTypeArguments :: ConversionMonad r m => DataTypeArguments -> [Binder] -> m ([Binder], [Binder])
rewriteDataTypeArguments dta bs = do
  let dtaEditFailure what =
        editFailure $ what ++ " when adjusting data type parameters and indices"

  let (ibs, ebs) = span (\b -> binderExplicitness b /= Coq.Explicit) bs

  explicitMap <-
    let extraImplicit  = "non-initial implicit arguments"
        complexBinding = "complex (let/generalized) bindings"
    in either dtaEditFailure (pure . M.fromList) . forFold ebs $ \case
         ExplicitBinder x              -> Right [(x, Coq.ExplicitBinder x)]
         Typed    g Coq.Explicit xs ty -> Right [(x, Typed g Coq.Explicit (pure x) ty) | x <- toList xs]

         ImplicitBinders _           -> Left extraImplicit
         Typed{}                     -> Left extraImplicit

         Generalized _ _   -> Left complexBinding

  let editIdents  = S.fromList $ dta^.dtParameters <> dta^.dtIndices
      boundIdents = fmap S.fromList . traverse (view nameToIdent) $ foldMap (toListOf binderNames) ebs
                       -- Underscores are an automatic failure
    in unless (boundIdents == Just editIdents) $
         dtaEditFailure "mismatched names"

  let coalesceTypedBinders [] = []
      coalesceTypedBinders (Typed g ei xs0 ty : bs) =
        let (tbs, bs') = flip span bs $ \case
                           Typed g' ei' _ ty' -> g == g' && ei == ei' && ty == ty'
                           _                  -> False
        in Typed g ei (foldl' (\xs b -> case b of Typed _ _ xs' _ -> xs <> xs'; _ -> xs) xs0 tbs) ty : coalesceTypedBinders bs'
      coalesceTypedBinders (b : bs) =
        b : coalesceTypedBinders bs

      gemkBindersFor = coalesceTypedBinders . map ((explicitMap M.!) . Ident) . (dta^.)

  pure (ibs ++ gemkBindersFor dtParameters, gemkBindersFor dtIndices)

--------------------------------------------------------------------------------

convertDataDefn :: LocalConvMonad r m
                => Term -> [Binder] -> HsDataDefn GhcRn
                -> m (Term, [Constructor])
#if __GLASGOW_HASKELL__ >= 910
convertDataDefn curType extraArgs (HsDataDefn NOEXTP lcxt _ctype ksig cons _derivs) = do
  when (isJust lcxt) $ convUnsupported' "data type contexts"
#elif __GLASGOW_HASKELL__ >= 900
convertDataDefn curType extraArgs (HsDataDefn NOEXTP _nd lcxt _ctype ksig cons _derivs) = do
  when (isJust lcxt) $ convUnsupported' "data type contexts"
#else
convertDataDefn curType extraArgs (HsDataDefn NOEXTP _nd lcxt _ctype ksig cons _derivs) = do
  unless (null $ unLoc lcxt) $ convUnsupported' "data type contexts"
#endif
  (,) <$> maybe (pure $ Sort Type) convertLHsType ksig
      <*> (traverse addAdditionalConstructorScope =<<
           foldTraverse (convertConDecl curType extraArgs . unLoc) cons)
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertDataDefn _ _ (XHsDataDefn v) = noExtCon v
#endif

convertDataDecl :: ConversionMonad r m
                => GenLocated l GHC.Name -> [LHsTyVarBndr flag GhcRn] -> HsDataDefn GhcRn
                -> m IndBody
convertDataDecl name tvs defn = do
  coqName   <- var TypeNS $ unLoc name

  addKindVars <- view (edits.polyKinds.at coqName) >>= \case
    Just ids -> pure $ (++) ((\id -> mkTypedBinder Implicit (Ident $ Bare id) $ Qualid (Bare "Type")) <$> toList ids)
    Nothing  -> pure id
  kinds     <- (++ repeat Nothing) . map Just . maybe [] NE.toList <$> view (edits.dataKinds.at coqName)
  let cvtName tv = Ident <$> var TypeNS (unLoc tv)
  let getName (L _ (UserTyVar NOEXTP GHC_900(_) name)) = name
      getName (L _ (KindedTyVar NOEXTP GHC_900(_) name _)) = name
#if __GLASGOW_HASKELL__ >= 806
      getName (L _ (XTyVarBndr v)) = noExtCon v
#endif
      mkBndr (Just t) n = mkBinders Coq.Explicit (n NE.:| []) t
      mkBndr Nothing n = ExplicitBinder n

  rawParams <- addKindVars <$> zipWithM (\n t -> mkBndr t <$> cvtName (getName n)) tvs kinds

  (params, indices) <-
    view (edits . dataTypeArguments . at coqName) >>= \case
      Just dta -> rewriteDataTypeArguments dta rawParams
      Nothing  -> pure (rawParams, [])
  let conIndices = toImplicitBinder <$> indices

  let curType  = appList (Qualid coqName) . binderArgs $ params ++ indices
  (resTy, cons) <- first (maybeForall indices)
                     <$> withCurrentDefinition coqName (convertDataDefn curType conIndices defn)

  conNames <- filterM (view . (edits.skippedConstructors.:notContains)) [con | (con,_,_) <- cons]
  storeConstructors coqName conNames
  for_ conNames $ \con -> do
    storeConstructorType con coqName
    lookupConstructorFields con >>= \case
      Just (RecordFields fields) ->
        for_ fields $ \field -> storeRecordFieldType field coqName
      _ ->
        pure ()

  -- Coq 8.20 auto-lowers eligible inductives (declared as Type) to Prop,
  -- which breaks pattern matching in non-Prop return contexts.  Detect these
  -- cases and explicitly annotate with `: Set` to prevent the lowering.
  -- Affected: empty types (0 constructors) and single-constructor types with
  -- no arguments.  Constructor args may appear as arrows in the return type
  -- rather than as binders, so we check both representations.
  let finalResTy = case resTy of
        Sort Type | propLowerable cons -> Sort Set
        _                              -> resTy
      propLowerable []                       = True
      propLowerable [(_, binders, mty)]      = null binders && not (hasArrows mty)
      propLowerable _                        = False
      hasArrows (Just (Coq.Arrow _ _))       = True
      hasArrows _                            = False

  -- Universe edits are also applied to 'redefine Inductive' bodies
  -- via applyUniverseEdit in TyCl.hs.
  univStatus <- views edits (lookupUniverseStatus coqName)
  pure $ IndBody coqName params finalResTy cons univStatus
