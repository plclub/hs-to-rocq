{-# LANGUAGE CPP, FlexibleContexts, OverloadedStrings #-}

#include "ghc-compat.h"

module HsToRocq.ConvertHaskell.Type (
  convertType,
  convertBindingType,
  convertKind,
  convertTyCon,
  convertPredType) where

import Data.List.NonEmpty (NonEmpty(..))
import Control.Lens

#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins hiding ((<>), App, InScope)
import GHC.Core.TyCo.Rep
#if __GLASGOW_HASKELL__ >= 910
import GHC.Core.TyCo.Tidy (tidyTopType)
import Data.Maybe (fromMaybe)
import Data.Bifunctor (first, second)
import HsToRocq.Util.GHC.Module (modName, moduleNameText)
#endif
#else
#if __GLASGOW_HASKELL__ >= 808
import Var
#endif
import TyCoRep
import TyCon
import Type (isPredTy)
import Name (getName)
#endif

import HsToRocq.Rocq.Gallina as Coq
import HsToRocq.Rocq.Gallina.Util
import HsToRocq.Edits.Types

import HsToRocq.ConvertHaskell.Variables
import HsToRocq.ConvertHaskell.Literals
import HsToRocq.ConvertHaskell.Monad

-- | Convert a TyCon application, filtering out invisible binder args.
-- Uses tyConBinders to determine which args are visible. Note: GHC 9.10's
-- FunTyCon reports 0 tyConBinders, so callers must handle (->) specially
-- (see the arrow case below) to avoid filtering against an empty binder list.
convertTyConApp :: ConversionMonad r m => Bool -> TyCon -> [KindOrType] -> Qualid -> m Term
convertTyConApp b tc ts ctc = do
  let cond = if b then const True else fst
  let rest = repeat True
  ts' <- mapM (convertType . snd) $ filter cond $
    zip ((isVisibleTyConBinder <$> tyConBinders tc) <> rest) ts
  case ts' of
    ct : cts' -> pure $ App (Qualid ctc) $ PosArg <$> (ct :| cts')
    _         -> pure $ Qualid ctc

convertType_ :: ConversionMonad r m => Bool -> Type -> m Term
convertType_ _ (TyVarTy tv) = Qualid <$> var TypeNS (getName tv)
convertType_ b (AppTy ty1 ty2) = App1 <$> convertType_ b ty1 <*> convertType_ b ty2
convertType_ _ (TyConApp tc []) = Qualid <$> convertTyCon tc
convertType_ b (TyConApp tc ts@(_:_)) = do
  convertedTc <- convertTyCon tc
  case convertedTc of
    (Qualified m t) | m == "GHC.Prim" && t == "TYPE"
                      -> pure $ Qualid (Bare "Type")
                    -- GHC 9.10: (->) has no tyConBinders (it's a FunTyCon).
                    -- When partially applied with only RuntimeRep args
                    -- (e.g., (->) @LiftedRep @LiftedRep in instance heads),
                    -- drop them and return plain GHC.Prim.arrow.
                    | m == "GHC.Prim" && t == "arrow" && null (tyConBinders tc)
                      -> convertTyConApp b tc [] convertedTc
                    | m == "GHC.Tuple" && length ts > 1 ->
                      if (t == "pair_type" || t == "op_Z2T__") || (t == "triple_type" && length ts > 2) ||
                         (t == "quad_type" && length ts > 3) || (t == "quint_type" && length ts > 4) ||
                         (t == "sext_type" && length ts > 5) || (t == "sept_type" && length ts > 6)
                      then (`InScope` "type") . foldl1 (mkInfix ?? "*") <$> traverse (convertType_ b) ts
                      else convertTyConApp b tc ts convertedTc
    _ -> convertTyConApp b tc ts convertedTc
convertType_ b (ForAllTy tv ty) = do
  convertedTv <- convertTyVarBinder Coq.Implicit tv
  convertedTy <- convertType_ b ty
  pure $ Forall (convertedTv :| []) convertedTy
-- GHC 9.0+ added a Mult (multiplicity) field to FunTy for linear types.
-- The MULT macro absorbs this field; we discard it (Coq has no linear types).
#if __GLASGOW_HASKELL__ >= 900
#define MULT _
#else
#define MULT
#endif
-- GHC 9.10 replaced AnonArgFlag (InvisArg/VisArg) with FunTyFlag, which has
-- more cases. isInvisibleFunArg provides a version-portable visibility check.
#if __GLASGOW_HASKELL__ >= 910
convertType_ b (FunTy af MULT ty1 ty2)
  | isInvisibleFunArg af = do
    cons <- convertPredType ty1
    Forall (Generalized Coq.Implicit cons :| []) <$> convertType_ b ty2
  | otherwise = Arrow <$> convertType_ b ty1 <*> convertType_ b ty2
#elif __GLASGOW_HASKELL__ >= 810
convertType_ b (FunTy InvisArg MULT ty1 ty2)  = do
  cons <- convertPredType ty1
  Forall (Generalized Coq.Implicit cons :| []) <$> convertType_ b ty2
convertType_ b (FunTy VisArg MULT ty1 ty2) = Arrow <$> convertType_ b ty1 <*> convertType_ b ty2
#else
convertType_ b (FunTy ty1 ty2) | isPredTy ty1 = do
                                   cons <- convertPredType ty1
                                   Forall (Generalized Coq.Implicit cons :| []) <$> convertType_ b ty2
                               | otherwise    = Arrow <$> convertType_ b ty1 <*> convertType_ b ty2
#endif                                   
convertType_ _ (LitTy tl) = case tl of
  NumTyLit int  -> either convUnsupported' (pure . Num) $ convertInteger "type-level integers" int
  StrTyLit str  -> pure $ convertFastString str
  CharTyLit _   -> convUnsupported' "type-level character literals"
convertType_ _ (CastTy _ty _coercion) = convUnsupported' "Kind cast"
convertType_ _ (CoercionTy _coercion) = convUnsupported' "Injection of a Coercion into a type"
  
convertType :: ConversionMonad r m => Type -> m Term
convertType = convertType_ False

-- A value can expose more type arguments after its first term argument,
-- possibly behind a synonym. Mark those binders non-maximal: partial
-- application must still produce a polymorphic value. Only inspect the
-- result spine; keep aliases in argument types and ordinary results intact.
convertBindingType :: ConversionMonad r m => Type -> m Term
#if __GLASGOW_HASKELL__ >= 910
convertBindingType ty = case expose False ty of
  Nothing -> convertType ty
  Just (aliases, ty') -> do
    allowed <- and <$> traverse unchangedLocal aliases
    if allowed then mark False <$> convertType (tidyTopType ty') else convertType ty
 where
  -- Do not look through an external model or a substituted declaration.
  unchangedLocal tc = do
    let n = getName tc
    home <- view (currentModule.modName)
    q <- convertTyCon tc
    task <- definitionTask q
    pure $ (moduleName <$> nameModule_maybe n) == Just home
           && q == Qualified (moduleNameText home) (bareName n)
           && task == TranslateIt
  expose after (ForAllTy b body)
    | after = Just $ second (ForAllTy b) $ fromMaybe ([],body) (expose True body)
    | otherwise = second (ForAllTy b) <$> expose False body
  expose after (FunTy af mult arg res) =
    second (FunTy af mult arg) <$> expose (after || not (isInvisibleFunArg af)) res
  expose True t@(TyConApp tc _) | Just t' <- coreView t = first (tc:) <$> expose True t'
  expose _ _ = Nothing

  mark after (Forall bs t) = Forall (if after then fmap nonMax bs else bs) (mark after t)
  mark _ (Arrow a t) = Arrow a (mark True t)
  mark _ t = t
  nonMax (Typed g Coq.Implicit ns k) = Typed g NonMaximal ns k
  nonMax b = b
#else
convertBindingType = convertType
#endif

convertKind :: ConversionMonad r m => Kind -> m Term
convertKind = convertType_ False

convertPredType :: ConversionMonad r m => Kind -> m Term
convertPredType = convertType_ True

convertTyCon :: ConversionMonad r m => TyCon -> m Qualid
convertTyCon tc = var TypeNS $ getName tc

convertTyVarBinder :: ConversionMonad r m => Explicitness -> TyVarBinder -> m Binder
convertTyVarBinder ex bndr = do
  tv <- Ident <$> var TypeNS (getName $ binderVar bndr)
#if __GLASGOW_HASKELL__ >= 808
  tk <- convertKind $ binderType bndr
#else
  tk <- convertKind $ binderKind bndr
#endif
  pure $ mkBinders ex (tv :| []) tk
