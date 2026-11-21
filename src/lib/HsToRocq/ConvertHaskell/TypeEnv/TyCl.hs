{-# LANGUAGE CPP, DeriveDataTypeable, RecordWildCards, FlexibleContexts #-}

module HsToRocq.ConvertHaskell.TypeEnv.TyCl(
  ConvertedTyClEnv,
  ConvertedTyCl,
  convertedTyClName,
  convertedTyClTyVars,
  convertedTyClPredTypes,
  convertedTyClMethods,
  convertedTyClBinderArgs,
  convertedTyClBinders,
  convertTyClEnv,
  convertedTyCl,
  convertTyCl,
  filterVisibleVars,
  unpeelTyClVars
  ) where

import qualified Data.Map as M
import Data.Generics (Data)

#if __GLASGOW_HASKELL__ >= 900
import GHC.Unit.Module.ModDetails
import GHC.Types.Var
import GHC.Core.Class
import GHC.Core.TyCon
import GHC.Types.TypeEnv
import GHC.Tc.Utils.TcType (eqType, tcSplitSigmaTy, transSuperClasses, mkSpecSigmaTy)
import Data.List (nubBy)
#else
import Class
import HscTypes
import TyCon
import Var
#endif

import HsToRocq.Rocq.Gallina
import HsToRocq.Rocq.Gallina.Util
import HsToRocq.Edits.Types

import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.Variables
import HsToRocq.ConvertHaskell.Type

import HsToRocq.ConvertHaskell.TypeEnv.Id

data ConvertedTyCl =
  ConvertedTyCl { convertedTyClName :: Qualid 
                  -- A map from type variable name to the variable's kind, we
                  -- don't use [Binder] here because we don't know the
                  -- explicitness
                , convertedTyClTyVars  :: [(Qualid, Term)]
                , convertedTyClVisibility :: [Explicitness]
                , convertedTyClPredTypes   :: [Term]
                , convertedTyClMethods :: [(Qualid, Term)]
                }
  deriving (Eq, Ord, Show, Data)

type ConvertedTyClEnv = M.Map Qualid ConvertedTyCl

convertedTyCl :: Qualid -> ConvertedTyClEnv -> Maybe ConvertedTyCl
convertedTyCl = M.lookup

isTyClConstraint :: Binder -> Qualid -> Bool
isTyClConstraint (Generalized _ex t) className = go t className
  where go :: Term -> Qualid -> Bool
        go (App t _args) className = go t className
        go (Qualid q) className = q == className
        go _t _className = False
isTyClConstraint _binder _className = False

unpeelTyClVars :: Term -> Qualid -> Term
unpeelTyClVars (Forall bs t) className
  | any (`isTyClConstraint` className) bs = t
  | otherwise                             = unpeelTyClVars t className
unpeelTyClVars t _className = t

convertedTyClBinderArgs :: ConvertedTyCl -> [Binder]
convertedTyClBinderArgs ConvertedTyCl{..} =
  (\(ex, (q, t)) -> mkTypedBinder ex (Ident q) t)
   <$> zip convertedTyClVisibility convertedTyClTyVars

convertedTyClBinders :: ConvertedTyCl -> [Binder]
convertedTyClBinders tc@ConvertedTyCl{..} =
  convertedTyClBinderArgs tc <> (Generalized Implicit <$> convertedTyClPredTypes)

convertTyClEnv :: ConversionMonad r m => ModDetails -> m ConvertedTyClEnv
convertTyClEnv mod = do
  cls <- convertTyCls mod
  pure $ M.fromList $ fmap (\cl -> (convertedTyClName cl, cl)) cls

convertTyCls :: ConversionMonad r m => ModDetails -> m [ConvertedTyCl]
convertTyCls mod = do
  let typeEnv = md_types mod
  let classes = typeEnvClasses typeEnv
  mapM convertTyCl classes

convertTyClVar :: ConversionMonad r m => Var -> m (Qualid, Term)
convertTyClVar tv = do
  name <- var TypeNS $ tyVarName tv
  kind <- convertType $ tyVarKind tv
  pure (name, kind)
  
convertTyCl :: ConversionMonad r m => Class -> m ConvertedTyCl
convertTyCl cl = do
  convertedTyClName      <- var TypeNS $ className cl
  convertedTyClTyVars    <- mapM convertTyClVar $ classTyVars cl
  convertedTyClMethods   <- mapM convertId $ classMethods cl
  convertedTyClPredTypes <- mapM convertPredType $
#if __GLASGOW_HASKELL__ >= 900
    -- A quantified dictionary does not bring the dictionaries for its result's
    -- superclasses into Rocq's context. Infer these from the same GHC constraint
    -- and put them in dependency order before the quantified result.
    let expand p = case tcSplitSigmaTy p of
          (vs@(_:_), theta, res) ->
            map (mkSpecSigmaTy vs theta) (nubBy eqType $ reverse $ transSuperClasses res) ++ [p]
          _ -> [p]
    in concatMap expand (classSCTheta cl)
#else
    classSCTheta cl
#endif
  let convertedTyClVisibility = (\b -> if isVisibleTyConBinder b then Explicit else Implicit)
                               <$> tyConBinders (classTyCon cl)
  pure ConvertedTyCl{..}

filterVisibleVars :: ConvertedTyCl -> [Term] -> [Term]
filterVisibleVars ConvertedTyCl{..} tms =
  snd <$> filter (\(ex, _t) -> ex == Explicit) (zip convertedTyClVisibility tms)
