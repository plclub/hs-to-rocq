{-# LANGUAGE CPP, DeriveDataTypeable, RecordWildCards, FlexibleContexts, OverloadedStrings #-}
#include "ghc-compat.h"

module HsToRocq.ConvertHaskell.TypeEnv.Instances where

import Data.Foldable
import Data.Generics (Data, everywhere, mkT)
import Data.Map as M
import Data.Maybe

import HsToRocq.Rocq.Gallina
import HsToRocq.Rocq.Gallina.Util
import HsToRocq.Rocq.Pretty
import HsToRocq.Edits.Types

import HsToRocq.ConvertHaskell.Type
import HsToRocq.ConvertHaskell.TypeEnv.TyCl
import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.Variables

#if __GLASGOW_HASKELL__ >= 900
import GHC.Unit.Module.ModDetails
import GHC.Core.InstEnv
import GHC.Core.RoughMap (RoughMatchTc(..))
import GHC.Types.Var
#else
import HscTypes
import InstEnv
import Var
#endif

data ConvertedInstance =
  ConvertedInstance { convertedInstanceClass :: ConvertedTyCl
                    , convertedInstanceBinds :: [Binder]
                    , convertedInstanceTops  :: [Qualid]
                    , convertedInstanceSubst :: M.Map Qualid Term
                    , convertedInstanceTypes :: [Term]
                    }
  deriving (Eq, Ord, Show, Data)

type ConvertedInstanceEnv = [ConvertedInstance]

instancesOfModDetails :: ConversionMonad r m => ModDetails -> m ConvertedInstanceEnv
-- GHC 9.10: md_insts changed from [ClsInst] to InstEnv; extract via instEnvElts
instancesOfModDetails mod = mapM convertInstance GHC_900($ instEnvElts) $ md_insts mod

convertInstance :: ConversionMonad r m => ClsInst -> m ConvertedInstance
convertInstance inst = do
  let (binds, cls, tms) = instanceHead inst
  convertedInstanceClass <- convertTyCl cls
  convertedInstanceBinds <- mapM tyVarToBinder binds
  convertedInstanceTypes <- mapM convertType tms
  let convertedInstanceSubst = M.fromList $ zip
        (fst <$> convertedTyClTyVars convertedInstanceClass) convertedInstanceTypes
  -- GHC 9.10: is_tcs changed from [Maybe Name] to [RoughMatchTc]
  convertedInstanceTops <- mapM (var TypeNS)
#if __GLASGOW_HASKELL__ >= 900
                             [n | RM_KnownTc n <- is_tcs inst]
#else
                             (catMaybes $ is_tcs inst)
#endif
  pure ConvertedInstance{..}
  where tyVarToBinder tv = do
          name <- var TypeNS  $ varName tv
          typ  <- convertType $ varType tv
          pure $ mkTypedBinder Implicit (Ident name) typ

lookupInstance :: ConversionMonad r m => [Term] -> Qualid -> ConvertedInstanceEnv -> m ConvertedInstance
lookupInstance instTys className env = case Prelude.filter matchInstance env of
  [i] -> pure i
  []  -> throwProgramError $ "The instance " <> showP instHead <> " is not found"
  _   -> throwProgramError $ "The instance " <> showP instHead <> " matches multiple checked instances"
  where instHead = appList (Qualid className) (PosArg <$> instTys)
        -- Source heads omit invisible kind arguments. Compare every visible
        -- argument in order; sharing just one argument does not identify an instance.
        matchInstance i = convertedTyClName (convertedInstanceClass i) == className &&
          let tys = filterVisibleVars (convertedInstanceClass i) (convertedInstanceTypes i)
          in length instTys == length tys && and (zipWith matchType instTys tys)
        -- Match types, allowing for the env type to have extra type arguments
        -- from GHC's representation polymorphism (e.g., instTy = GHC.Prim.arrow
        -- matching env type = GHC.Prim.arrow LiftedRep LiftedRep)
        matchType needle haystack
          | normalize needle == normalize haystack = True
          | Qualid q <- needle, termHead haystack == Just q = True
          | otherwise = False
        normalize = everywhere (mkT normalizeType)
