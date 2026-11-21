{-# LANGUAGE CPP, DeriveDataTypeable, RecordWildCards, FlexibleContexts, OverloadedStrings #-}
#include "ghc-compat.h"

module HsToRocq.ConvertHaskell.TypeEnv.Instances where

import Data.Generics (Data)
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
import GHC.Types.Name (nameStableString)
#else
import HscTypes
import InstEnv
import Var
import Name (nameStableString)
#endif

data ConvertedInstance =
  ConvertedInstance { convertedInstanceClass :: ConvertedTyCl
                    , convertedInstanceDFun :: String
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
      convertedInstanceDFun = nameStableString (varName (is_dfun inst))
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
  []  -> throwProgramError $ "No checked instance for " <> showP headTy
  _   -> throwProgramError $ "Ambiguous checked instances for " <> showP headTy
  where headTy = appList (Qualid className) (PosArg <$> instTys)
        matchInstance i =
          let cls = convertedInstanceClass i
              args = filterVisibleVars cls (convertedInstanceTypes i)
          in convertedTyClName cls == className && length args == length instTys &&
             and (zipWith matchType instTys args)
        -- Match types, allowing for the env type to have extra type arguments
        -- from GHC's representation polymorphism (e.g., instTy = GHC.Prim.arrow
        -- matching env type = GHC.Prim.arrow LiftedRep LiftedRep)
        matchType needle haystack
          | needle == haystack = True
          | Qualid q <- needle, termHead haystack == Just q = True
          | otherwise = False
