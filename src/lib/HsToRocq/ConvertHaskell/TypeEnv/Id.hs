{-# LANGUAGE CPP, FlexibleContexts #-}

module HsToRocq.ConvertHaskell.TypeEnv.Id(
  ConvertedIdEnv,
  ConvertedId,
  convertedIdType,
  convertIdEnv,
  convertId,
  idEnvOfModDetails
  ) where

import qualified Data.Map as M

#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins
import GHC.Unit.Module.ModDetails (ModDetails(..))
import GHC.Types.TypeEnv (typeEnvIds)
#else
import HscTypes
import Var
#endif

import HsToRocq.Rocq.Gallina
import HsToRocq.Edits.Types

import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.Variables
import HsToRocq.ConvertHaskell.Type

type ConvertedId = (Qualid, Term)

type ConvertedIdEnv = M.Map Qualid Term

convertedIdType :: Qualid -> ConvertedIdEnv -> Maybe Term
convertedIdType = M.lookup

idEnvOfModDetails :: ConversionMonad r m => ModDetails -> m ConvertedIdEnv
idEnvOfModDetails mod = M.fromList <$> mapM convertId (typeEnvIds $ md_types mod)

convertIdEnv :: ConversionMonad r m => [Id] -> m ConvertedIdEnv
convertIdEnv ids = M.fromList <$> mapM convertId ids

convertId :: ConversionMonad r m => Id -> m ConvertedId
convertId id = (,) <$> var ExprNS (varName id) <*> convertBindingType (varType id)
