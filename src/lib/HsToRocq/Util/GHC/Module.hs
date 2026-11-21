{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP, StandaloneDeriving, DeriveAnyClass #-}

module HsToRocq.Util.GHC.Module (
  module Module, ModuleData(..),
  moduleNameText, mkModuleNameT,
  modName, modExports, modDetails, modCallbackUses, modMethodCalls) where

import Data.Text (Text)
import qualified Data.Text as T

import Control.Lens

import qualified GHC
import HsToRocq.Util.GHC.Callbacks (CallbackUses)
import HsToRocq.Util.GHC.MethodCalls (MethodCalls)
#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins hiding ((<>))
import GHC.Core.InstEnv (InstEnv, unionInstEnv)
import GHC.Unit.Module as Module
import GHC.Unit.Module.ModDetails (ModDetails(..), emptyModDetails)
#else
import Module
import HscTypes (ModDetails(..), emptyModDetails)
#endif


-- Note: the names in the list of module exports are from before any renaming
-- has occurred.
data ModuleData = ModuleData { _modName     :: ModuleName
                             , _modExports  :: [GHC.Name]
                             , _modDetails  :: ModDetails
                             , _modCallbackUses :: CallbackUses
                             , _modMethodCalls :: MethodCalls
                             } 
makeLenses ''ModuleData

instance Semigroup ModDetails where
#if __GLASGOW_HASKELL__ >= 806
  ModDetails e1 t1 i1 f1 r1 a1 c1 <> ModDetails e2 t2 i2 f2 r2 a2 c2 =
    -- md_vect_info is discarded
    ModDetails (e1 <> e2) (t1 <> t2) (i1 <> i2) (f1 <> f2) (r1 <> r2) (a1 <> a2) (c1 <> c2)
#else
  ModDetails e1 t1 i1 f1 r1 a1 v1 c1 <> ModDetails e2 t2 i2 f2 r2 a2 _v2 c2 =
    -- md_vect_info is discarded
    ModDetails (e1 <> e2) (t1 <> t2) (i1 <> i2) (f1 <> f2) (r1 <> r2) (a1 <> a2) v1 (c1 <> c2)
#endif

instance Monoid ModDetails where
  mempty = emptyModDetails

-- GHC 9.x provides Show ModuleName upstream, so the orphan instance is
-- only needed for older GHC. Instead, GHC 9.x needs a Semigroup InstEnv
-- instance (used by the ModDetails Semigroup above via md_insts field).
#if __GLASGOW_HASKELL__ >= 900
instance Semigroup InstEnv where
  (<>) = unionInstEnv
#else
instance Show ModuleName where
  showsPrec p mod = showParen (p >= 11)
                  $ showString "ModuleName " . showsPrec 11 (moduleNameString mod)
#endif

-- should this have ModuleData as a parameter instead of ModuleName?
moduleNameText :: ModuleName -> Text
moduleNameText = T.pack . moduleNameString

mkModuleNameT :: Text -> ModuleName
mkModuleNameT = mkModuleName . T.unpack
