{-# LANGUAGE CPP #-}

module HsToRocq.Util.GHC (
  defaultRunGhc,
  ghcPpr
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import Control.Monad.IO.Class (liftIO)
import System.Exit (exitFailure)

import GHC
import GHC.Paths
-- GHC 9.x moved showPpr to GHC.Driver.Ppr (separate from Outputable)
#if __GLASGOW_HASKELL__ >= 900
import GHC.Driver.Session
import GHC.Driver.Ppr
import GHC.Utils.Outputable
#else
import DynFlags
import Outputable
#endif

ghcPpr :: (GhcMonad m, Outputable a) => a -> m Text
ghcPpr x = fmap T.pack $ showPpr <$> getSessionDynFlags <*> pure x

defaultRunGhc :: Ghc () -> IO ()
defaultRunGhc = defaultErrorHandler defaultFatalMessager defaultFlushOut
              . runGhc (Just libdir)
              -- The CLI sets the session flags after parsing --ghc options.
              -- Setting them here would select the default interpreter
              -- before a caller can request -fexternal-interpreter.
              . handleSourceError (\err -> printException err >> liftIO exitFailure)
