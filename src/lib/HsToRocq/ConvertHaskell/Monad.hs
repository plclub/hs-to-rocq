{-# LANGUAGE CPP, TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings, ScopedTypeVariables,
             RankNTypes, ConstraintKinds, FlexibleContexts,
             TemplateHaskell,
             FunctionalDependencies,
             FlexibleInstances,
             TypeApplications
  #-}

module HsToRocq.ConvertHaskell.Monad (
  -- * Environments
  GlobalEnv(..), ModuleEnv(..), LocalEnv(..),
  -- * Constraints
  GlobalMonad, ConversionMonad, LocalConvMonad,
  HasEdits(..), HasLeniency(..), HasRocqVersion(..), HasCurrentModule(..), HasCurrentDefinition(..),
  runGlobalMonad,
  withCurrentModule,
  withCurrentDefinition,
  -- * Convenience views
  currentModuleAxiomatized, UnusedTyVarMode(..), unusedTyVarModeFor,
  -- * Leniency
  Leniency(..), whenPermissive, handleIfPermissive,
  -- * Testing skippedness/axiomness
  definitionTask, TranslationTask(..), AxiomatizationMode(..),
  -- * Operations
  fresh, gensym, genqid,
  useProgramHere, renamed,
  -- * Errors and warnings
  -- ** Within a definition
  convUnsupported,
  -- ** Within a module
  convUnsupported', convUnsupportedIn, convUnsupportedIns,
  warnConvUnsupported',
  -- ** Anywhere
  convUnsupportedIn', convUnsupportedIns',
  -- ** Edits
  editFailure,
  -- ** General
  throwProgramError,
  -- * Modules
  skipModules, skipModulesBy
  ) where

import Control.Lens hiding (Strict)

import Data.Semigroup (Semigroup(..))
import Data.Text (Text)
import qualified Data.Text as T
import HsToRocq.Util.Monad

import Control.Monad (filterM)
import Control.Monad.Trans.Counter
import Control.Monad.State
import Control.Monad.Reader

import Data.Set (Set)

import HsToRocq.Rocq.Gallina (Qualid, Qualid(..), Ident, RocqVersion(..))
import HsToRocq.Rocq.Pretty
import HsToRocq.Util.GHC.Module (moduleNameText, ModuleData, modName)

import HsToRocq.Edits.Types
import HsToRocq.ConvertHaskell.TypeInfo

-- GHC 9.x replaced the Exception-based ExceptionMonad with MonadCatch,
-- restructured diagnostics into a typed GhcMessage pipeline, and moved
-- warning emission from logWarnings (Bag) to logDiagnostics (Messages).
#if __GLASGOW_HASKELL__ >= 900
import Control.Monad.Catch
#define ExceptionMonad MonadCatch
#define ghandle handle
import GHC
import GHC.Driver.Session (getDynFlags)
import GHC.Driver.Monad (logDiagnostics)
import GHC.Driver.Config.Diagnostic (initDiagOpts)
import GHC.Driver.Errors.Types (GhcMessage(GhcUnknownMessage))
import GHC.Types.Error (DiagnosticReason(WarningWithoutFlag), singleMessage, mkPlainDiagnostic, mkSimpleUnknownDiagnostic, mkLocMessage, MessageClass(MCDiagnostic), Severity(SevWarning))
import GHC.Utils.Error (mkPlainMsgEnvelope)
import GHC.Utils.Outputable (text)
import GHC.Utils.Panic (throwGhcExceptionIO)
#else
import Bag (unitBag)
import DynFlags (getDynFlags)
import ErrUtils (mkPlainWarnMsg)
import Exception
import GhcMonad (logWarnings)
import Outputable (text)
import Panic

logDiagnostics = logWarnings . unitBag
#endif

--------------------------------------------------------------------------------

-- |How to handle translation errors
data Leniency = Permissive -- ^Try to recover by e.g. introducing an axiom
              | Strict     -- ^Blow up
              deriving (Eq, Ord, Enum, Bounded, Show, Read)              

--------------------------------------------------------------------------------

-- The reader states
--
-- In various stages of the program (top-level, module level, definition level)
-- we need to extend the reader environment with additional data.
--
-- mtl’s ReaderT is not extensible, so we have a concrete data type for
-- all three levels, and use the HasFoo type classes from lens to uniformly
-- access the various fields


data GlobalEnv = GlobalEnv
    { _globalEnvEdits       :: !Edits
    , _globalEnvLeniency    :: !Leniency
    , _globalEnvRocqVersion :: !RocqVersion
    } deriving Show

data ModuleEnv = ModuleEnv
    { _moduleEnvEdits         :: !Edits
    , _moduleEnvLeniency      :: !Leniency
    , _moduleEnvRocqVersion   :: !RocqVersion
    , _moduleEnvCurrentModule :: !ModuleData
    }

data LocalEnv = LocalEnv
    { _localEnvEdits             :: !Edits
    , _localEnvLeniency          :: !Leniency
    , _localEnvRocqVersion       :: !RocqVersion
    , _localEnvCurrentModule     :: !ModuleData
    , _localEnvCurrentDefinition :: !Qualid
    }

makeFields ''GlobalEnv
makeFields ''ModuleEnv
makeFields ''LocalEnv

currentModuleAxiomatized :: (HasEdits s Edits, HasCurrentModule s ModuleData) => Getter  s Bool
currentModuleAxiomatized = to $ \s -> s^.edits.axiomatizedModules.contains (s^.currentModule.modName)

data AxiomatizationMode = SpecificAxiomatize | GeneralAxiomatize
                        deriving (Eq, Ord, Enum, Bounded, Show, Read)

data TranslationTask = SkipIt
                     | RedefineIt   RocqDefinition
                     | AxiomatizeIt AxiomatizationMode
                     | TranslateIt
                     deriving (Eq, Ord, Show, Read)

-- |Should this definition be skipped, axiomatized, or translated?
-- `HasEdits`, and `HasCurrentModule`, but that hardly seems necessary.
definitionTask :: forall s m. (MonadReader s m, HasEdits s Edits, HasCurrentModule s ModuleData)
               => Qualid -> m TranslationTask
definitionTask name =
  let isIn :: Lens' Edits (Set Qualid) -> m Bool
      isIn field = view $ edits.field.contains name
  in ifM (isIn skipped)
       (pure SkipIt)
       (view (edits.redefinitions.at name) >>= \case
         Just def ->
           pure $ RedefineIt def
         Nothing  ->
           ifM (view currentModuleAxiomatized)
             (ifM (isIn unaxiomatizedDefinitions)
                (pure TranslateIt)
                (pure $ AxiomatizeIt GeneralAxiomatize))
             (ifM (isIn axiomatizedDefinitions)
                (pure $ AxiomatizeIt SpecificAxiomatize)
                (pure TranslateIt)))

data UnusedTyVarMode = PreserveUnusedTyVars | DeleteUnusedTyVars
                     deriving (Eq, Ord, Enum, Bounded, Show, Read)

unusedTyVarModeFor :: (MonadReader r m, HasEdits r Edits) => Qualid -> m UnusedTyVarMode
unusedTyVarModeFor qid = view (edits.deleteUnusedTypeVariables.contains qid) <&> \case
                           True  -> DeleteUnusedTyVars
                           False -> PreserveUnusedTyVars

-- The constraint aliases, for the three levels of scoping
-- Note that they are subconstraints of each other, so you can call a
-- fuction with a GlobalMonad constraint from one with a LocalConvMonad
-- constraints

-- Unfortunately the r sticks around here, despite being a functional
-- dependency of m

-- | The global monad, used outside specific modules
--
type GlobalMonad r m =
        ( GhcMonad m
        , TypeInfoMonad m
        , MonadReader r m
        , HasEdits r Edits
        , HasLeniency r Leniency
        , HasRocqVersion r RocqVersion
        )

-- | The global monad, used for top-level bindings.
--   Has edits, current module name, access to GHC etc.
type ConversionMonad r m =
        ( GlobalMonad r m
        , HasCurrentModule r ModuleData
        )
-- | The local one monad, additional knows the current function name
--   and a counter for fresh variables
type LocalConvMonad r m =
        ( ConversionMonad r m
        , MonadCounter m
        , HasCurrentDefinition r Qualid
        )

runGlobalMonad :: GhcMonad m =>
    Edits ->
    Leniency ->
    TypeInfoConfig ->
    RocqVersion ->
    (forall r m. GlobalMonad r m => m a) ->
    m a
runGlobalMonad initEdits leniency paths version act =
    runTypeInfoMonad paths $
    runReaderT ?? GlobalEnv{_globalEnvEdits = initEdits, _globalEnvLeniency = leniency, _globalEnvRocqVersion = version} $
    act

withCurrentModule :: GlobalMonad r m =>
    ModuleData ->
    (forall r m. ConversionMonad r m => m a) ->
    m a
withCurrentModule newModule act = do
    _edits    <- view edits
    _leniency <- view leniency
    _version  <- view rocqVersion
    isProcessedModule (moduleNameText (newModule ^. modName)) -- Start collecting the interface
    runReaderT act $ ModuleEnv
        { _moduleEnvEdits         = _edits
        , _moduleEnvLeniency      = _leniency
        , _moduleEnvRocqVersion   = _version
        , _moduleEnvCurrentModule = newModule
        }

withCurrentDefinition :: ConversionMonad r m =>
    Qualid ->
    (forall r m. LocalConvMonad r m => m a) ->
    m a
withCurrentDefinition newDef act = do
    global_edits <- view edits
    local_edits <- view (edits.inEdits.at newDef.non mempty)
    let edits_in_scope = local_edits <> global_edits
    
    -- Subtract out the edits to be excluded for this definition.
    excluded_edits <- view (edits.exceptInEdits.at newDef.non mempty)
    let edits_final = subtractEdits edits_in_scope excluded_edits
    
    _leniency      <- view leniency
    _version       <- view rocqVersion
    _currentModule <- view currentModule
    runCounterT . runReaderT act $ LocalEnv
        { _localEnvEdits             = edits_final
        , _localEnvLeniency          = _leniency
        , _localEnvRocqVersion       = _version
        , _localEnvCurrentModule     = _currentModule
        , _localEnvCurrentDefinition = newDef
        }


gensym :: LocalConvMonad r m => Text -> m Ident
gensym name = do u <- fresh
                 pure $ name <> "_" <> T.pack (show u) <> "__"

genqid :: LocalConvMonad r m => Text -> m Qualid
genqid name = Bare <$> gensym name

throwProgramError :: MonadIO m => String -> m a
throwProgramError = liftIO . throwGhcExceptionIO . ProgramError

convUnsupportedIns' :: MonadIO m => String -> [(String, String)] -> m a
convUnsupportedIns' what locs =
  throwProgramError
    $  what ++ " unsupported"
    ++ if null locs
       then ""
       else " [" ++ unwords ["in " ++ category ++ " " ++ which | (category, which) <- locs] ++ "]"

convUnsupportedIn' :: MonadIO m => String -> String -> String -> m a
convUnsupportedIn' what category which =
  convUnsupportedIns' what [(category, which)]

convUnsupportedIns :: ConversionMonad r m => String -> [(String, String)] -> m a
convUnsupportedIns what locs = do
  mod <- views (currentModule.modName) $ ("module",) . moduleNameString
  convUnsupportedIns' what $ locs ++ [mod]

convUnsupportedIn :: ConversionMonad r m => String -> String -> String -> m a
convUnsupportedIn what category which =
  convUnsupportedIns what [(category, which)]

convUnsupported' :: ConversionMonad r m => String -> m a
convUnsupported' what =
  convUnsupportedIns what []

convUnsupported :: LocalConvMonad r m => String -> m a
convUnsupported what =
  convUnsupportedIn what "definition" . showP =<< view currentDefinition

warnConvUnsupported' :: ConversionMonad r m => SrcSpan -> String -> m ()
warnConvUnsupported' loc what = do
  -- GHC 9.x diagnostic pipeline: wrap message in GhcUnknownMessage to
  -- satisfy the typed Messages framework (replaces old mkPlainWarnMsg).
#if __GLASGOW_HASKELL__ >= 900
  diag_opts <- initDiagOpts <$> getDynFlags
  let mkMsg loc = singleMessage . mkPlainMsgEnvelope diag_opts loc . GhcUnknownMessage . mkSimpleUnknownDiagnostic . mkPlainDiagnostic WarningWithoutFlag []
#else
  mkMsg <- mkPlainWarnMsg <$> getDynFlags
#endif
  let msg = mkMsg loc (text (what ++ " unsupported, skipping translation"))
  logDiagnostics msg

editFailure :: MonadIO m => String -> m a
editFailure what = throwProgramError $ "Could not apply edit: " ++ what

skipModulesBy :: GlobalMonad r m => (a -> ModuleName) -> [a] -> m [a]
skipModulesBy f = filterM $ \a -> view $ edits.skippedModules.contains (f a).to not

skipModules :: GlobalMonad r m => [ModuleName] -> m [ModuleName]
skipModules = skipModulesBy id

useProgramHere :: LocalConvMonad r m => m Bool
useProgramHere = do
    n <- view currentDefinition
    useProgram n <$> view edits

renamed :: HsNamespace -> Qualid -> Lens' Edits (Maybe Qualid)
renamed ns x = renamings.at (NamespacedIdent ns x)
{-# INLINABLE renamed #-}

whenPermissive :: (MonadReader r m, HasLeniency r Leniency) => a -> m (Maybe a)
whenPermissive x =
  view leniency <&> \case
    Permissive -> Just x
    Strict     -> Nothing

handleIfPermissive :: (ExceptionMonad m, MonadReader r m, HasLeniency r Leniency, Exception e)
                   => (e -> m a) -> m a -> m a
handleIfPermissive onError act =
  view leniency >>= \case
    Permissive -> ghandle onError act
    Strict     -> act
