{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase, RecordWildCards,
             OverloadedStrings,
             FlexibleContexts,
             TemplateHaskell,
             ScopedTypeVariables,
             RankNTypes #-}

#include "ghc-compat.h"

module HsToRocq.CLI (
  -- * General main-action creator
  processFilesMain,
  -- * Specific application processors
  printConvertedModules,
  convertAndPrintModules,
  WithModulePrinter,
  -- * CLI configuration, parameters, etc.
  Config(..),
  outputFile, preambleFile, midambleFile, editsFiles, leniency, processingMode,
  modulesFiles, modulesRoot, directInputFiles, ifaceDirs, cfgRocqVersion,
  processArgs,
  ProgramArgs(..),
  argParser, argParserInfo,
  -- * Utility functions
  prettyPrint, hPrettyPrint
  ) where

import Control.Lens hiding (Strict, (<.>))

import Data.Foldable
import Data.List (intersperse, isSuffixOf)
import Data.List.NonEmpty (NonEmpty(..))

import Data.Functor
import HsToRocq.Util.Traversable
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Except

import System.FilePath
import System.Directory
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.IO
import System.Exit

import GHC
#if __GLASGOW_HASKELL__ >= 910
import GHC.Driver.Session hiding (outputFile)
import GHC.Unit.Module
import GHC.Data.Bag (bagToList)
import GHC.Types.Error (getMessages)
import GHC.Driver.Errors.Ppr ()  -- instance Diagnostic DriverMessage => pprDiagnostic
import GHC.Utils.Error (pprMsgEnvelopeBagWithLocDefault)
import GHC.Utils.Outputable (showSDocUnsafe)
import qualified GHC.Utils.Outputable as GHCOut
#elif __GLASGOW_HASKELL__ >= 900
import GHC.Driver.Session hiding (outputFile)
import GHC.Unit.Module
import GHC.Driver.CmdLine (Warn(..))
#else
import DynFlags hiding (outputFile)
import Module
import CmdLineParser (Warn(..))
#endif
import HsToRocq.Util.GHC.Exception

import HsToRocq.Edits.Parser (parseEditList, runParser, prettyParseError)
import HsToRocq.Edits.Types

import HsToRocq.Util.Monad
import HsToRocq.Util.Messages
import HsToRocq.Util.GHC.Module
import HsToRocq.PrettyPrint hiding ((</>))
import HsToRocq.Rocq.Gallina.Util
import HsToRocq.Util.FVs
import HsToRocq.Rocq.Pretty
import HsToRocq.Rocq.Gallina (RocqVersion(..), Sentence)
import HsToRocq.Rocq.Preamble
import HsToRocq.ProcessFiles
import HsToRocq.ConvertHaskell
import HsToRocq.ConvertHaskell.TypeInfo
import HsToRocq.CLI.FileTree
import HsToRocq.CLI.FileTree.Parser

import Options.Applicative

hPrettyPrint :: MonadIO m => Handle -> Doc -> m ()
hPrettyPrint h = liftIO . displayIO h . renderPretty 0.67 120

prettyPrint :: MonadIO m => Doc -> m ()
prettyPrint = hPrettyPrint stdout

data ProgramArgs = ProgramArgs { outputFileArg          :: !(Maybe FilePath)
                               , preambleFileArg        :: !(Maybe FilePath)
                               , midambleFileArg        :: !(Maybe FilePath)
                               , editsFilesArgs         :: ![FilePath]
                               , translationLeniencyArg :: !Leniency
                               , processingModeArg      :: !ProcessingMode
                               , modulesFilesArgs       :: ![FilePath]
                               , modulesRootArg         :: !(Maybe FilePath)
                               , ifaceDirsArgs          :: ![FilePath]
                               , dependencyDirArg       :: !(Maybe FilePath)
                               , importDirsArgs         :: ![FilePath]
                               , includeDirsArgs        :: ![FilePath]
                               , ghcTreeDirsArgs        :: ![FilePath]
                               , ghcOptionsArgs         :: ![String]
                               , directInputFilesArgs   :: ![FilePath]
                               , rocqVersionArg         :: !RocqVersion
                               }
                 deriving (Eq, Ord, Show, Read)

argParser :: Parser ProgramArgs
argParser = ProgramArgs <$> optional (strOption       $  long    "output"
                                                      <> short   'o'
                                                      <> metavar "FILE"
                                                      <> help    "File to write the translated Coq code to (defaults to stdout)")

                        <*> optional (strOption       $  long    "preamble"
                                                      <> short   'p'
                                                      <> metavar "FILE"
                                                      <> help    "File containing code that goes at the top of the Coq output")

                        <*> optional (strOption       $  long    "midamble"
                                                      <> short   'm'
                                                      <> metavar "FILE"
                                                      <> help    "File containing code that goes after the type declarations")

                        <*> many     (strOption       $  long    "edits"
                                                      <> short   'e'
                                                      <> metavar "FILE"
                                                      <> help    "File with extra Haskell -> Coq edits")

                        <*> asum [ flag' Strict       $  long    "strict"
                                                      <> short   'S'
                                                      <> help    "Fail hard if a definition can't be translated (default)"
                                 , flag' Permissive   $  long    "permissive"
                                                      <> short   'P'
                                                      <> help    "Try to skip or produce fallback definitions for definitions that can't be translated"
                                 , pure  Strict ]

                        <*> asum [ flag' Recursive    $  long    "recursive"
                                                      <> short   'R'
                                                      <> help    "Translate dependencies of the given modules (default)"
                                 , flag' NonRecursive $  long    "nonrecursive"
                                                      <> short   'N'
                                                      <> help    "Only translate the given modules, and not their dependencies"
                                 , pure  Recursive ]

                        <*> many     (strOption       $  long    "modules"
                                                      <> short   'm'
                                                      <> metavar "FILE"
                                                      <> help    "File listing Haskell files to translate into Coq, in an indented tree structure")

                        <*> optional (strOption       $  long    "modules-dir"
                                                      <> short   'd'
                                                      <> metavar "DIR"
                                                      <> help    "The directory the module tree files' contents are rooted at")

                        <*> many     (strOption       $  long    "iface-dir"
                                                      <> metavar "DIR"
                                                      <> help    "Directory to search for hs-to-rocq interface files (.h2ci)" )

                        <*> optional (strOption       $  long    "dependency-dir"
                                                      <> metavar "DIR"
                                                      <> help    "Directory to write interface file dependencies to")

                        <*> many     (strOption       $  long    "import-dir"
                                                      <> short   'i'
                                                      <> metavar "DIR"
                                                      <> help    "Directory to search for Haskell modules")

                        <*> many     (strOption       $  long    "include-dir"
                                                      <> short   'I'
                                                      <> metavar "DIR"
                                                      <> help    "Directory to search for CPP `#include's")

                        <*> many     (strOption       $  long    "ghc-tree"
                                                      <> metavar "DIR"
                                                      <> help    "Add the usual ghc build tree subdirectories rooted atDIR to the module search path")

                        <*> many     (strOption       $  long    "ghc"
                                                      <> metavar "ARGUMENT"
                                                      <> help    "Option to pass through to GHC")

                        <*> many     (strArgument     $  metavar "FILES"
                                                      <> help    "Haskell files to translate into Coq")

                        <*> option   (eitherReader parseRocqVersion)
                                                      (  long    "target-version"
                                                      <> metavar "VERSION"
                                                      <> value   Rocq_8_20
                                                      <> help    "Target Rocq version: 8.20 (default) or 9.0")

parseRocqVersion :: String -> Either String RocqVersion
parseRocqVersion "8.20" = Right Rocq_8_20
parseRocqVersion "9.0"  = Right Rocq_9_0
parseRocqVersion s      = Left $ "Unknown Rocq version '" ++ s ++ "'. Supported: 8.20, 9.0"

argParserInfo :: ParserInfo ProgramArgs
argParserInfo = info (helper <*> argParser) $  fullDesc
                                            <> progDesc "Convert Haskell source files to Coq"

data Config = Config { _outputFile          :: !(Maybe FilePath)
                     , _preambleFile        :: !(Maybe FilePath)
                     , _midambleFile        :: !(Maybe FilePath)
                     , _editsFiles          :: ![FilePath]
                     , _translationLeniency :: !Leniency
                     , _processingMode      :: !ProcessingMode
                     , _modulesFiles        :: ![FilePath]
                     , _modulesRoot         :: !(Maybe FilePath)
                     , _directInputFiles    :: ![FilePath]
                     , _ifaceDirs           :: ![FilePath]
                     , _dependencyDir       :: !(Maybe FilePath)
                     , _cfgRocqVersion      :: !RocqVersion
                     }
            deriving (Eq, Ord, Show, Read)
makeLenses ''Config

ghcInputDirs :: FilePath -> [FilePath]
-- GHC 9.10 reorganized the source tree; all needed modules are under compiler/
ghcInputDirs base = [base </> "compiler"]

processArgs :: GhcMonad m => m Config
processArgs = do
  ProgramArgs{..} <- liftIO $ customExecParser defaultPrefs{prefMultiSuffix="..."} argParserInfo

  -- Translation needs types, not native objects. Shared source dependencies can
  -- race on .o.tmp files when separate translator processes generate code.
  let defaultArgs = map (mkGeneralLocated "defaultArgs") $
        words "-no-link -fno-code -hidir=.ghc-tmp -odir=.ghc-tmp"

  let ghcArgs = let locate opt = mkGeneralLocated $ "command line (" ++ opt ++ ")"
                in defaultArgs ++
                   map (locate "-i"         . ("-i" ++)) importDirsArgs ++
                   map (locate "-I"         . ("-I" ++)) includeDirsArgs ++
                   map (locate "--ghc-tree" . ("-i" ++)) (concatMap ghcInputDirs ghcTreeDirsArgs) ++
                   map (locate "--ghc")                  ghcOptionsArgs

  -- GHC 9.10 removed Warn type; warnings are now a Messages bag, not [Warn]
#if __GLASGOW_HASKELL__ >= 910
  (dflags, ghcRest, warnings) <- (parseDynamicFlagsCmdLine ?? ghcArgs) =<< getSessionDynFlags
  let numWarns = length (bagToList (getMessages warnings))
  when (numWarns > 0) $ liftIO $ do
    hPutStrLn stderr $ "Command-line argument warnings (" ++ show numWarns ++ "):"
    hPutStrLn stderr $ showSDocUnsafe $ GHCOut.vcat $ pprMsgEnvelopeBagWithLocDefault (getMessages warnings)
#else
  (dflags, ghcRest, warnings) <- (parseDynamicFlagsCmdLine ?? ghcArgs) =<< getSessionDynFlags
  printAllIfPresent unLoc "Command-line argument warning" (map warnMsg warnings)
#endif
  printAllIfPresent unLoc "Ignored GHC arguments"         ghcRest

  void $ setSessionDynFlags dflags

  pure $ Config { _outputFile          = if outputFileArg == Just "-"
                                         then Nothing
                                         else outputFileArg
                , _preambleFile        = preambleFileArg
                , _midambleFile        = midambleFileArg
                , _editsFiles          = editsFilesArgs
                , _translationLeniency = translationLeniencyArg
                , _processingMode      = processingModeArg
                , _modulesFiles        = modulesFilesArgs
                , _modulesRoot         = modulesRootArg
                , _directInputFiles    = directInputFilesArgs
                , _ifaceDirs           = ifaceDirsArgs
                , _dependencyDir       = dependencyDirArg
                , _cfgRocqVersion      = rocqVersionArg
                }

parseModulesFiles :: (MonadIO m, MonadError String m)
                  => FilePath -> [FilePath] -> m [FilePath]
parseModulesFiles root files =
  let fullName name = root </> if ".hs" `isSuffixOf` name
                               then name
                               else name <.> "hs"
  in fmap (map fullName . resolveFileTrees) . forFold files $ \file ->
       exceptEither . parseFileTrees (Just file) =<< liftIO (readFile file)

--------------------------------------------------------------------------------

type WithModulePrinter m =
    ModuleName ->
    (Handle -> m ()) -> -- print type declarations
    (Handle -> m ()) -> -- print rest
    m ()

processFilesMain ::
    forall m . GhcMonad m
    => (forall r m. GlobalMonad r m => WithModulePrinter m -> [TypecheckedModule] -> m ())
    -> m ()
processFilesMain process = do
  conf <- processArgs

  let parseConfigFiles files builder parser =
        liftIO . forFold (conf^.files) $ \filename ->
          T.readFile filename >>= (\case
            Left  err -> die $ unlines $ map (prettyParseError filename) err
            Right res -> either die pure $ builder res) . runParser parser

  edits <- parseConfigFiles editsFiles buildEdits parseEditList

  inputFiles <- either (liftIO . die) pure <=< runExceptT $
                  (++) <$> parseModulesFiles (conf^.modulesRoot.non "") (conf^.modulesFiles)
                       <*> pure (conf^.directInputFiles)

  let rewriteVFileContent s = rewriteTextFor (conf^.cfgRocqVersion) (T.pack s)

  preambles <- liftIO $ traverse readFile (conf^.preambleFile)
  let printPreambles hOut = liftIO $ do
        T.hPutStr hOut (staticPreamble (conf^.cfgRocqVersion))
        hPutStrLn hOut ""
        unless (null preambles) $ do
          hPutStrLn hOut "(* Preamble *)"
          hPutStrLn hOut ""
        for_ preambles $ \contents -> do
            T.hPutStr hOut (rewriteVFileContent contents)
            hPutStrLn hOut ""
            hFlush    hOut

  midambles <- liftIO $ traverse readFile (conf^.midambleFile)
  let printMidambles hOut = liftIO $ do
        unless (null midambles) $ do
          hPutStrLn hOut "(* Midamble *)"
          hPutStrLn hOut ""
        for_ midambles $ \contents -> do
            T.hPutStr hOut (rewriteVFileContent contents)
            hPutStrLn hOut ""
            hFlush    hOut

  let withModulePrinter :: forall r m. GlobalMonad r m => WithModulePrinter m
      withModulePrinter = case conf^.outputFile of
        Nothing  -> \mod act1 act2 -> do
            liftIO . putStrLn $ "(* " ++ moduleNameString mod ++ " *)"
            liftIO $ putStrLn ""
            printPreambles stdout
            void $ act1 stdout
            printMidambles stdout
            void $ act2 stdout
        Just outDir -> \mod act1 act2 -> do
          let path = outDir </> moduleNameSlashes mod <.> "v"
          liftIO . createDirectoryIfMissing True $ takeDirectory path
          gWithFile path WriteMode $ \hOut -> do
            printPreambles hOut
            void $ act1 hOut
            printMidambles hOut
            void $ act2 hOut
          let ifacepath = outDir </> moduleNameSlashes mod <.> "h2ci"
          serializeIfaceFor (moduleNameText mod) ifacepath
          for_ (conf^.dependencyDir) $ \dir -> do
            let deppath = dir </> moduleNameString mod <.> "mk"
            gWithFile deppath WriteMode $ \hOut -> do
              deps <- loadedInterfaceFiles
              liftIO $ hPutStrLn hOut $ path ++ ": " ++ unwords deps


  runGlobalMonad edits (conf^.translationLeniency) (conf^.ifaceDirs) (conf^.cfgRocqVersion) $
    traverse_ (process withModulePrinter) =<< processFiles (conf^.processingMode) inputFiles

printConvertedModule :: GlobalMonad r m
                     => WithModulePrinter m
                     -> ConvertedModule
                     -> m ()
printConvertedModule withModulePrinter cmod@ConvertedModule{..} = do
  ModuleDeclarations{..} <- moduleDeclarations cmod

  version <- view rocqVersion
  let rewrite :: [Sentence] -> [Sentence]
      rewrite = rewriteASTFor version

      imports'  = rewrite convModImports
      typDecls' = rewrite moduleTypeDeclarations
      valDecls' = rewrite moduleValueDeclarations

  let fvs = toList . getFVs $ foldScopes bvOf (typDecls' ++ valDecls') mempty

      printUnbound out =
        unless (null fvs) $ do
          hPrettyPrint out $
            line <> "(*" <+> hang 2
              ("External variables:" <!> fillSep (map (text . qualidToIdent) fvs))
            <!> "*)" <> line
          hFlush out

      printImportsTypes out = liftIO $ do
          printThe out "imports"            mempty imports'   <* gap out
          printThe out "type declarations"  line   typDecls'  <* gap out
      printValues out = liftIO $ do
          printThe out "value declarations" line   valDecls'  <* hFlush out
          printUnbound out

  withModulePrinter convModName printImportsTypes printValues
 where
  gap out = hPutStrLn out "" >> hFlush out

  printThe out what sep ds = do
    printTheHeader out what ds
    unless (null ds) $ do
      gap out
      traverse_ (hPrettyPrint out) . intersperse sep $
        map ((<> line) . renderGallina) ds

  printTheHeader out what ds
    | all isComment ds = hPutStrLn out $ "(* No " ++ what ++ " to convert. *)"
    | otherwise = hPutStrLn out $ "(* Converted " ++ what ++ ": *)"

printConvertedModules :: GlobalMonad r m
                      => WithModulePrinter m
                      -> [NonEmpty ConvertedModule]
                      -> m ()
printConvertedModules withModulePrinter =
  traverse_ (printConvertedModule withModulePrinter) . foldMap toList

convertAndPrintModules :: GlobalMonad r m => WithModulePrinter m -> [TypecheckedModule] -> m ()
convertAndPrintModules p = printConvertedModules p <=< convertModules <=< traverse toRenamedHsGroup
  where
    toRenamedHsGroup tcm
      -- GHC 9.10 added a Docs field to tm_renamed_source (5-tuple vs 4-tuple)
#if __GLASGOW_HASKELL__ >= 910
      | Just (hs_group, _, _, _, _) <- tm_renamed_source tcm =
#else
      | Just (hs_group, _, _, _) <- tm_renamed_source tcm =
#endif
          let (_, modDetails) = tm_internals_ tcm in
          let exports = modInfoExports (tm_checked_module_info tcm) 
              modData = ModuleData {_modName = mod, _modExports = exports, _modDetails = modDetails} in
          pure (modData, hs_group)
      | otherwise = throwProgramError $  "Renamer failed for `" ++ moduleNameString mod ++ "'"
      where mod = ms_mod_name . pm_mod_summary $ tm_parsed_module tcm

