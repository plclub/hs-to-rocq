{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad (forM_, unless)
import Crypto.Hash (Digest, SHA256, hash)
import qualified Data.ByteString as BS
import qualified Data.List.NonEmpty as NE
import Data.List (intercalate)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import HsToRocq.CLI (ProgramArgs(..), argParserInfo)
import HsToRocq.ConvertHaskell.Monad (Leniency(Strict))
import HsToRocq.Edits.Parser (parseEditList, prettyParseError, runParser)
import HsToRocq.Edits.Types
import HsToRocq.Rocq.Gallina (RocqVersion(Rocq_9_0))
import HsToRocq.Rocq.Gallina.Util (qualidToIdent)
import Options.Applicative (execParser)
import System.Exit (die)

baseEdits :: FilePath
baseEdits = "../../base/edits"

-- This is the resolved contents of base/edits at 5e6a7bdd.
baseSHA256 :: String
baseSHA256 = "ad3e975926fed9abc752ef614ca34f43b056d49f4f612831764602f293845d68"

listed :: [FilePath]
listed = [baseEdits, "edits", "reader.edits", "tests/allowed.edits"]
      ++ map ("tests/vc1/" ++) ["structural", "direct", "in", "except", "nested", "rewrite", "malformed"]

-- Symbol literals are Haskell strings in the model. Its indexed singleton
-- comparison returns equality or a refutation, as required by upstream At.
-- Keep namespace, source, and target together: SSymbol names both a type
-- and its constructor, whose Rocq names differ.
symbolMappings :: [(HsNamespace, String, String)]
symbolMappings =
  [ (TypeNS, "GHC.Types.Symbol", "Parkour.Symbol.Symbol")
  , (TypeNS, "GHC.Internal.TypeLits.KnownSymbol", "Parkour.Symbol.KnownSymbol")
  , (TypeNS, "GHC.Internal.TypeLits.SSymbol", "Parkour.Symbol.SSymbol")
  , (ExprNS, "GHC.Internal.TypeLits.SSymbol", "Parkour.Symbol.MkSSymbol")
  , (ExprNS, "GHC.Internal.TypeLits.symbolVal", "Parkour.Symbol.symbolVal")
  , (ExprNS, "Data.Singletons.Decide.Proved", "Parkour.Symbol.Proved")
  , (ExprNS, "Data.Singletons.Decide.Disproved", "Parkour.Symbol.Disproved")
    -- The edit parser encodes the Haskell operator (%~) in Qualid.
  , (ExprNS, "Data.Singletons.Decide.op_zvz7eU__", "Parkour.Symbol.decide")
    -- Homogeneous :~: and its eliminators use ordinary Rocq equality.
  , (TypeNS, "GHC.Internal.Data.Type.Equality.op_ZCz7eUZC__", "Parkour.Symbol.Equal")
  , (ExprNS, "GHC.Internal.Data.Type.Equality.Refl", "Parkour.Symbol.Refl")
  , (ExprNS, "GHC.Internal.Data.Type.Equality.sym", "eq_sym")
  , (ExprNS, "GHC.Internal.Data.Type.Equality.trans", "eq_trans")
  ]

-- Only the pure TH constructors used to *describe* upstream mkLoc.
-- Expansion of Main's splices still happens in GHC against the real library.
thMappings :: [(HsNamespace, String, String)]
thMappings =
  [ (ns, "Language.Haskell.TH.Syntax." ++ n, "Parkour.TH." ++ n)
  | (ns, names) <- [(TypeNS, ["Q", "Dec"]),
                    (ExprNS, ["mkName", "SigD", "AppT", "ConT", "LitT", "StrTyLit",
                              "ValD", "VarP", "NormalB", "ConE"])]
  , n <- names
  ]

codecMappings :: [(HsNamespace, String, String)]
codecMappings = [ (TypeNS, "GHC.Internal.Show.Show", "Parkour.Codec.Show")
                , (TypeNS, "GHC.Internal.Read.Read", "Parkour.Codec.Read") ]

-- Main's primitive effects and the backend configuration. The protocol
-- and runChoreography are absent: their bodies must come from translation.
runtimeMappings :: [(HsNamespace, String, String)]
runtimeMappings =
  [ (TypeNS, "GHC.Types.IO", "Parkour.Runtime.IO")
  , (TypeNS, "GHC.Internal.Conc.Sync.TVar", "Parkour.Runtime.TVar")
  , (TypeNS, "Choreography.Network.Http.HttpConfig", "Parkour.Http.HttpConfig")
  , (ExprNS, "GHC.Internal.Conc.Sync.atomically", "Parkour.Runtime.atomically")
  , (ExprNS, "GHC.Internal.Conc.Sync.newTVarIO", "Parkour.Runtime.newTVarIO")
  , (ExprNS, "GHC.Internal.Conc.Sync.readTVar", "Parkour.Runtime.readTVar")
  , (ExprNS, "Control.Concurrent.STM.TVar.modifyTVar", "Parkour.Runtime.modifyTVar")
  , (ExprNS, "Control.Monad.STM.check", "Parkour.Runtime.check")
  , (ExprNS, "GHC.Internal.System.IO.getLine", "Parkour.Runtime.getLine")
  , (ExprNS, "GHC.Internal.System.IO.putStrLn", "Parkour.Runtime.putStrLn")
  , (ExprNS, "GHC.Internal.System.Environment.getArgs", "Parkour.Runtime.getArgs")
  , (ExprNS, "GHC.Internal.Text.Read.read", "Parkour.Runtime.read")
  , (ExprNS, "Choreography.Network.Http.mkHttpConfig", "Parkour.Http.mkHttpConfig")
  ]

libraryMappings :: [(HsNamespace, String, String)]
libraryMappings =
  [ (ExprNS, "Choreography.Choreo2.At", "Choreography.Choreo2.Mk_At")
  , (ExprNS, "Choreography.Choreo2.Epp", "Choreography.Choreo2.Mk_Epp")
  , (TypeNS, "Control.Monad.Reader.Class.MonadReader", "Parkour.Reader.MonadReader")
  , (ExprNS, "Control.Monad.Reader.Class.ask", "Parkour.Reader.ask")
  , (ExprNS, "Control.Monad.Reader.Class.local", "Parkour.Reader.local")
  , (ExprNS, "Control.Monad.Reader.Class.reader", "Parkour.Reader.reader")
  ]

exactKinds :: [T.Text] -> [Edit]
exactKinds = either (error . unlines . map (prettyParseError "built-in kind policy")) id
           . runParser parseEditList . T.unlines

libraryKinds :: [Edit]
libraryKinds = exactKinds
  [ "data kinds Choreography.Location.@ Type, Parkour.Symbol.Symbol"
  , "universe template Control.Monad.Tree.Tree"
  , "universe template Choreography.Location.@"
  , "universe template Choreography.Network.NetworkSig"
  , "universe template Choreography.Network.Backend__Dict"
  , "universe template Choreography.Choreo2.At"
  , "universe template Choreography.Choreo2.Epp"
  , "data kinds Choreography.Network.NetworkSig (Type -> Type), Type"
  , "data kinds Choreography.Choreo2.ChoreoSig (Type -> Type), Parkour.Symbol.Symbol, Type"
  , "data kinds Choreography.Choreo2.At Type, Parkour.Symbol.Symbol, Parkour.Symbol.Symbol"
  ]

-- These kinds are for transformers' declared Haskell2010 language.
readerKinds :: [Edit]
readerKinds = exactKinds
    [ "data kinds Control.Monad.Signatures.Catch Type, Type -> Type, Type"
    , "universe template Parkour.Contravariant.Contravariant__Dict"
    , "universe template Control.Monad.IO.Class.MonadIO__Dict"
    , "universe template Control.Monad.Trans.Class.MonadTrans__Dict"
    , "universe template Control.Monad.Trans.Reader.ReaderT"
    , "data kinds Control.Monad.Signatures.CallCC Type -> Type, Type, Type"
    , "data kinds Control.Monad.Trans.Reader.ReaderT Type, Type -> Type, Type" ]

readerMappings :: [(HsNamespace, String, String)]
readerMappings =
  [ (ExprNS, "Control.Monad.Trans.Reader.ReaderT", "Control.Monad.Trans.Reader.Mk_ReaderT")
  , (TypeNS, "GHC.Types.IO", "Parkour.Runtime.IO")
  , (ExprNS, "GHC.Prim.leftSection", "Parkour.Functions.leftSection")
  , (TypeNS, "Data.Functor.Contravariant.Contravariant", "Parkour.Contravariant.Contravariant")
  , (ExprNS, "Data.Functor.Contravariant.contramap", "Parkour.Contravariant.contramap")
  , (ExprNS, "Data.Functor.Contravariant.op_zgzd__", "Parkour.Contravariant.op_zgzd__")
  ]

checkFile :: FilePath -> IO ()
checkFile file = do
  unless (file `elem` listed) $ die $ "VC1: unlisted edits input: " ++ file
  bytes <- BS.readFile file
  text <- either (die . ((file ++ ": ") ++) . show) pure $ T.decodeUtf8' bytes
  directives <- either (die . unlines . map (prettyParseError file)) pure $
                  runParser parseEditList text
  mapM_ (inspect []) directives
  unless (file /= baseEdits || show (hash bytes :: Digest SHA256) == baseSHA256) $
    die $ "VC1: " ++ file ++ ": unexpected SHA-256"
 where
  name = T.unpack . qualidToIdent
  inspect scope edit = case edit of
    InEdit q e -> inspect (scope ++ ["in " ++ name q]) e
    ExceptInEdit qs e -> inspect (scope ++ ["except in " ++ intercalate ", " (map name $ NE.toList qs)]) e
    RedefinitionEdit{} -> reject
    _ | file == baseEdits -> pure ()
    _ | file == "reader.edits", null scope, edit `elem` readerKinds -> pure ()
    _ | file == "edits", null scope, edit `elem` libraryKinds -> pure ()
    SkipEdit q | file == "edits", null scope, name q == "Choreography.Location.unwrap" -> pure ()
    OrderEdit{} -> pure ()
    DataTypeArgumentsEdit{} -> pure ()
    EquationsEdit{} -> pure ()
    RenameEdit (NamespacedIdent ns src) dst
      | file == "edits", null scope
      , (ns, name src, name dst) `elem`
        (symbolMappings ++ thMappings ++ codecMappings ++ runtimeMappings ++ libraryMappings) -> pure ()
    RenameEdit (NamespacedIdent ns src) dst
      | file == "reader.edits", null scope
      , (ns, name src, name dst) `elem` readerMappings -> pure ()
    _ -> reject
   where
    reject = die $ "VC1: " ++ file ++ " [" ++ intercalate " > " ("global" : scope)
                ++ "]: forbidden " ++ show edit

main :: IO ()
main = do
  setLocaleEncoding utf8
  args <- execParser argParserInfo
  unless (translationLeniencyArg args == Strict && rocqVersionArg args == Rocq_9_0) $
    die "VC1: expected strict translation for Rocq 9.0"
  forM_ (preambleFileArg args) $ \f -> do
    unless (f `elem` ["module-edits/Choreography/Location/preamble.v",
                      "module-edits/Choreography2/preamble.v"]) $
      die $ "VC1: unlisted preamble: " ++ f
    contents <- BS.readFile f
    unless (contents == "Require GHC.Base.\nImport GHC.Base.Notations.\n") $
      die $ "VC1: unexpected preamble contents: " ++ f
  forM_ (midambleFileArg args) $ \f -> die $ "VC1: forbidden midamble: " ++ f
  mapM_ checkFile (editsFilesArgs args)
