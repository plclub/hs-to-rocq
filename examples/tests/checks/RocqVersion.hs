{-# LANGUAGE OverloadedStrings #-}

-- Run against the installed library after stack build:
-- stack exec -- runghc -package=hs-to-rocq examples/tests/checks/RocqVersion.hs
module Main (main) where

import Control.Monad (unless)
import Data.Data (Data)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T
import qualified Options.Applicative as OA
import System.Exit (die)

import HsToRocq.CLI (ProgramArgs(..), argParserInfo)
import HsToRocq.Rocq.Gallina
import HsToRocq.Rocq.Gallina.Util
import HsToRocq.Rocq.Preamble (staticPreamble)
import HsToRocq.Rocq.Pretty (textP)

assertEqual :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEqual label expected actual = unless (expected == actual) $
  die (label ++ "\n  expected: " ++ show expected ++ "\n  actual:   " ++ show actual)

checkCLI :: String -> [String] -> (RocqVersion, Maybe FilePath, [FilePath]) -> IO ()
checkCLI label input expected = case OA.execParserPure OA.defaultPrefs argParserInfo input of
  OA.Success args -> assertEqual label expected
    (rocqVersionArg args, outputFileArg args, directInputFilesArgs args)
  OA.Failure failure -> die (label ++ "\n" ++ fst (OA.renderFailure failure "hs-to-rocq"))
  OA.CompletionInvoked _ -> die (label ++ "\n  unexpected completion request")

checkCLIRejected :: String -> [String] -> IO ()
checkCLIRejected label input = case OA.execParserPure OA.defaultPrefs argParserInfo input of
  OA.Failure _ -> pure ()
  OA.Success args -> die (label ++ "\n  unexpectedly accepted: " ++ show args)
  OA.CompletionInvoked _ -> die (label ++ "\n  unexpected completion request")

cliChecks :: [IO ()]
cliChecks =
  [ checkCLI "CLI defaults to Coq 8.20" [] (Rocq_8_20, Nothing, [])
  , checkCLI "CLI default preserves output and input files"
      ["-o", "output", "Input.hs"] (Rocq_8_20, Just "output", ["Input.hs"])
  , checkCLI "CLI explicit Coq 8.20" ["--target-version", "8.20", "Input.hs"]
      (Rocq_8_20, Nothing, ["Input.hs"])
  , checkCLI "CLI Rocq 9.0 preserves output and multiple input files"
      ["--target-version", "9.0", "-o", "output directory", "Input.hs", "Other Input.hs"]
      (Rocq_9_0, Just "output directory", ["Input.hs", "Other Input.hs"])
  , checkCLI "CLI equals syntax after an input file"
      ["Input.hs", "--target-version=9.0", "--output=output"]
      (Rocq_9_0, Just "output", ["Input.hs"])
  ] ++
  [ checkCLIRejected ("CLI rejects target version " ++ show version)
      ["--target-version=" ++ version, "Input.hs"]
  | version <- ["unknown", "8.19", "9.2", "9.0.1", ""]
  ] ++
  [ checkCLIRejected "CLI rejects a missing target version" ["--target-version"]
  , checkCLIRejected "CLI rejects a missing target version before another option"
      ["--target-version", "-o", "output", "Input.hs"]
  ]

checkAST :: (Data a, Eq a, Show a) => String -> a -> a -> [IO ()]
checkAST label input expected =
  [ assertEqual (label ++ " (AST)") expected (coqToStdlib input)
  , assertEqual (label ++ " (9.0 dispatch)") expected (rewriteASTFor Rocq_9_0 input)
  , assertEqual (label ++ " (8.20 identity)") input (rewriteASTFor Rocq_8_20 input)
  , assertEqual (label ++ " (AST idempotence)") expected
      (rewriteASTFor Rocq_9_0 (rewriteASTFor Rocq_9_0 input))
  ]

qualidCases :: [(String, Qualid, Qualid)]
qualidCases =
  [ ("exact shim", Qualified "Coq.Init.Decimal" "Nil",
      Qualified "Corelib.Init.Decimal" "Nil")
  , ("nested shim", Qualified "Coq.Init.Decimal.Little" "succ",
      Qualified "Corelib.Init.Decimal.Little" "succ")
  , ("deeply nested shim", Qualified "Coq.Init.Decimal.Little.More" "value",
      Qualified "Corelib.Init.Decimal.Little.More" "value")
  , ("moved theorem", Qualified "Coq.Program.Wf.WfExtensionality" "fix_sub_eq",
      Qualified "Stdlib.Program.WfExtensionality.WfExtensionality" "fix_sub_eq")
  , ("exact moved module reference", Qualified "Coq.Program.Wf" "WfExtensionality",
      Qualified "Stdlib.Program.WfExtensionality" "WfExtensionality")
  , ("nested moved module reference", Qualified "Coq.Program.Wf.WfExtensionality.Inner" "value",
      Qualified "Stdlib.Program.WfExtensionality.WfExtensionality.Inner" "value")
  , ("dotted moved accessor", Qualified "Coq.Program.Wf" "WfExtensionality.fix_sub_eq",
      Qualified "Stdlib.Program.WfExtensionality" "WfExtensionality.fix_sub_eq")
  , ("Z accessor", unsafeIdentToQualid "Coq.ZArith.BinInt.Z.eqb",
      Qualified "Stdlib.ZArith.BinInt" "Z.eqb")
  , ("N accessor", unsafeIdentToQualid "Coq.NArith.BinNat.N.eqb",
      Qualified "Stdlib.NArith.BinNat" "N.eqb")
  , ("shim Z accessor", unsafeIdentToQualid "Coq.Numbers.BinNums.Z.Z0",
      Qualified "Corelib.Numbers.BinNums" "Z.Z0")
  , ("shim N accessor", unsafeIdentToQualid "Coq.Numbers.BinNums.N.N0",
      Qualified "Corelib.Numbers.BinNums" "N.N0")
  , ("moved Z accessor", unsafeIdentToQualid "Coq.Program.Wf.WfExtensionality.Z.value",
      Qualified "Stdlib.Program.WfExtensionality.WfExtensionality" "Z.value")
  , ("moved N accessor", unsafeIdentToQualid "Coq.Program.Wf.WfExtensionality.N.value",
      Qualified "Stdlib.Program.WfExtensionality.WfExtensionality" "N.value")
  , ("already Corelib", Qualified "Corelib.Init.Decimal.Little" "succ",
      Qualified "Corelib.Init.Decimal.Little" "succ")
  , ("already Stdlib", Qualified "Stdlib.Program.WfExtensionality.WfExtensionality" "fix_sub_eq",
      Qualified "Stdlib.Program.WfExtensionality.WfExtensionality" "fix_sub_eq")
  , ("unrelated namespace", Qualified "Other.Init.Decimal.Little" "succ",
      Qualified "Other.Init.Decimal.Little" "succ")
  , ("embedded namespace", Qualified "Other.Coq.Program.Wf.WfExtensionality" "value",
      Qualified "Other.Coq.Program.Wf.WfExtensionality" "value")
  , ("bare name", Bare "WfExtensionality", Bare "WfExtensionality")
  ] ++ concatMap boundaryCases ["X", "1", "_", "'"]
  where
    boundaryCases suffix =
      [ ("shim boundary " ++ T.unpack suffix,
          Qualified ("Coq.Init.Decimal" <> suffix <> ".Little") "succ",
          Qualified ("Stdlib.Init.Decimal" <> suffix <> ".Little") "succ")
      , ("moved module boundary " ++ T.unpack suffix,
          Qualified ("Coq.Program.Wf.WfExtensionality" <> suffix) "value",
          Qualified ("Corelib.Program.Wf.WfExtensionality" <> suffix) "value")
      , ("moved accessor boundary " ++ T.unpack suffix,
          Qualified "Coq.Program.Wf" ("WfExtensionality" <> suffix),
          Qualified "Corelib.Program.Wf" ("WfExtensionality" <> suffix))
      ]

moduleCases :: [(String, ModuleSentence, ModuleSentence, T.Text)]
moduleCases =
  [ ("Import exact shim", ModuleImport Import ("Coq.Init.Decimal" :| []),
      ModuleImport Import ("Corelib.Init.Decimal" :| []),
      "Import Corelib.Init.Decimal.")
  , ("Import nested shim", ModuleImport Import ("Coq.Init.Decimal.Little" :| []),
      ModuleImport Import ("Corelib.Init.Decimal.Little" :| []),
      "Import Corelib.Init.Decimal.Little.")
  , ("Export moved module", ModuleImport Export ("Coq.Program.Wf.WfExtensionality" :| []),
      ModuleImport Export ("Stdlib.Program.WfExtensionality.WfExtensionality" :| []),
      "Export Stdlib.Program.WfExtensionality.WfExtensionality.")
  , ("Import multiple modules",
      ModuleImport Import ("Coq.Init.Decimal.Little" :| ["Coq.Program.Wf.WfExtensionality"]),
      ModuleImport Import ("Corelib.Init.Decimal.Little" :| ["Stdlib.Program.WfExtensionality.WfExtensionality"]),
      "Import Corelib.Init.Decimal.Little Stdlib.Program.WfExtensionality.WfExtensionality.")
  , ("nested shim assignment", ModuleAssignment "Little" "Coq.Init.Decimal.Little",
      ModuleAssignment "Little" "Corelib.Init.Decimal.Little",
      "Module Little := Corelib.Init.Decimal.Little.")
  , ("moved module assignment", ModuleAssignment "WE" "Coq.Program.Wf.WfExtensionality",
      ModuleAssignment "WE" "Stdlib.Program.WfExtensionality.WfExtensionality",
      "Module WE := Stdlib.Program.WfExtensionality.WfExtensionality.")
  , ("assignment binds its left side", ModuleAssignment "Coq" "Other.Module",
      ModuleAssignment "Coq" "Other.Module", "Module Coq := Other.Module.")
  , ("Require shim library", Require Nothing Nothing ("Coq.Program.Wf" :| []),
      Require Nothing Nothing ("Corelib.Program.Wf" :| []), "Require Corelib.Program.Wf.")
  , ("Require moved library", Require Nothing (Just Import) ("Coq.Program.WfExtensionality" :| []),
      Require Nothing (Just Import) ("Stdlib.Program.WfExtensionality" :| []),
      "Require Import Stdlib.Program.WfExtensionality.")
  , ("Require Export multiple libraries",
      Require Nothing (Just Export) ("Coq.Init.Datatypes" :| ["Coq.Lists.List"]),
      Require Nothing (Just Export) ("Corelib.Init.Datatypes" :| ["Stdlib.Lists.List"]),
      "Require Export Corelib.Init.Datatypes Stdlib.Lists.List.")
  , ("From Coq Require", Require (Just "Coq") (Just Import) ("Init.Datatypes" :| []),
      Require (Just "Stdlib") (Just Import) ("Init.Datatypes" :| []),
      "From Stdlib Require Import Init.Datatypes.")
  , ("From Coq.Program Require Wf", Require (Just "Coq.Program") (Just Import) ("Wf" :| []),
      Require (Just "Stdlib.Program") (Just Import) ("Wf" :| []),
      "From Stdlib.Program Require Import Wf.")
  , ("From Require moved library", Require (Just "Coq.Program") (Just Import) ("WfExtensionality" :| []),
      Require (Just "Stdlib.Program") (Just Import) ("WfExtensionality" :| []),
      "From Stdlib.Program Require Import WfExtensionality.")
  , ("unrelated Require", Require (Just "Other") Nothing ("Library" :| []),
      Require (Just "Other") Nothing ("Library" :| []), "From Other Require Library.")
  , ("From user prefix Require Import preserves relative operands",
      Require (Just "Other") (Just Import) ("Coq.Init.Decimal" :| ["Coq.Program.Wf"]),
      Require (Just "Other") (Just Import) ("Coq.Init.Decimal" :| ["Coq.Program.Wf"]),
      "From Other Require Import Coq.Init.Decimal Coq.Program.Wf.")
  , ("From user prefix Require Export preserves relative operands",
      Require (Just "Other") (Just Export) ("Coq.Init.Decimal" :| []),
      Require (Just "Other") (Just Export) ("Coq.Init.Decimal" :| []),
      "From Other Require Export Coq.Init.Decimal.")
  , ("From user prefix plain Require preserves relative operands",
      Require (Just "Other") Nothing ("Coq.Program.WfExtensionality" :| []),
      Require (Just "Other") Nothing ("Coq.Program.WfExtensionality" :| []),
      "From Other Require Coq.Program.WfExtensionality.")
  , ("From root Coq prefix rewrites only the prefix",
      Require (Just "Coq.Program") (Just Import) ("Coq.Init.Decimal" :| []),
      Require (Just "Stdlib.Program") (Just Import) ("Coq.Init.Decimal" :| []),
      "From Stdlib.Program Require Import Coq.Init.Decimal.")
  , ("From embedded Coq prefix preserves relative operands",
      Require (Just "Other.Coq") (Just Import) ("Coq.Init.Decimal" :| []),
      Require (Just "Other.Coq") (Just Import) ("Coq.Init.Decimal" :| []),
      "From Other.Coq Require Import Coq.Init.Decimal.")
  , ("already target Import", ModuleImport Import ("Corelib.Init.Decimal.Little" :| []),
      ModuleImport Import ("Corelib.Init.Decimal.Little" :| []), "Import Corelib.Init.Decimal.Little.")
  , ("already target Require", Require Nothing (Just Import) ("Stdlib.Program.WfExtensionality" :| []),
      Require Nothing (Just Import) ("Stdlib.Program.WfExtensionality" :| []),
      "Require Import Stdlib.Program.WfExtensionality.")
  ]

fieldTacticCases :: [(String, T.Text, T.Text)]
fieldTacticCases =
  [ ("spaced FIELD tokens",
      "pose proof @Coq .Program.Wf .WfExtensionality.fix_sub_eq_ext as H; pose (\"Coq .Program.Wf\") as path; exact Coq .Init.Logic.I",
      "pose proof @Stdlib .Program.WfExtensionality .WfExtensionality.fix_sub_eq_ext as H; pose (\"Coq .Program.Wf\") as path; exact Corelib .Init.Logic.I")
  , ("commented FIELD tokens",
      "pose proof @Coq(* \"Coq.Program.Wf\" (* nested *) *) .Program .Wf .WfExtensionality .fix_sub_eq_ext as H; exact Coq(* \"Coq.Init.Logic\" *) .Init.Logic.I",
      "pose proof @Stdlib(* \"Coq.Program.Wf\" (* nested *) *) .Program .WfExtensionality .WfExtensionality .fix_sub_eq_ext as H; exact Corelib(* \"Coq.Init.Logic\" *) .Init.Logic.I")
  ]

proofCases :: [(String, Proof, Proof)]
proofCases =
  [ (label, ending oldTactics, ending newTactics)
  | (label, ending) <-
      [("Qed proof tactics", ProofQed), ("Defined proof tactics", ProofDefined),
       ("Admitted proof tactics", ProofAdmitted)]
  ] ++
  [ (endingLabel ++ " with " ++ label, ending oldTactics, ending newTactics)
  | (endingLabel, ending) <-
      [("Qed", ProofQed), ("Defined", ProofDefined), ("Admitted", ProofAdmitted)]
  , (label, oldTactics, newTactics) <- fieldTacticCases
  ] ++
  [ ("empty admitted proof", ProofAdmitted "", ProofAdmitted "")
  , ("proof tactics preserve user qualifiers",
      ProofQed "pose proof MyCoq.Init.Decimal.Little.add as H; pose proof Other.Coq.Program.Wf.WfExtensionality.add as Hwf; exact Coq.Init.Logic.I.",
      ProofQed "pose proof MyCoq.Init.Decimal.Little.add as H; pose proof Other.Coq.Program.Wf.WfExtensionality.add as Hwf; exact Corelib.Init.Logic.I.")
  ]
  where
    oldTactics = T.unlines
      [ "pose proof Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext as H."
      , "pose proof Coq.Arith.PeanoNat.Nat.add_comm as Hcomm."
      , "pose (\"Coq.Init.Decimal\") as path."
      , "exact Coq.Init.Logic.I."
      ]
    newTactics = T.unlines
      [ "pose proof Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext as H."
      , "pose proof Stdlib.Arith.PeanoNat.Nat.add_comm as Hcomm."
      , "pose (\"Coq.Init.Decimal\") as path."
      , "exact Corelib.Init.Logic.I."
      ]

programCases :: [(String, Sentence, Sentence)]
programCases =
  [ ("Program obligation tactics",
      ProgramSentence oldDefinition
        (Just "pose proof Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext as H; exact I"),
      ProgramSentence newDefinition
        (Just "pose proof Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext as H; exact I"))
  , ("Program obligation standard namespaces",
      ProgramSentence oldDefinition
        (Just "pose proof Coq.Arith.PeanoNat.Nat.add_comm as H; exact Coq.Init.Logic.I"),
      ProgramSentence newDefinition
        (Just "pose proof Stdlib.Arith.PeanoNat.Nat.add_comm as H; exact Corelib.Init.Logic.I"))
  , ("Program obligation tactics preserve user qualifiers",
      ProgramSentence oldDefinition
        (Just "pose proof MyCoq.add as H; pose proof Other.Coq.Init.Decimal.Little.add as Hdec; exact Coq.Init.Logic.I"),
      ProgramSentence newDefinition
        (Just "pose proof MyCoq.add as H; pose proof Other.Coq.Init.Decimal.Little.add as Hdec; exact Corelib.Init.Logic.I"))
  , ("Program obligation tactics preserve string literals",
      ProgramSentence oldDefinition
        (Just "pose (\"Coq.Init.Decimal\") as path; exact Coq.Init.Logic.I"),
      ProgramSentence newDefinition
        (Just "pose (\"Coq.Init.Decimal\") as path; exact Corelib.Init.Logic.I"))
  , ("Program without obligation tactics",
      ProgramSentence oldDefinition Nothing, ProgramSentence newDefinition Nothing)
  , ("Program admitted obligations",
      ProgramSentence oldDefinition (Just "admit"), ProgramSentence newDefinition (Just "admit"))
  ] ++
  [ ("Program obligation with " ++ label,
      ProgramSentence oldDefinition (Just oldTactics),
      ProgramSentence newDefinition (Just newTactics))
  | (label, oldTactics, newTactics) <- fieldTacticCases
  ]
  where
    oldDefinition = DefinitionSentence (DefinitionDef ExportL (Bare "witness") [] Nothing
      (Qualid (Qualified "Coq.Init.Logic" "I")) NotExistingClass)
    newDefinition = DefinitionSentence (DefinitionDef ExportL (Bare "witness") [] Nothing
      (Qualid (Qualified "Corelib.Init.Logic" "I")) NotExistingClass)

textCases :: [(String, T.Text, T.Text)]
textCases =
  [ ("exact shim text", "Coq.Init.Decimal", "Corelib.Init.Decimal")
  , ("nested shim text", "Coq.Init.Decimal.Little.succ", "Corelib.Init.Decimal.Little.succ")
  , ("quoted string stays unchanged while code reference rewrites",
      "exact (eq_refl \"Coq.Init.Decimal\"); pose proof Coq.Init.Logic.I.",
      "exact (eq_refl \"Coq.Init.Decimal\"); pose proof Corelib.Init.Logic.I.")
  , ("doubled quotes keep paths inside the literal",
      "pose (\"before \"\"Coq.Init.Decimal\"\" after\") as path; exact Coq.Init.Logic.I.",
      "pose (\"before \"\"Coq.Init.Decimal\"\" after\") as path; exact Corelib.Init.Logic.I.")
  , ("empty string does not hide the following code reference",
      "pose (\"\") as path; exact Coq.Init.Logic.I.",
      "pose (\"\") as path; exact Corelib.Init.Logic.I.")
  , ("multiline string preserves paths and comment delimiters",
      "pose (\"Coq.Init.Decimal\n(* Coq.Program.Wf *)\") as path; exact Coq.Init.Logic.I.",
      "pose (\"Coq.Init.Decimal\n(* Coq.Program.Wf *)\") as path; exact Corelib.Init.Logic.I.")
  , ("backslash does not escape a Rocq closing quote",
      "pose (\"Coq.Init.Decimal\\\") as path; exact Coq.Init.Logic.I.",
      "pose (\"Coq.Init.Decimal\\\") as path; exact Corelib.Init.Logic.I.")
  , ("unterminated string remains unchanged after a code reference",
      "Coq.Init.Logic.I \"Coq.Init.Decimal",
      "Corelib.Init.Logic.I \"Coq.Init.Decimal")
  , ("moved theorem text", "Coq.Program.Wf.WfExtensionality.fix_sub_eq",
      "Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq")
  , ("moved theorem across spaced FIELD tokens",
      "Check Coq.Program.Wf .WfExtensionality.fix_sub_eq_ext.",
      "Check Stdlib.Program.WfExtensionality .WfExtensionality.fix_sub_eq_ext.")
  , ("moved theorem preserves every FIELD separator",
      "Check Coq .Program\n .Wf(* \"Coq.Program.Wf\" (* nested *) *) .WfExtensionality\t.fix_sub_eq_ext.",
      "Check Stdlib .Program\n .WfExtensionality(* \"Coq.Program.Wf\" (* nested *) *) .WfExtensionality\t.fix_sub_eq_ext.")
  , ("shim and generic paths match across trivia",
      "Check Coq .Init(* shim *) .Logic.I. Check Coq .Arith.PeanoNat .Nat.add_comm.",
      "Check Corelib .Init(* shim *) .Logic.I. Check Stdlib .Arith.PeanoNat .Nat.add_comm.")
  , ("FIELD lookahead preserves literals and trailing comments",
      "pose (\"Coq.Program.Wf .WfExtensionality\") as path; exact Coq(* \"Coq.Init.Logic\" *) .Init.Logic.I (* trailing *).",
      "pose (\"Coq.Program.Wf .WfExtensionality\") as path; exact Corelib(* \"Coq.Init.Logic\" *) .Init.Logic.I (* trailing *).")
  , ("FIELD lookahead leaves command dots separate",
      "Check Coq.Init.Logic.I (* trailing *) .\nCheck Coq.Init.Logic.I.",
      "Check Corelib.Init.Logic.I (* trailing *) .\nCheck Corelib.Init.Logic.I.")
  , ("FIELD lookahead leaves dot notation separate",
      "Check Coq.Init.Datatypes.O (* notation *) .....Coq.Init.Logic.I.",
      "Check Corelib.Init.Datatypes.O (* notation *) .....Corelib.Init.Logic.I.")
  , ("spaced and commented user paths stay unchanged",
      "Check Other .Coq .Program.Wf .WfExtensionality.add. Check Other(* \"Coq.Init.Decimal\" *) .Coq.Init.Decimal.Little.add.",
      "Check Other .Coq .Program.Wf .WfExtensionality.add. Check Other(* \"Coq.Init.Decimal\" *) .Coq.Init.Decimal.Little.add.")
  , ("exact moved module text", "Coq.Program.Wf.WfExtensionality",
      "Stdlib.Program.WfExtensionality.WfExtensionality")
  , ("Require text without injection", "Require Import Coq.Program.Wf.\n",
      "Require Import Corelib.Program.Wf.\n")
  , ("indented Require text", "  Require Import Coq.Program.Wf.  \n",
      "  Require Import Corelib.Program.Wf.  \n")
  , ("Require multiple text", "Require Export Coq.Program.Wf Coq.Init.Datatypes.",
      "Require Export Corelib.Program.Wf Corelib.Init.Datatypes.")
  , ("Require moved library text", "Require Import Coq.Program.WfExtensionality.",
      "Require Import Stdlib.Program.WfExtensionality.")
  , ("From Require and moved reference text",
      "From Coq.Program Require Import Wf.\nCheck Coq.Program.Wf.WfExtensionality.fix_sub_eq.\n",
      "From Stdlib.Program Require Import Wf.\nCheck Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq.\n")
  , ("bare From Coq prefix", "From Coq Require Import Init.Datatypes Program.Wf.",
      "From Stdlib Require Import Init.Datatypes Program.Wf.")
  , ("bare From Coq preserves relative operands",
      "From Coq Require Coq.Init.Decimal Coq.Program.Wf.",
      "From Stdlib Require Coq.Init.Decimal Coq.Program.Wf.")
  , ("bare From Coq Export releases following root references",
      "From Coq Require Export Init.Datatypes.\nCheck Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.",
      "From Stdlib Require Export Init.Datatypes.\nCheck Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext.")
  , ("bare From Coq handles comments and newlines",
      "From(* outer (* From Coq Require Bogus. *) *)\nCoq(* prefix . *)\nRequire(* operands *)Import Init.Datatypes Coq.Program.Wf.\nCheck Coq.Init.Logic.I.",
      "From(* outer (* From Coq Require Bogus. *) *)\nStdlib(* prefix . *)\nRequire(* operands *)Import Init.Datatypes Coq.Program.Wf.\nCheck Corelib.Init.Logic.I.")
  , ("bare From Coq in comments and strings stays unchanged",
      "(* From Coq Require Import Init.Datatypes. *)\npose (\"From Coq Require Import Init.Datatypes.\") as command; exact Coq.Init.Logic.I.",
      "(* From Coq Require Import Init.Datatypes. *)\npose (\"From Coq Require Import Init.Datatypes.\") as command; exact Corelib.Init.Logic.I.")
  , ("bare Coq names and module alias stay unchanged",
      "Module Coq := Other.Module.\nCheck Coq.\nCheck (Coq).\nCheck Coq.Init.Logic.I.",
      "Module Coq := Other.Module.\nCheck Coq.\nCheck (Coq).\nCheck Corelib.Init.Logic.I.")
  , ("bare From Coq matching preserves user prefixes and relative operands",
      "From CoqX Require Import Coq.Init.Decimal. From Other.Coq Require Coq.Program.Wf.\nCheck Coq.Init.Logic.I.",
      "From CoqX Require Import Coq.Init.Decimal. From Other.Coq Require Coq.Program.Wf.\nCheck Corelib.Init.Logic.I.")
  , ("From user prefix Require Import preserves relative operands",
      "From Other Require Import Coq.Init.Decimal Coq.Program.Wf.",
      "From Other Require Import Coq.Init.Decimal Coq.Program.Wf.")
  , ("From user prefix Require Export preserves relative operands",
      "From Other Require Export Coq.Init.Decimal.",
      "From Other Require Export Coq.Init.Decimal.")
  , ("From user prefix plain Require preserves relative operands",
      "From Other Require Coq.Program.WfExtensionality.",
      "From Other Require Coq.Program.WfExtensionality.")
  , ("From root Coq prefix rewrites only the prefix",
      "From Coq.Program Require Import Coq.Init.Decimal Wf.",
      "From Stdlib.Program Require Import Coq.Init.Decimal Wf.")
  , ("From embedded Coq prefix preserves relative operands",
      "From Other.Coq Require Import Coq.Init.Decimal.",
      "From Other.Coq Require Import Coq.Init.Decimal.")
  , ("From spaced standard prefix rewrites with its separators",
      "From Coq .Program Require Wf. From Coq .Init Require Import Datatypes.",
      "From Stdlib .Program Require Wf. From Stdlib .Init Require Import Datatypes.")
  , ("From commented standard prefix preserves comment contents",
      "From Coq(* \"Coq.Program.Wf\" (* nested *) *) .Program Require Import Wf.",
      "From Stdlib(* \"Coq.Program.Wf\" (* nested *) *) .Program Require Import Wf.")
  , ("From spaced user prefix protects relative operands",
      "From Other .Prefix Require Import Coq.Init.Decimal. Check Coq.Init.Logic.I.",
      "From Other .Prefix Require Import Coq.Init.Decimal. Check Corelib.Init.Logic.I.")
  , ("From commented user prefix protects spaced relative operands",
      "From Other(* \"Coq.Init.Decimal\" (* nested *) *) .Prefix Require Export Coq .Init.Decimal. Check Coq.Init.Logic.I.",
      "From Other(* \"Coq.Init.Decimal\" (* nested *) *) .Prefix Require Export Coq .Init.Decimal. Check Corelib.Init.Logic.I.")
  , ("From imports preserve whitespace and release following root references",
      "Check Coq.Init.Logic.I.\n  From\tOther\nRequire\nImport\n Coq.Init.Decimal\n Coq.Program.Wf.\nCheck Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.",
      "Check Corelib.Init.Logic.I.\n  From\tOther\nRequire\nImport\n Coq.Init.Decimal\n Coq.Program.Wf.\nCheck Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext.")
  , ("From imports recognize comments as whitespace without ending at comment dots",
      "From(* outer (* From Coq.Program Require Wf. *) *)Other(* prefix *)Require(* list *)Import Coq.Init.Decimal(* . *)Coq.Program.Wf.\nCheck Coq.Init.Logic.I.",
      "From(* outer (* From Coq.Program Require Wf. *) *)Other(* prefix *)Require(* list *)Import Coq.Init.Decimal(* . *)Coq.Program.Wf.\nCheck Corelib.Init.Logic.I.")
  , ("From in comments does not suppress following code rewrites",
      "(* From Other Require Import Coq.Init.Decimal *) Check Coq.Init.Logic.I.",
      "(* From Other Require Import Coq.Init.Decimal *) Check Corelib.Init.Logic.I.")
  , ("From in strings does not suppress following code rewrites",
      "pose (\"From Other Require Import Coq.Init.Decimal\") as command; exact Coq.Init.Logic.I.",
      "pose (\"From Other Require Import Coq.Init.Decimal\") as command; exact Corelib.Init.Logic.I.")
  , ("quotes in comments do not expose a false From command",
      "(* \"*) From Other Require Import Coq.Init.Decimal\" *) Check Coq.Init.Logic.I.",
      "(* \"*) From Other Require Import Coq.Init.Decimal\" *) Check Corelib.Init.Logic.I.")
  , ("comments do not prevent rewriting the standard From prefix",
      "From (* \"From Other Require Import\" *) Coq.Program (* prefix *) Require Export Wf.\nCheck Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.",
      "From (* \"From Other Require Import\" *) Stdlib.Program (* prefix *) Require Export Wf.\nCheck Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext.")
  , ("successive From and root Require commands keep their own roots",
      "From Other Require Coq.Init.Decimal.(* separator *)From Coq.Program Require Wf. Require Coq.Init.Logic.",
      "From Other Require Coq.Init.Decimal.(* separator *)From Stdlib.Program Require Wf. Require Corelib.Init.Logic.")
  , ("From must be a whole token",
      "Check Other.From. Check FromOther. Require Coq.Init.Decimal.",
      "Check Other.From. Check FromOther. Require Corelib.Init.Decimal.")
  , ("Import nested module text", "Import Coq.Init.Decimal.Little.",
      "Import Corelib.Init.Decimal.Little.")
  , ("Import moved module text", "Import Coq.Program.Wf.WfExtensionality.",
      "Import Stdlib.Program.WfExtensionality.WfExtensionality.")
  , ("module assignment text", "Module WE := Coq.Program.Wf.WfExtensionality.",
      "Module WE := Stdlib.Program.WfExtensionality.WfExtensionality.")
  , ("user module alias text", "Module MyCoq := Nat.\nCheck MyCoq.add.",
      "Module MyCoq := Nat.\nCheck MyCoq.add.")
  , ("combining marks preserve user qualifiers and module boundaries",
      "A\x1dc0\&Coq.add Coq.Init.Decimal\x1dc0.Little.succ",
      "A\x1dc0\&Coq.add Stdlib.Init.Decimal\x1dc0.Little.succ")
  , ("root path after superscript notation",
      "Check \xb2\&Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.",
      "Check \xb2\&Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext.")
  , ("root paths after subscript notation",
      "Check \x2081\&Coq.Init.Logic.I. Check \x2081\&Coq.Arith.PeanoNat.Nat.add_comm. Check \x2081\&Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.",
      "Check \x2081\&Corelib.Init.Logic.I. Check \x2081\&Stdlib.Arith.PeanoNat.Nat.add_comm. Check \x2081\&Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext.")
  , ("subscripts inside user paths and module components stay together",
      "My\x2081\&Coq.add Other\x2081.Coq.Init.Decimal.Little.add Coq.Init.Decimal\x2081.Little.succ",
      "My\x2081\&Coq.add Other\x2081.Coq.Init.Decimal.Little.add Stdlib.Init.Decimal\x2081.Little.succ")
  , ("root paths after symbolic notation ending in a dot",
      "Check +.Coq.Init.Logic.I. Check +.Coq.Arith.PeanoNat.Nat.add_comm. Check +.Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.",
      "Check +.Corelib.Init.Logic.I. Check +.Stdlib.Arith.PeanoNat.Nat.add_comm. Check +.Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext.")
  , ("multiple dots and punctuation stay in the preceding notation token",
      "Check +..Coq.Init.Logic.I. Check +...Coq.Init.Logic.I. Check ..Coq.Init.Logic.I. Check ....Coq.Init.Logic.I. Check (.Coq.Init.Logic.I. Check \x2295..Coq.Init.Logic.I.",
      "Check +..Corelib.Init.Logic.I. Check +...Corelib.Init.Logic.I. Check ..Corelib.Init.Logic.I. Check ....Corelib.Init.Logic.I. Check (.Corelib.Init.Logic.I. Check \x2295..Corelib.Init.Logic.I.")
  , ("dot-only infix notation separates identifiers, paths and numerals",
      "Check n.....Coq.Init.Logic.I. Check Coq.Init.Datatypes.O.....Coq.Init.Logic.I. Check 0.....Coq.Init.Logic.I.",
      "Check n.....Corelib.Init.Logic.I. Check Corelib.Init.Datatypes.O.....Corelib.Init.Logic.I. Check 0.....Corelib.Init.Logic.I.")
  , ("symbolic notation preserves following user paths",
      "+.My\x2081\&Coq.add +..Other'1.Coq.Init.Decimal.Little.add ..Other\x2081.Coq.Program.Wf.WfExtensionality.add (.Other.Coq.Init.Decimal.Little.add",
      "+.My\x2081\&Coq.add +..Other'1.Coq.Init.Decimal.Little.add ..Other\x2081.Coq.Program.Wf.WfExtensionality.add (.Other.Coq.Init.Decimal.Little.add")
  , ("a single field dot does not expose a root path",
      "r.Coq.Init.Logic.I .Coq.Init.Decimal.Little.add 1.Coq.Init.Logic.I",
      "r.Coq.Init.Logic.I .Coq.Init.Decimal.Little.add 1.Coq.Init.Logic.I")
  , ("notation tokens stop before comments and string literals",
      "+.(* Coq.Init.Logic.I (* nested *) *)Coq.Init.Logic.I +.\"Coq.Init.Logic.I\" Coq.Init.Logic.I",
      "+.(* Coq.Init.Logic.I (* nested *) *)Corelib.Init.Logic.I +.\"Coq.Init.Logic.I\" Corelib.Init.Logic.I")
  , ("spaced ellipsis leaves the following path separate",
      "Check ... Coq.Init.Logic.I.",
      "Check ... Corelib.Init.Logic.I.")
  , ("From commands end before a following notation and root path",
      "From Other Require Coq.Init.Decimal. Check ..Coq.Init.Logic.I. From Coq Require Init.Datatypes. Check +.Coq.Init.Logic.I.",
      "From Other Require Coq.Init.Decimal. Check ..Corelib.Init.Logic.I. From Stdlib Require Init.Datatypes. Check +.Corelib.Init.Logic.I.")
  , ("non-breaking spaces preserve user qualifiers and module boundaries",
      "A\xa0\&Coq.add Coq.Init.Decimal\xa0.Little.succ",
      "A\xa0\&Coq.add Stdlib.Init.Decimal\xa0.Little.succ")
  , ("repeated shim roots after false matches",
      "MyCoq.Init.Decimal Other.Coq.Init.Decimal Coq.Init.Decimal Coq.Init.Decimal",
      "MyCoq.Init.Decimal Other.Coq.Init.Decimal Corelib.Init.Decimal Corelib.Init.Decimal")
  , ("repeated moved roots after false matches",
      "MyCoq.Program.Wf.WfExtensionality Other.Coq.Program.Wf.WfExtensionality Coq.Program.Wf.WfExtensionality Coq.Program.Wf.WfExtensionality",
      "MyCoq.Program.Wf.WfExtensionality Other.Coq.Program.Wf.WfExtensionality Stdlib.Program.WfExtensionality.WfExtensionality Stdlib.Program.WfExtensionality.WfExtensionality")
  , ("repeated generic roots after false matches",
      "MyCoq.Arith.PeanoNat Other.Coq.Arith.PeanoNat Coq.Arith.PeanoNat Coq.Arith.PeanoNat",
      "MyCoq.Arith.PeanoNat Other.Coq.Arith.PeanoNat Stdlib.Arith.PeanoNat Stdlib.Arith.PeanoNat")
  , ("root paths in unspaced parentheses",
      "f(Coq.Init.Logic.I)(Coq.Arith.PeanoNat.Nat.add_comm)(Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext)",
      "f(Corelib.Init.Logic.I)(Stdlib.Arith.PeanoNat.Nat.add_comm)(Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext)")
  , ("explicit root applications",
      "@Coq.Init.Logic.I @Coq.Arith.PeanoNat.Nat.add_comm @Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext",
      "@Corelib.Init.Logic.I @Stdlib.Arith.PeanoNat.Nat.add_comm @Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext")
  , ("root constructor after a pattern apostrophe",
      "let 'Coq.Init.Datatypes.pair a b := p in a",
      "let 'Corelib.Init.Datatypes.pair a b := p in a")
  , ("apostrophes inside user identifiers and qualified paths stay unchanged",
      "Check My'Coq.add. Check Other'.Coq.Init.Decimal.Little.add. Check Coq'.Init.Logic.I.",
      "Check My'Coq.add. Check Other'.Coq.Init.Decimal.Little.add. Check Coq'.Init.Logic.I.")
  , ("root references after adjacent decimal numerals",
      "f 1Coq.Init.Logic.I 2Coq.Arith.PeanoNat.Nat.add_comm 3Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext",
      "f 1Corelib.Init.Logic.I 2Stdlib.Arith.PeanoNat.Nat.add_comm 3Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq_ext")
  , ("numeric tokens preserve underscores and decimal exponents",
      "f 1_000Coq.Init.Logic.I 2e3Coq.Init.Logic.I 3e+4Coq.Init.Logic.I 5e-6Coq.Init.Logic.I",
      "f 1_000Corelib.Init.Logic.I 2e3Corelib.Init.Logic.I 3e+4Corelib.Init.Logic.I 5e-6Corelib.Init.Logic.I")
  , ("root references after decimal fractions and exponents",
      "f 1.5Coq.Init.Logic.I 1.25e+3Coq.Init.Logic.I",
      "f 1.5Corelib.Init.Logic.I 1.25e+3Corelib.Init.Logic.I")
  , ("root references after hexadecimal exponents",
      "f 0x1p2Coq.Init.Logic.I 0x1.fp-2Coq.Init.Logic.I",
      "f 0x1p2Corelib.Init.Logic.I 0x1.fp-2Corelib.Init.Logic.I")
  , ("hexadecimal digits consume C before the following identifier",
      "f 0x1Coq.Init.Logic.I 0XACoq.Init.Logic.I 0x1.Coq.Init.Logic.I",
      "f 0x1Coq.Init.Logic.I 0XACoq.Init.Logic.I 0x1.Coq.Init.Logic.I")
  , ("incomplete numeric prefixes preserve following user identifiers",
      "f 1eCoq.Init.Logic.I 0xGCoq.Init.Logic.I",
      "f 1eCoq.Init.Logic.I 0xGCoq.Init.Logic.I")
  , ("digits inside user identifiers and qualified paths stay unchanged",
      "Check My1Coq.add. Check Other1.Coq.Init.Decimal.Little.add. Check Coq1.Init.Logic.I.",
      "Check My1Coq.add. Check Other1.Coq.Init.Decimal.Little.add. Check Coq1.Init.Logic.I.")
  , ("numeric tokens preserve following user-qualified paths",
      "f 1My1Coq.add 2Other1.Coq.Init.Decimal.Little.add",
      "f 1My1Coq.add 2Other1.Coq.Init.Decimal.Little.add")
  , ("generic replacement preserves nested Coq component", "Coq.Coq.X", "Stdlib.Coq.X")
  , ("shim replacement preserves nested Coq component",
      "Coq.Init.Decimal.Coq.Init.Logic.I", "Corelib.Init.Decimal.Coq.Init.Logic.I")
  , ("moved replacement preserves nested Coq component",
      "Coq.Program.Wf.WfExtensionality.Coq.Init.Decimal.Little.succ",
      "Stdlib.Program.WfExtensionality.WfExtensionality.Coq.Init.Decimal.Little.succ")
  , ("rejected shim prefix preserves embedded identifier context",
      "Coq.Init.DecimalCoq.Init.Logic.I", "Stdlib.Init.DecimalCoq.Init.Logic.I")
  , ("rejected root preserves nested context before a real root",
      "MyCoq.Coq.Init.Decimal.Little.succ(Coq.Init.Logic.I)",
      "MyCoq.Coq.Init.Decimal.Little.succ(Corelib.Init.Logic.I)")
  , ("target namespaces preserve nested Coq components",
      "Stdlib.Coq.Init.Decimal.Little.succ Corelib.Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext",
      "Stdlib.Coq.Init.Decimal.Little.succ Corelib.Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext")
  , ("already target text",
      "Corelib.Init.Decimal.Little.succ Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq",
      "Corelib.Init.Decimal.Little.succ Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq")
  , ("unrelated text", "Other.Init.Decimal.Little.succ CoqX.Program.Wf.value",
      "Other.Init.Decimal.Little.succ CoqX.Program.Wf.value")
  , ("empty text", "", "")
  ] ++ concatMap boundaryCases ["X", "1", "_", "'"] ++
  [ ("non-root text " ++ T.unpack (prefix <> path), prefix <> path, prefix <> path)
  | prefix <- ["My", "My1", "_", "My'", "Other.", "\x03bb"]
  , path <- ["Coq.Init.Decimal.Little.succ",
             "Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext",
             "Coq.Arith.PeanoNat.Nat.add_comm"]
  ]
  where
    boundaryCases suffix =
      [ ("shim text boundary " ++ T.unpack suffix,
          "Coq.Init.Decimal" <> suffix <> ".Little.succ",
          "Stdlib.Init.Decimal" <> suffix <> ".Little.succ")
      , ("moved text boundary " ++ T.unpack suffix,
          "Coq.Program.Wf.WfExtensionality" <> suffix <> ".value",
          "Corelib.Program.Wf.WfExtensionality" <> suffix <> ".value")
      , ("sibling text boundary " ++ T.unpack suffix,
          "Coq.Program.Wf" <> suffix <> ".value",
          "Stdlib.Program.Wf" <> suffix <> ".value")
      ]

oldHeader :: T.Text
oldHeader = T.unlines
  [ "(* Default settings (from HsToRocq.Rocq.Preamble) *)"
  , ""
  , "Generalizable All Variables."
  , ""
  , "Unset Implicit Arguments."
  , "Set Maximal Implicit Insertion."
  , "Unset Strict Implicit."
  , "Unset Printing Implicit Defensive."
  , ""
  , "Require Coq.Program.Tactics."
  , "Require Coq.Program.Wf."
  ]

main :: IO ()
main = do
  let movedRequire = "Require Import Stdlib.Program.WfExtensionality."
      assertion = Assertion Theorem (Bare "witness") [] (Qualid (Bare "True"))
      nonCodeText = "Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext"
      fromText = "From Other Require Import Coq.Init.Decimal."
      bareFromText = "From Coq Require Import Init.Datatypes."
      nonCodeAST = (nonCodeText, [Comment nonCodeText, Comment fromText, Comment bareFromText],
        [String nonCodeText, HsString nonCodeText, String fromText, HsString fromText,
         String bareFromText, HsString bareFromText],
        [StringPat nonCodeText, StringPat fromText, StringPat bareFromText], Bare nonCodeText)
      checks = cliChecks
        ++ concatMap (\(label, input, expected) -> checkAST label input expected) qualidCases
        ++ concatMap (\(label, input, expected, printed) ->
             checkAST label input expected ++
             [assertEqual (label ++ " (rendered)") printed (textP (rewriteASTFor Rocq_9_0 input))]) moduleCases
        ++ checkAST "nested AST traversal"
             (App (Qualid (Qualified "Coq.Program.Wf.WfExtensionality" "fix_sub_eq"))
               (PosArg (Qualid (Qualified "Coq.Init.Decimal.Little" "succ")) :| []))
             (App (Qualid (Qualified "Stdlib.Program.WfExtensionality.WfExtensionality" "fix_sub_eq"))
               (PosArg (Qualid (Qualified "Corelib.Init.Decimal.Little" "succ")) :| []))
        ++ checkAST "sentence traversal"
             [ModuleSentence input | (_, input, _, _) <- moduleCases]
             [ModuleSentence expected | (_, _, expected, _) <- moduleCases]
        ++ concatMap (\(label, input, expected) -> checkAST label input expected) proofCases
        ++ concatMap (\(label, input, expected) -> checkAST label input expected) programCases
        ++ checkAST "nested proof and obligation traversal"
             (LocalModuleSentence (LocalModule "Proofs"
               ([AssertionSentence assertion input | (_, input, _) <- proofCases] ++
                [input | (_, input, _) <- programCases])))
             (LocalModuleSentence (LocalModule "Proofs"
               ([AssertionSentence assertion expected | (_, _, expected) <- proofCases] ++
                [expected | (_, _, expected) <- programCases])))
        ++ checkAST "instance proof traversal"
             [InstanceProof (Bare "witness") [] (Qualid (Bare "C")) input | (_, input, _) <- proofCases]
             [InstanceProof (Bare "witness") [] (Qualid (Bare "C")) expected | (_, _, expected) <- proofCases]
        ++ checkAST "non-code AST text stays unchanged" nonCodeAST nonCodeAST
        ++ concatMap (\(label, input, expected) ->
             [ assertEqual (label ++ " (text)") expected (rocq9RewriteText input)
             , assertEqual (label ++ " (9.0 dispatch)") expected (rewriteTextFor Rocq_9_0 input)
             , assertEqual (label ++ " (8.20 identity)") input (rewriteTextFor Rocq_8_20 input)
             , assertEqual (label ++ " (text idempotence)") expected
                 (rewriteTextFor Rocq_9_0 (rewriteTextFor Rocq_9_0 input))
             ]) textCases
        ++ [ assertEqual "exact Coq 8.20 header" oldHeader (staticPreamble Rocq_8_20)
           , assertEqual "exact Rocq 9.0 header"
               (T.replace "Coq." "Stdlib." oldHeader <> movedRequire <> "\n")
               (staticPreamble Rocq_9_0)
           , assertEqual "one moved-library import in Rocq 9 header" 1
               (T.count movedRequire (staticPreamble Rocq_9_0))
           , assertEqual "no moved-library import in Coq 8.20 header" 0
               (T.count movedRequire (staticPreamble Rocq_8_20))
           ]
  sequence_ checks
  putStrLn ("Rocq version checks passed (" ++ show (length checks) ++ " assertions).")
