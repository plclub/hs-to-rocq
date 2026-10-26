{-# LANGUAGE OverloadedStrings #-}

-- Run against the installed library after stack build:
-- stack exec -- runghc -package=hs-to-rocq examples/tests/checks/RocqVersion.hs
module Main (main) where

import Control.Monad (unless)
import Data.Data (Data)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T
import System.Exit (die)

import HsToRocq.Rocq.Gallina
import HsToRocq.Rocq.Gallina.Util
import HsToRocq.Rocq.Preamble (staticPreamble)
import HsToRocq.Rocq.Pretty (textP)

assertEqual :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEqual label expected actual = unless (expected == actual) $
  die (label ++ "\n  expected: " ++ show expected ++ "\n  actual:   " ++ show actual)

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
  , ("already target Import", ModuleImport Import ("Corelib.Init.Decimal.Little" :| []),
      ModuleImport Import ("Corelib.Init.Decimal.Little" :| []), "Import Corelib.Init.Decimal.Little.")
  , ("already target Require", Require Nothing (Just Import) ("Stdlib.Program.WfExtensionality" :| []),
      Require Nothing (Just Import) ("Stdlib.Program.WfExtensionality" :| []),
      "Require Import Stdlib.Program.WfExtensionality.")
  ]

proofCases :: [(String, Proof, Proof)]
proofCases =
  [ (label, ending oldTactics, ending newTactics)
  | (label, ending) <-
      [("Qed proof tactics", ProofQed), ("Defined proof tactics", ProofDefined),
       ("Admitted proof tactics", ProofAdmitted)]
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
  , ("bare From Coq text (dotted-path rewriter limitation)", "From Coq Require Import Init.Datatypes Program.Wf.",
      "From Coq Require Import Init.Datatypes Program.Wf.")
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
  | prefix <- ["My", "1", "_", "'", "Other.", "\x03bb"]
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
      nonCodeAST = (nonCodeText, Comment nonCodeText,
        [String nonCodeText, HsString nonCodeText], StringPat nonCodeText, Bare nonCodeText)
      checks = concatMap (\(label, input, expected) -> checkAST label input expected) qualidCases
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
