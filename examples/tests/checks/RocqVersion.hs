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

textCases :: [(String, T.Text, T.Text)]
textCases =
  [ ("exact shim text", "Coq.Init.Decimal", "Corelib.Init.Decimal")
  , ("nested shim text", "Coq.Init.Decimal.Little.succ", "Corelib.Init.Decimal.Little.succ")
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
  , ("already target text",
      "Corelib.Init.Decimal.Little.succ Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq",
      "Corelib.Init.Decimal.Little.succ Stdlib.Program.WfExtensionality.WfExtensionality.fix_sub_eq")
  , ("unrelated text", "Other.Init.Decimal.Little.succ CoqX.Program.Wf.value",
      "Other.Init.Decimal.Little.succ CoqX.Program.Wf.value")
  , ("empty text", "", "")
  ] ++ concatMap boundaryCases ["X", "1", "_", "'"]
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
