{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -Werror #-}

-- Run against the installed library after stack build:
-- stack exec -- runghc -package=hs-to-rocq examples/tests/checks/Edits.hs
module Main (main) where

import Control.Monad (unless)
import Control.Monad.Reader (runReader)
import Data.List (isInfixOf)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import System.Exit (die)

import HsToRocq.ConvertHaskell.Monad
  ( AxiomatizationMode(..), Leniency(Strict), ModuleEnv(..)
  , TranslationTask(..), definitionTask
  )
import HsToRocq.Edits.Parser (parseEditList, parseTerm, prettyParseError)
import HsToRocq.Edits.ParserState (Parser, runParser)
import HsToRocq.Edits.Types
import HsToRocq.Rocq.Gallina
import HsToRocq.Rocq.Gallina.Rewrite (rewrite)
import HsToRocq.Util.GHC.Module (ModuleData(..), mkModuleName)

assertEqual :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEqual label expected actual = unless (expected == actual) $
  die (label ++ "\n  expected: " ++ show expected ++ "\n  actual:   " ++ show actual)

parseWith :: Parser a -> T.Text -> Either String a
parseWith parser = either (Left . unlines . map (prettyParseError "<edits>")) Right
  . runParser parser

parseConfig :: T.Text -> Either String Edits
parseConfig source = parseWith parseEditList source >>= buildEdits

checkBuilt :: (Eq a, Show a) => String -> [Edit] -> a -> (Edits -> a) -> IO ()
checkBuilt label input expected observe =
  checkConfig label (buildEdits input) expected observe

checkConfig :: (Eq a, Show a) => String -> Either String Edits -> a -> (Edits -> a) -> IO ()
checkConfig label input expected observe =
  assertEqual label (Right expected) (observe <$> input)

checkRejected :: Show a => String -> Parser a -> T.Text -> String -> IO ()
checkRejected label parser source expectedMessage = case parseWith parser source of
  Left message -> unless (expectedMessage `isInfixOf` message) $
    die (label ++ "\n  expected diagnostic containing: " ++ show expectedMessage
      ++ "\n  actual: " ++ message)
  Right actual -> die (label ++ "\n  unexpectedly accepted: " ++ show actual)

-- Exhaustive on purpose: a new Edit constructor must extend this inventory.
editKind :: Edit -> String
editKind = \case
  TypeSynonymTypeEdit{} -> "TypeSynonymTypeEdit"
  DataTypeArgumentsEdit{} -> "DataTypeArgumentsEdit"
  TerminationEdit{} -> "TerminationEdit"
  ObligationsEdit{} -> "ObligationsEdit"
  RedefinitionEdit{} -> "RedefinitionEdit"
  AddEdit{} -> "AddEdit"
  SkipEdit{} -> "SkipEdit"
  SkipConstructorEdit{} -> "SkipConstructorEdit"
  SkipClassEdit{} -> "SkipClassEdit"
  SkipMethodEdit{} -> "SkipMethodEdit"
  SkipEquationEdit{} -> "SkipEquationEdit"
  SkipCasePatternEdit{} -> "SkipCasePatternEdit"
  SkipModuleEdit{} -> "SkipModuleEdit"
  ImportModuleEdit{} -> "ImportModuleEdit"
  AxiomatizeModuleEdit{} -> "AxiomatizeModuleEdit"
  AxiomatizeOriginalModuleNameEdit{} -> "AxiomatizeOriginalModuleNameEdit"
  AxiomatizeDefinitionEdit{} -> "AxiomatizeDefinitionEdit"
  UnaxiomatizeDefinitionEdit{} -> "UnaxiomatizeDefinitionEdit"
  HasManualNotationEdit{} -> "HasManualNotationEdit"
  AdditionalScopeEdit{} -> "AdditionalScopeEdit"
  OrderEdit{} -> "OrderEdit"
  RenameEdit{} -> "RenameEdit"
  ClassKindEdit{} -> "ClassKindEdit"
  DataKindEdit{} -> "DataKindEdit"
  PolyKindEdit{} -> "PolyKindEdit"
  DeleteUnusedTypeVariablesEdit{} -> "DeleteUnusedTypeVariablesEdit"
  RewriteEdit{} -> "RewriteEdit"
  CoinductiveEdit{} -> "CoinductiveEdit"
  RenameModuleEdit{} -> "RenameModuleEdit"
  AliasModuleEdit{} -> "AliasModuleEdit"
  SimpleClassEdit{} -> "SimpleClassEdit"
  InlineMutualEdit{} -> "InlineMutualEdit"
  SetTypeEdit{} -> "SetTypeEdit"
  CollapseLetEdit{} -> "CollapseLetEdit"
  InEdit{} -> "InEdit"
  ExceptInEdit{} -> "ExceptInEdit"
  PromoteEdit{} -> "PromoteEdit"
  PolyrecEdit{} -> "PolyrecEdit"
  UniversePolymorphicEdit{} -> "UniversePolymorphicEdit"
  UniverseCumulativeEdit{} -> "UniverseCumulativeEdit"
  EquationsEdit{} -> "EquationsEdit"
  InvariantEdit{} -> "InvariantEdit"

grammarCases :: [(String, T.Text, Edit)]
grammarCases =
  [ ("type synonym result", "type synonym String :-> Type",
      TypeSynonymTypeEdit "String" "Type")
  , ("data parameters and indices",
      "data type arguments Sample.Vector (parameters: a) (indices: n)",
      DataTypeArgumentsEdit (Qualified "Sample" "Vector")
        (DataTypeArguments [Bare "a"] [Bare "n"]))
  , ("named structural argument", "termination Sample.fold {struct xs}",
      TerminationEdit (Qualified "Sample" "fold") (StructOrderTA (StructId_ (Bare "xs"))))
  , ("obligation tactics", "obligations Sample.fold solve 2; (auto || exact @proof)",
      ObligationsEdit (Qualified "Sample" "fold") "solve 2; (auto || exact @proof)")
  , ("redefined definition", "redefine Definition Sample.answer : nat := 42.",
      RedefinitionEdit (RocqDefinitionDef (DefinitionDef Global
        (Qualified "Sample" "answer") [] (Just (Qualid (Bare "nat"))) (Num 42) NotExistingClass)))
  , ("term-phase addition", "add Sample Axiom extra : nat.",
      AddEdit (mkModuleName "Sample") (RocqAxiomDef (Bare "extra", Qualid (Bare "nat"))) PhaseTerm)
  , ("skip value", "skip Sample.hidden", SkipEdit (Qualified "Sample" "hidden"))
  , ("skip constructor", "skip constructor Sample.Hidden",
      SkipConstructorEdit (Qualified "Sample" "Hidden"))
  , ("skip class", "skip class Sample.Class", SkipClassEdit (Qualified "Sample" "Class"))
  , ("skip method", "skip method Sample.Class methodName",
      SkipMethodEdit (Qualified "Sample" "Class") "methodName")
  , ("skip equation preserves argument patterns", "skip equation Sample.choose (Just x) _ 7",
      SkipEquationEdit (Qualified "Sample" "choose")
        (ArgsPat (Bare "Just") [QualidPat (Bare "x")] :| [UnderscorePat, NumPat 7]))
  , ("skip case constructor and as-pattern",
      "skip case pattern Sample.Node _ (Sample.Leaf n) as whole",
      SkipCasePatternEdit (AsPat (ArgsPat (Qualified "Sample" "Node")
        [UnderscorePat, ArgsPat (Qualified "Sample" "Leaf") [QualidPat (Bare "n")]]) (Bare "whole")))
  , ("skip module", "skip module Sample.Internal", SkipModuleEdit (mkModuleName "Sample.Internal"))
  , ("import module", "import module Support.Helpers", ImportModuleEdit (mkModuleName "Support.Helpers"))
  , ("axiomatize module", "axiomatize module Sample", AxiomatizeModuleEdit (mkModuleName "Sample"))
  , ("axiomatize original module name", "axiomatize original module name Original.Sample",
      AxiomatizeOriginalModuleNameEdit (mkModuleName "Original.Sample"))
  , ("axiomatize definition", "axiomatize definition Sample.external",
      AxiomatizeDefinitionEdit (Qualified "Sample" "external"))
  , ("unaxiomatize definition", "unaxiomatize definition Sample.concrete",
      UnaxiomatizeDefinitionEdit (Qualified "Sample" "concrete"))
  , ("manual notation", "manual notation Sample", HasManualNotationEdit (mkModuleName "Sample"))
  , ("value notation scope", "add scope nat_scope for value Sample.plus",
      AdditionalScopeEdit SPValue (Qualified "Sample" "plus") "nat_scope")
  , ("declaration order preserves all names", "order Sample.first Sample.middle Sample.last",
      OrderEdit (Qualified "Sample" "first" :| [Qualified "Sample" "middle", Qualified "Sample" "last"]))
  , ("rename in value namespace", "rename value Sample.old = Target.fresh",
      RenameEdit (NamespacedIdent ExprNS (Qualified "Sample" "old")) (Qualified "Target" "fresh"))
  -- Class kinds has no consumer; its contract here is its parsed syntax only.
  , ("class kinds", "class kinds Sample.Class Type -> Type, Prop",
      ClassKindEdit (Qualified "Sample" "Class")
        (Arrow (Qualid (Bare "Type")) (Qualid (Bare "Type")) :| [Qualid (Bare "Prop")]))
  , ("data kinds", "data kinds Sample.Indexed Type, nat -> Type",
      DataKindEdit (Qualified "Sample" "Indexed")
        (Qualid (Bare "Type") :| [Arrow (Qualid (Bare "nat")) (Qualid (Bare "Type"))]))
  , ("polykinds", "polykinds Sample.Indexed k j",
      PolyKindEdit (Qualified "Sample" "Indexed") ("k" :| ["j"]))
  , ("delete unused type variables", "delete unused type variables Sample.Phantom",
      DeleteUnusedTypeVariablesEdit (Qualified "Sample" "Phantom"))
  , ("rewrite variables and argument order",
      "rewrite forall x y, Sample.apply x y = Sample.pair y x",
      RewriteEdit (Rewrite ["x", "y"]
        (App (Qualid (Qualified "Sample" "apply"))
          (PosArg (Qualid (Bare "x")) :| [PosArg (Qualid (Bare "y"))]))
        (App (Qualid (Qualified "Sample" "pair"))
          (PosArg (Qualid (Bare "y")) :| [PosArg (Qualid (Bare "x"))]))))
  , ("coinductive type", "coinductive Sample.Stream", CoinductiveEdit (Qualified "Sample" "Stream"))
  , ("rename module", "rename module Original.Sample Target.Sample",
      RenameModuleEdit (mkModuleName "Original.Sample") (mkModuleName "Target.Sample"))
  , ("alias module", "alias module Short Original.Sample", AliasModuleEdit "Short" "Original.Sample")
  , ("simple class", "simple class Sample.Class", SimpleClassEdit (Qualified "Sample" "Class"))
  , ("inline mutual", "inline mutual Sample.even", InlineMutualEdit (Qualified "Sample" "even"))
  , ("set type", "set type Sample.items : list nat",
      SetTypeEdit (Qualified "Sample" "items")
        (Just (App (Qualid (Bare "list")) (PosArg (Qualid (Bare "nat")) :| []))))
  , ("collapse let", "collapse let Sample.value", CollapseLetEdit (Qualified "Sample" "value"))
  , ("in definition", "in Sample.outer skip Sample.helper",
      InEdit (Qualified "Sample" "outer") (SkipEdit (Qualified "Sample" "helper")))
  , ("except in definitions", "except in Sample.keep, Sample.alsoKeep termination Sample.loop deferred",
      ExceptInEdit (Qualified "Sample" "keep" :| [Qualified "Sample" "alsoKeep"])
        (TerminationEdit (Qualified "Sample" "loop") Deferred))
  , ("promote", "promote Sample.f", PromoteEdit (Qualified "Sample" "f"))
  , ("polyrec", "polyrec Sample.f", PolyrecEdit (Qualified "Sample" "f"))
  , ("universe polymorphic", "universe polymorphic Sample.Box",
      UniversePolymorphicEdit (Qualified "Sample" "Box"))
  , ("universe cumulative", "universe cumulative Sample.Box",
      UniverseCumulativeEdit (Qualified "Sample" "Box"))
  , ("equations", "equations Sample.loop", EquationsEdit (Qualified "Sample" "loop"))
  , ("invariant carries type, binders, constructor, exports, and predicate",
      "add invariant {module = Sample, qid = Sample.Box, tyVars = [{a : Type}], constructor = Box, useSigmaType = [Sample.pack, Sample.unpack], invariant = Definition Sample.valid (x : Sample.Box a) : Prop := True.}",
      InvariantEdit (mkModuleName "Sample") (Qualified "Sample" "Box")
        [Typed Ungeneralizable Implicit (Ident (Bare "a") :| []) (Qualid (Bare "Type"))]
        "Box" [Qualified "Sample" "pack", Qualified "Sample" "unpack"]
        (RocqDefinitionDef (DefinitionDef Global (Qualified "Sample" "valid")
          [Typed Ungeneralizable Explicit (Ident (Bare "x") :| [])
            (App (Qualid (Qualified "Sample" "Box")) (PosArg (Qualid (Bare "a")) :| []))]
          (Just (Qualid (Bare "Prop"))) (Qualid (Bare "True")) NotExistingClass)))
  ]

grammarBranchCases :: [(String, T.Text, Edit)]
grammarBranchCases =
  [ ("type-phase addition", "add type Sample Inductive Extra (a : Type) : Type := MkExtra (payload : a).",
      AddEdit (mkModuleName "Sample")
        (RocqInductiveDef (Inductive (IndBody (Bare "Extra")
          [Typed Ungeneralizable Explicit (Ident (Bare "a") :| []) (Qualid (Bare "Type"))]
          (Qualid (Bare "Type"))
          [(Bare "MkExtra", [Typed Ungeneralizable Explicit (Ident (Bare "payload") :| [])
              (Qualid (Bare "a"))], Nothing)] NotUnivPoly :| []) [])) PhaseTyCl)
  , ("positional structural argument", "termination Sample.fold {struct 2}",
      TerminationEdit (Qualified "Sample" "fold") (StructOrderTA (StructPos_ 2)))
  , ("measure with default relation", "termination Sample.fold {measure (size xs)}",
      TerminationEdit (Qualified "Sample" "fold") (WellFoundedTA (MeasureOrder_
        (App (Qualid (Bare "size")) (PosArg (Qualid (Bare "xs")) :| [])) Nothing)))
  , ("measure with custom relation",
      "termination Sample.fold {measure (size xs) (fun n m => lt m n)}",
      TerminationEdit (Qualified "Sample" "fold") (WellFoundedTA (MeasureOrder_
        (App (Qualid (Bare "size")) (PosArg (Qualid (Bare "xs")) :| []))
        (Just (Fun (ExplicitBinder (Ident (Bare "n")) :| [ExplicitBinder (Ident (Bare "m"))])
          (App (Qualid (Bare "lt"))
            (PosArg (Qualid (Bare "m")) :| [PosArg (Qualid (Bare "n"))])))))))
  , ("well-founded relation and decreasing variable", "termination Sample.fold {wf (R xs) xs}",
      TerminationEdit (Qualified "Sample" "fold") (WellFoundedTA (WFOrder_
        (App (Qualid (Bare "R")) (PosArg (Qualid (Bare "xs")) :| [])) (Bare "xs"))))
  , ("deferred termination", "termination Sample.fold deferred",
      TerminationEdit (Qualified "Sample" "fold") Deferred)
  , ("corecursive termination", "termination Sample.repeat corecursive",
      TerminationEdit (Qualified "Sample" "repeat") Corecursive)
  , ("parameters without indices", "data type arguments Sample.Pair (parameters: a b)",
      DataTypeArgumentsEdit (Qualified "Sample" "Pair") (DataTypeArguments [Bare "a", Bare "b"] []))
  , ("indices without parameters", "data type arguments Sample.Matrix (indices: n m)",
      DataTypeArgumentsEdit (Qualified "Sample" "Matrix") (DataTypeArguments [] [Bare "n", Bare "m"]))
  , ("omitted data arguments", "data type arguments Sample.Unit",
      DataTypeArgumentsEdit (Qualified "Sample" "Unit") (DataTypeArguments [] []))
  , ("explicitly empty data arguments", "data type arguments Sample.Unit (parameters:) (indices:)",
      DataTypeArgumentsEdit (Qualified "Sample" "Unit") (DataTypeArguments [] []))
  , ("remove type annotation", "set type Sample.inferred no type",
      SetTypeEdit (Qualified "Sample" "inferred") Nothing)
  , ("rename in type namespace", "rename type Sample.Old = Target.New",
      RenameEdit (NamespacedIdent TypeNS (Qualified "Sample" "Old")) (Qualified "Target" "New"))
  , ("constructor notation scope accepts type keyword", "add scope type for constructor Sample.Wrap",
      AdditionalScopeEdit SPConstructor (Qualified "Sample" "Wrap") "type")
  , ("combined polymorphic cumulative syntax", "universe polymorphic cumulative Sample.Box",
      UniverseCumulativeEdit (Qualified "Sample" "Box"))
  , ("nested in syntax", "in Sample.outer in Sample.inner skip method Sample.Class meth",
      InEdit (Qualified "Sample" "outer") (InEdit (Qualified "Sample" "inner")
        (SkipMethodEdit (Qualified "Sample" "Class") "meth")))
  , ("in containing except", "in Sample.outer except in Sample.inner polyrec Sample.loop",
      InEdit (Qualified "Sample" "outer") (ExceptInEdit (Qualified "Sample" "inner" :| [])
        (PolyrecEdit (Qualified "Sample" "loop"))))
  ]

definitionCases :: [(String, T.Text, RocqDefinition)]
definitionCases =
  [ ("local definition with implicit and generalized binders",
      "Local Definition Sample.project {a b : Type} `{inst : Class a} `(Class b) (_ : a) := choose (payload := 3) (@id a).",
      RocqDefinitionDef (DefinitionDef Local (Qualified "Sample" "project")
        [ Typed Ungeneralizable Implicit (Ident (Bare "a") :| [Ident (Bare "b")]) (Qualid (Bare "Type"))
        , Typed Generalizable Implicit (Ident (Bare "inst") :| [])
            (App (Qualid (Bare "Class")) (PosArg (Qualid (Bare "a")) :| []))
        , Generalized Explicit (App (Qualid (Bare "Class")) (PosArg (Qualid (Bare "b")) :| []))
        , Typed Ungeneralizable Explicit (UnderscoreName :| []) (Qualid (Bare "a"))
        ] Nothing (App (Qualid (Bare "choose"))
          (NamedArg "payload" (Num 3) :| [PosArg (ExplicitApp (Bare "id") [Qualid (Bare "a")])]))
        NotExistingClass))
  , ("let definition with inferred implicit binder", "Let local {a} (x : a) := x.",
      RocqDefinitionDef (LetDef (Bare "local")
        [ ImplicitBinders (Ident (Bare "a") :| [])
        , Typed Ungeneralizable Explicit (Ident (Bare "x") :| []) (Qualid (Bare "a"))
        ] Nothing (Qualid (Bare "x"))))
  , ("record instance preserves fields and binders",
      "Instance Sample.inst {a : Type} : Class a := {first := @id a; second := 2}.",
      RocqInstanceDef (InstanceDefinition (Qualified "Sample" "inst")
        [Typed Ungeneralizable Implicit (Ident (Bare "a") :| []) (Qualid (Bare "Type"))]
        (App (Qualid (Bare "Class")) (PosArg (Qualid (Bare "a")) :| []))
        [(Bare "first", ExplicitApp (Bare "id") [Qualid (Bare "a")]), (Bare "second", Num 2)] Nothing))
  , ("term instance", "Instance Sample.inherited {a} : Class a := parent a.",
      RocqInstanceDef (InstanceTerm (Qualified "Sample" "inherited")
        [ImplicitBinders (Ident (Bare "a") :| [])]
        (App (Qualid (Bare "Class")) (PosArg (Qualid (Bare "a")) :| []))
        (App (Qualid (Bare "parent")) (PosArg (Qualid (Bare "a")) :| [])) Nothing))
  , ("cofixpoint definition",
      "CoFixpoint Sample.ones (u : unit) : Stream := Sample.cons 1 (Sample.ones u).",
      RocqFixpointDef (CoFixpoint (FixBody (Qualified "Sample" "ones")
        (Typed Ungeneralizable Explicit (Ident (Bare "u") :| []) (Qualid (Bare "unit")) :| [])
        Nothing (Just (Qualid (Bare "Stream")))
        (App (Qualid (Qualified "Sample" "cons")) (PosArg (Num 1) :|
          [PosArg (App (Qualid (Qualified "Sample" "ones")) (PosArg (Qualid (Bare "u")) :| []))]))
        :| []) []))
  , ("mutual fixpoint definitions",
      "Fixpoint Sample.left (n : nat) {struct n} : nat := Sample.right n with Sample.right (n : nat) : nat := n.",
      RocqFixpointDef (Fixpoint
        (FixBody (Qualified "Sample" "left")
          (Typed Ungeneralizable Explicit (Ident (Bare "n") :| []) (Qualid (Bare "nat")) :| [])
          (Just (StructOrder (Bare "n"))) (Just (Qualid (Bare "nat")))
          (App (Qualid (Qualified "Sample" "right")) (PosArg (Qualid (Bare "n")) :| [])) :|
        [FixBody (Qualified "Sample" "right")
          (Typed Ungeneralizable Explicit (Ident (Bare "n") :| []) (Qualid (Bare "nat")) :| [])
          Nothing (Just (Qualid (Bare "nat"))) (Qualid (Bare "n"))]) []))
  , ("empty coinductive uses default sort", "CoInductive Sample.Empty := .",
      RocqInductiveDef (CoInductive
        (IndBody (Qualified "Sample" "Empty") [] (Sort Type) [] NotUnivPoly :| []) []))
  , ("if expression in a definition", "Definition Sample.branch b := if b then left else right.",
      RocqDefinitionDef (DefinitionDef Global (Qualified "Sample" "branch")
        [ExplicitBinder (Ident (Bare "b"))] Nothing
        (If SymmetricIf (Qualid (Bare "b")) Nothing (Qualid (Bare "left")) (Qualid (Bare "right")))
        NotExistingClass))
  , ("hash-number term in a definition", "Definition Sample.literal := #17.",
      RocqDefinitionDef (DefinitionDef Global (Qualified "Sample" "literal") [] Nothing
        (App (Qualid (Qualified "GHC.Num" "fromInteger")) (PosArg (Num 17) :| [])) NotExistingClass))
  , ("let fix term in a definition",
      "Definition Sample.localLoop := let fix loop (n : nat) {struct n} : nat := n in loop 3.",
      RocqDefinitionDef (DefinitionDef Global (Qualified "Sample" "localLoop") [] Nothing
        (Let (Bare "loop") [] Nothing (Fix (FixOne (FixBody (Bare "loop")
          (Typed Ungeneralizable Explicit (Ident (Bare "n") :| []) (Qualid (Bare "nat")) :| [])
          (Just (StructOrder (Bare "n"))) (Just (Qualid (Bare "nat"))) (Qualid (Bare "n")))))
          (App (Qualid (Bare "loop")) (PosArg (Num 3) :| []))) NotExistingClass))
  , ("raw Qed proof preserves whitespace, comments, and strings",
      "Lemma Sample.proof (x : nat) : True.\nProof.\n  (* keep spacing *)\n  pose (\"raw.path\") as text.\n  exact I.\nQed.",
      RocqAssertionDef (Assertion Lemma (Qualified "Sample" "proof")
        [Typed Ungeneralizable Explicit (Ident (Bare "x") :| []) (Qualid (Bare "nat"))]
        (Qualid (Bare "True")),
        ProofQed "  (* keep spacing *)\n  pose (\"raw.path\") as text.\n  exact I.\n"))
  , ("raw Defined proof preserves same-line leading spaces",
      "Theorem Sample.transparent : True. Proof.  idtac \"raw text\". exact I.\nDefined.",
      RocqAssertionDef (Assertion Theorem (Qualified "Sample" "transparent") [] (Qualid (Bare "True")),
        ProofDefined "  idtac \"raw text\". exact I.\n"))
  , ("raw Admitted proof preserves tactics", "Example Sample.todo : True. Proof.\n  idtac \"verbatim\".\nAdmitted.",
      RocqAssertionDef (Assertion Example (Qualified "Sample" "todo") [] (Qualid (Bare "True")),
        ProofAdmitted "  idtac \"verbatim\".\n"))
  ]

termCases :: [(String, T.Text, Term)]
termCases =
  [ ("match has multiple scrutinees, explicit/as patterns, and alternatives",
      "match x, y with | @Pair a b as whole, _ => f whole | 0, Some z | 1, Some z => z end",
      Match (MatchItem (Qualid (Bare "x")) Nothing Nothing :|
        [MatchItem (Qualid (Bare "y")) Nothing Nothing]) Nothing
        [ Equation (MultPattern
            (AsPat (ExplicitArgsPat (Bare "Pair") (QualidPat (Bare "a") :| [QualidPat (Bare "b")]))
              (Bare "whole") :| [UnderscorePat]) :| [])
            (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "whole")) :| []))
        , Equation (MultPattern (NumPat 0 :| [ArgsPat (Bare "Some") [QualidPat (Bare "z")]]) :|
            [MultPattern (NumPat 1 :| [ArgsPat (Bare "Some") [QualidPat (Bare "z")]])]) (Qualid (Bare "z"))
        ])
  , ("destructuring let pattern", "let 'Pair x y := pair in x",
      LetTick (ArgsPat (Bare "Pair") [QualidPat (Bare "x"), QualidPat (Bare "y")])
        (Qualid (Bare "pair")) (Qualid (Bare "x")))
  , ("forall with implicit binders and right-associated arrow", "forall {a} (x : a), a -> a -> a",
      Forall (ImplicitBinders (Ident (Bare "a") :| []) :|
        [Typed Ungeneralizable Explicit (Ident (Bare "x") :| []) (Qualid (Bare "a"))])
        (Arrow (Qualid (Bare "a")) (Arrow (Qualid (Bare "a")) (Qualid (Bare "a")))))
  ]

aliasChecks :: [IO ()]
aliasChecks =
  [ assertEqual "aliases affect following qualids, module names, binders, and bodies in one file"
      (Right
        [ SkipEdit (Qualified "Short" "before")
        , AliasModuleEdit "Short" "Original.Sample"
        , SkipEdit (Qualified "Original.Sample" "after")
        , ImportModuleEdit (mkModuleName "Original.Sample")
        , RenameEdit (NamespacedIdent ExprNS (Qualified "Original.Sample" "source"))
            (Qualified "Target" "result")
        , InEdit (Qualified "Original.Sample" "outer") (SkipEdit (Qualified "Original.Sample" "helper"))
        , AddEdit (mkModuleName "Original.Sample")
            (RocqDefinitionDef (DefinitionDef Global (Qualified "Original.Sample" "injected")
              [Typed Ungeneralizable Explicit (Ident (Bare "x") :| [])
                (Qualid (Qualified "Original.Sample" "Type"))] Nothing
              (App (Qualid (Qualified "Original.Sample" "id")) (PosArg (Qualid (Bare "x")) :| []))
              NotExistingClass)) PhaseTerm
        , SkipEdit (Qualified "Short.Nested" "untouched")
        , SkipEdit (Qualified "MyShort" "untouched")
        , AliasModuleEdit "Short" "Replacement.Sample"
        , SkipEdit (Qualified "Replacement.Sample" "last")
        ])
      (parseWith parseEditList (T.unlines
        [ "skip Short.before"
        , "alias module Short Original.Sample"
        , "skip Short.after"
        , "import module Short"
        , "rename value Short.source = Target.result"
        , "in Short.outer skip Short.helper"
        , "add Short Definition Short.injected (x : Short.Type) := Short.id x."
        , "skip Short.Nested.untouched"
        , "skip MyShort.untouched"
        , "alias module Short Replacement.Sample"
        , "skip Short.last"
        ]))
  , assertEqual "aliases reset between independently parsed files"
      (Right
        ( [AliasModuleEdit "Short" "Original.Sample", SkipEdit (Qualified "Original.Sample" "f")]
        , [SkipEdit (Qualified "Short" "f"), ImportModuleEdit (mkModuleName "Short")]
        ))
      ((,) <$> parseWith parseEditList "alias module Short Original.Sample\nskip Short.f\n"
           <*> parseWith parseEditList "skip Short.f\nimport module Short\n")
  , checkBuilt "alias directives have no builder effect after parsing"
      [AliasModuleEdit "Short" "First", AliasModuleEdit "Short" "Second"] mempty id
  , assertEqual "building a parsed alias file uses the expanded key"
      (Right (S.singleton (Qualified "Original.Sample" "f")))
      (_skipped <$> (parseWith parseEditList "alias module Short Original.Sample\nskip Short.f\n" >>= buildEdits))
  ]

rejectionChecks :: [IO ()]
rejectionChecks =
  [ checkRejected "unknown directive argument" parseEditList "set thing Sample.f : nat\n"
      "unexpected word `thing'"
  , checkRejected "skip method requires its method name" parseEditList "skip method Sample.Class\n"
      "unexpected newline"
  , checkRejected "indices cannot precede a parameters clause" parseEditList
      "data type arguments Sample.Box (indices: n) (parameters: a)\n" "unexpected opening"
  , checkRejected "struct requires a name or position" parseEditList "termination Sample.f {struct}\n"
      "unexpected closing"
  , checkRejected "fix requires a binder" parseTerm "fix loop {struct n} := n"
      "no binders given for fixpoint"
  , checkRejected "decreasing annotation must follow binders" parseTerm
      "fix loop {struct n} (n : nat) := n" "decreasing argument for fixpoint specified too early"
  , checkRejected "fix accepts only one decreasing annotation" parseTerm
      "fix loop (n : nat) {struct n} {measure n} := n" "too many decreasing arguments given for fixpoint"
  ]

-- Expected messages are literals, independent of the diagnostic formatter.
duplicateCases :: [(String, Edit, Edit, String)]
duplicateCases =
  [ ("type synonym", TypeSynonymTypeEdit "Text" "Type", TypeSynonymTypeEdit "Text" "Prop",
      "Duplicate type synonym result types for Text")
  , ("data arguments", DataTypeArgumentsEdit (Bare "Box") (DataTypeArguments [Bare "a"] []),
      DataTypeArgumentsEdit (Bare "Box") (DataTypeArguments [] [Bare "n"]),
      "Duplicate data type argument specifications for Box")
  , ("termination", TerminationEdit (Qualified "Sample" "f") Deferred,
      TerminationEdit (Qualified "Sample" "f") Corecursive,
      "Duplicate termination requests for Sample.f")
  , ("obligations", ObligationsEdit (Bare "f") "auto", ObligationsEdit (Bare "f") "admit",
      "Duplicate obligation kinds for f")
  , ("redefinition", RedefinitionEdit (RocqAxiomDef (Bare "f", Qualid (Bare "nat"))),
      RedefinitionEdit (RocqAxiomDef (Bare "f", Qualid (Bare "bool"))), "Duplicate redefinitions for f")
  , ("skip", SkipEdit (Bare "f"), SkipEdit (Bare "f"), "Duplicate skips for f")
  , ("constructor", SkipConstructorEdit (Bare "Mk"), SkipConstructorEdit (Bare "Mk"),
      "Duplicate skipped constructor requests for Mk")
  , ("class", SkipClassEdit (Bare "Class"), SkipClassEdit (Bare "Class"),
      "Duplicate skipped class requests for Class")
  , ("method", SkipMethodEdit (Qualified "Sample" "Class") "meth",
      SkipMethodEdit (Qualified "Sample" "Class") "meth",
      "Duplicate skipped method requests for Sample.Class.meth")
  , ("equation", SkipEquationEdit (Qualified "Sample" "f") (UnderscorePat :| []),
      SkipEquationEdit (Qualified "Sample" "f") (UnderscorePat :| []),
      "Duplicate skipped equation requests for Sample.f _")
  , ("case pattern", SkipCasePatternEdit (QualidPat (Qualified "Sample" "None")),
      SkipCasePatternEdit (QualidPat (Qualified "Sample" "None")),
      "Duplicate skipped case pattern requests for Sample.None")
  , ("skip module", SkipModuleEdit (mkModuleName "Sample"), SkipModuleEdit (mkModuleName "Sample"),
      "Duplicate skipped module requests for Sample")
  , ("import module", ImportModuleEdit (mkModuleName "Sample"), ImportModuleEdit (mkModuleName "Sample"),
      "Duplicate imported module requests for Sample")
  , ("module axiomatization", AxiomatizeModuleEdit (mkModuleName "Sample"),
      AxiomatizeModuleEdit (mkModuleName "Sample"), "Duplicate module axiomatizations for Sample")
  , ("original module axiomatization", AxiomatizeOriginalModuleNameEdit (mkModuleName "Sample"),
      AxiomatizeOriginalModuleNameEdit (mkModuleName "Sample"),
      "Duplicate module axiomatizations under the original name for Sample")
  , ("definition axiomatization", AxiomatizeDefinitionEdit (Bare "f"), AxiomatizeDefinitionEdit (Bare "f"),
      "Duplicate definition axiomatizations for f")
  , ("definition unaxiomatization", UnaxiomatizeDefinitionEdit (Bare "f"), UnaxiomatizeDefinitionEdit (Bare "f"),
      "Duplicate definition unaxiomatizations for f")
  , ("manual notation", HasManualNotationEdit (mkModuleName "Sample"), HasManualNotationEdit (mkModuleName "Sample"),
      "Duplicate has manual notation for Sample")
  , ("value scope", AdditionalScopeEdit SPValue (Bare "f") "first", AdditionalScopeEdit SPValue (Bare "f") "second",
      "Duplicate additions of a scope for value f")
  , ("constructor scope", AdditionalScopeEdit SPConstructor (Bare "Mk") "first",
      AdditionalScopeEdit SPConstructor (Bare "Mk") "second", "Duplicate additions of a scope for constructor Mk")
  , ("value renaming", RenameEdit (NamespacedIdent ExprNS (Bare "f")) (Bare "g"),
      RenameEdit (NamespacedIdent ExprNS (Bare "f")) (Bare "h"), "Duplicate renamings for value f")
  , ("type renaming", RenameEdit (NamespacedIdent TypeNS (Bare "T")) (Bare "U"),
      RenameEdit (NamespacedIdent TypeNS (Bare "T")) (Bare "V"), "Duplicate renamings for type T")
  , ("data kinds", DataKindEdit (Bare "T") (Qualid (Bare "Type") :| []),
      DataKindEdit (Bare "T") (Qualid (Bare "Prop") :| []), "Duplicate data kinds for T")
  , ("polykinds", PolyKindEdit (Bare "T") ("k" :| []), PolyKindEdit (Bare "T") ("j" :| []),
      "Duplicate polykinds for T")
  , ("unused variables", DeleteUnusedTypeVariablesEdit (Bare "T"), DeleteUnusedTypeVariablesEdit (Bare "T"),
      "Duplicate unused type variables deletions for T")
  , ("coinductive", CoinductiveEdit (Bare "T"), CoinductiveEdit (Bare "T"),
      "Duplicate coinductive data types for T")
  , ("module renaming", RenameModuleEdit (mkModuleName "From") (mkModuleName "First"),
      RenameModuleEdit (mkModuleName "From") (mkModuleName "Second"), "Duplicate renamed modules for From")
  , ("simple class", SimpleClassEdit (Bare "Class"), SimpleClassEdit (Bare "Class"),
      "Duplicate simple class requests for Class")
  , ("inline mutual", InlineMutualEdit (Bare "f"), InlineMutualEdit (Bare "f"),
      "Duplicate inlined mutually recursive functions for f")
  , ("set type", SetTypeEdit (Bare "f") (Just (Qualid (Bare "nat"))), SetTypeEdit (Bare "f") Nothing,
      "Duplicate set types for f")
  , ("collapse let", CollapseLetEdit (Bare "f"), CollapseLetEdit (Bare "f"), "Duplicate collapsed lets for f")
  , ("promote", PromoteEdit (Qualified "Sample" "f"), PromoteEdit (Qualified "Sample" "f"),
      "Duplicate promotions for Sample.f")
  , ("polyrec", PolyrecEdit (Qualified "Sample" "f"), PolyrecEdit (Qualified "Sample" "f"),
      "Duplicate polymorphic recursion requests for Sample.f")
  , ("universe polymorphic", UniversePolymorphicEdit (Bare "T"), UniversePolymorphicEdit (Bare "T"),
      "Duplicate universe polymorphic requests for T")
  , ("universe cumulative", UniverseCumulativeEdit (Bare "T"), UniverseCumulativeEdit (Bare "T"),
      "Duplicate universe cumulative requests for T")
  , ("equations", EquationsEdit (Bare "f"), EquationsEdit (Bare "f"), "Duplicate equations requests for f")
  ]

mappingConfig :: Either String Edits
mappingConfig = buildEdits
  [ TypeSynonymTypeEdit "Text" "Type"
  , DataTypeArgumentsEdit (Bare "Vector") (DataTypeArguments [Bare "a"] [Bare "n"])
  , TerminationEdit (Bare "loop") (StructOrderTA (StructPos_ 2))
  , ObligationsEdit (Bare "proof") "auto"
  , RedefinitionEdit (RocqAxiomDef (Bare "external", Qualid (Bare "nat")))
  , SkipEdit (Bare "hidden")
  , SkipConstructorEdit (Bare "Hidden")
  , SkipClassEdit (Bare "HiddenClass")
  , SkipMethodEdit (Bare "Class") "hiddenMethod"
  , SkipEquationEdit (Bare "choose") (ArgsPat (Bare "None") [] :| [])
  , SkipEquationEdit (Bare "choose") (ArgsPat (Bare "Some") [ArgsPat (Bare "None") []] :| [UnderscorePat])
  , SkipCasePatternEdit (AsPat (ArgsPat (Bare "Node") [ArgsPat (Bare "Leaf") []]) (Bare "tree"))
  , SkipModuleEdit (mkModuleName "Hidden.Module")
  , ImportModuleEdit (mkModuleName "Support.Module")
  , AxiomatizeModuleEdit (mkModuleName "Opaque.Module")
  , AxiomatizeOriginalModuleNameEdit (mkModuleName "Original.Module")
  , AxiomatizeDefinitionEdit (Bare "opaque")
  , UnaxiomatizeDefinitionEdit (Bare "concrete")
  , HasManualNotationEdit (mkModuleName "Notation.Module")
  , AdditionalScopeEdit SPValue (Bare "Shared") "term_scope"
  , AdditionalScopeEdit SPConstructor (Bare "Shared") "type_scope"
  , OrderEdit (Bare "first" :| [Bare "middle", Bare "last"])
  , OrderEdit (Bare "alternate" :| [Bare "last"])
  , RenameEdit (NamespacedIdent ExprNS (Bare "Shared")) (Bare "termName")
  , RenameEdit (NamespacedIdent TypeNS (Bare "Shared")) (Bare "typeName")
  , DataKindEdit (Bare "Indexed") (Qualid (Bare "Type") :| [Qualid (Bare "nat")])
  , PolyKindEdit (Bare "Indexed") ("k" :| ["j"])
  , DeleteUnusedTypeVariablesEdit (Bare "Phantom")
  , CoinductiveEdit (Bare "Stream")
  , RenameModuleEdit (mkModuleName "Original") (mkModuleName "Target")
  , SimpleClassEdit (Bare "Simple")
  , InlineMutualEdit (Bare "even")
  , SetTypeEdit (Bare "typed") (Just (Qualid (Bare "bool")))
  , SetTypeEdit (Bare "inferred") Nothing
  , CollapseLetEdit (Bare "flatten")
  , PromoteEdit (Bare "lifted")
  , PolyrecEdit (Bare "polymorphicLoop")
  , UniversePolymorphicEdit (Bare "Poly")
  , UniversePolymorphicEdit (Bare "Cumulative")
  , UniverseCumulativeEdit (Bare "Cumulative")
  , EquationsEdit (Bare "equational")
  ]

mappingChecks :: [IO ()]
mappingChecks =
  [ check "type synonym result mapping" (M.singleton "Text" "Type") _typeSynonymTypes
  , check "data argument mapping"
      (M.singleton (Bare "Vector") (DataTypeArguments [Bare "a"] [Bare "n"])) _dataTypeArguments
  , check "termination argument mapping" (M.singleton (Bare "loop") (StructOrderTA (StructPos_ 2))) _termination
  , check "obligation tactics mapping" (M.singleton (Bare "proof") "auto") _obligations
  , check "redefinition is keyed by its declared name"
      (M.singleton (Bare "external") (RocqAxiomDef (Bare "external", Qualid (Bare "nat")))) _redefinitions
  , check "skipped values" (S.singleton (Bare "hidden")) _skipped
  , check "skipped constructors" (S.singleton (Bare "Hidden")) _skippedConstructors
  , check "skipped classes" (S.singleton (Bare "HiddenClass")) _skippedClasses
  , check "skipped methods retain class and method" (S.singleton (Bare "Class", "hiddenMethod")) _skippedMethods
  , check "skipped equations merge by function and normalize nullary constructors"
      (M.singleton (Bare "choose") (S.fromList
        [ QualidPat (Bare "None") :| []
        , ArgsPat (Bare "Some") [QualidPat (Bare "None")] :| [UnderscorePat]
        ])) (M.map (S.map (fmap getNormalizedPattern)) . _skippedEquations)
  , check "skipped case patterns normalize nested constructors"
      (S.singleton (AsPat (ArgsPat (Bare "Node") [QualidPat (Bare "Leaf")]) (Bare "tree")))
      (S.map getNormalizedPattern . _skippedCasePatterns)
  , check "skipped modules" (S.singleton (mkModuleName "Hidden.Module")) _skippedModules
  , check "imported modules" (S.singleton (mkModuleName "Support.Module")) _importedModules
  , check "axiomatized modules" (S.singleton (mkModuleName "Opaque.Module")) _axiomatizedModules
  , check "original-name module axiomatizations" (S.singleton (mkModuleName "Original.Module"))
      _axiomatizedOriginalModuleNames
  , check "axiomatized definitions" (S.singleton (Bare "opaque")) _axiomatizedDefinitions
  , check "unaxiomatized definitions" (S.singleton (Bare "concrete")) _unaxiomatizedDefinitions
  , check "manual notation modules" (S.singleton (mkModuleName "Notation.Module")) _hasManualNotation
  , check "value and constructor scopes have separate keys"
      (M.fromList [((SPValue, Bare "Shared"), "term_scope"), ((SPConstructor, Bare "Shared"), "type_scope")])
      _additionalScopes
  , check "order records adjacent prerequisites and unions repeated edges"
      (M.fromList [(Bare "middle", S.singleton (Bare "first")),
        (Bare "last", S.fromList [Bare "middle", Bare "alternate"])]) _orders
  , check "type and value renamings have separate keys"
      (M.fromList [(NamespacedIdent ExprNS (Bare "Shared"), Bare "termName"),
        (NamespacedIdent TypeNS (Bare "Shared"), Bare "typeName")]) _renamings
  , check "data kinds retain their sequence"
      (M.singleton (Bare "Indexed") (Qualid (Bare "Type") :| [Qualid (Bare "nat")])) _dataKinds
  , check "polykinds retain their sequence" (M.singleton (Bare "Indexed") ("k" :| ["j"])) _polyKinds
  , check "unused variable deletions" (S.singleton (Bare "Phantom")) _deleteUnusedTypeVariables
  , check "coinductive types" (S.singleton (Bare "Stream")) _coinductiveTypes
  , check "module renaming mapping" (M.singleton (mkModuleName "Original") (mkModuleName "Target")) _renamedModules
  , check "simple classes" (S.singleton (Bare "Simple")) _simpleClasses
  , check "inlined mutuals" (S.singleton (Bare "even")) _inlinedMutuals
  , check "replacement types distinguish no type from no edit"
      (M.fromList [(Bare "typed", Just (Qualid (Bare "bool"))), (Bare "inferred", Nothing)]) _replacedTypes
  , check "collapsed lets" (S.singleton (Bare "flatten")) _collapsedLets
  , check "promotions" (S.singleton (Bare "lifted")) _promotions
  , check "polymorphic recursion" (S.singleton (Bare "polymorphicLoop")) _polyrecs
  , check "universe polymorphic requests" (S.fromList [Bare "Poly", Bare "Cumulative"]) _universePolymorphic
  , check "universe cumulative requests" (S.singleton (Bare "Cumulative")) _universeCumulative
  , check "equations requests" (S.singleton (Bare "equational")) _equations
  , check "universe status defaults to monomorphic" NotUnivPoly (lookupUniverseStatus (Bare "Unknown"))
  , check "universe status recognizes polymorphic" UnivPoly (lookupUniverseStatus (Bare "Poly"))
  , check "cumulative status subsumes polymorphic" UnivPolyCumulative (lookupUniverseStatus (Bare "Cumulative"))
  , checkBuilt "a one-name order creates no dependency" [OrderEdit (Bare "single" :| [])] M.empty _orders
  , assertEqual "normalized case-pattern duplicates are rejected"
      (Left "Duplicate skipped case pattern requests for None")
      (buildEdits [SkipCasePatternEdit (ArgsPat (Bare "None") []), SkipCasePatternEdit (QualidPat (Bare "None"))])
  , assertEqual "normalized equation-pattern duplicates are rejected"
      (Left "Duplicate skipped equation requests for f None")
      (buildEdits [SkipEquationEdit (Bare "f") (ArgsPat (Bare "None") [] :| []),
        SkipEquationEdit (Bare "f") (QualidPat (Bare "None") :| [])])
  ]
  where
    check :: (Eq a, Show a) => String -> a -> (Edits -> a) -> IO ()
    check label = checkConfig label mappingConfig

additionChecks :: [IO ()]
additionChecks =
  [ checkBuilt "additions reverse source order within each phase and retain their module"
      [ AddEdit (mkModuleName "Sample") (RocqAxiomDef (Bare "termFirst", Qualid (Bare "nat"))) PhaseTerm
      , AddEdit (mkModuleName "Sample") (RocqAxiomDef (Bare "typeFirst", Qualid (Bare "Type"))) PhaseTyCl
      , AddEdit (mkModuleName "Sample") (RocqAxiomDef (Bare "termLast", Qualid (Bare "bool"))) PhaseTerm
      , AddEdit (mkModuleName "Sample") (RocqAxiomDef (Bare "typeLast", Qualid (Bare "Prop"))) PhaseTyCl
      , AddEdit (mkModuleName "Other") (RocqAxiomDef (Bare "only", Qualid (Bare "unit"))) PhaseTerm
      ]
      (M.fromList
        [ (mkModuleName "Sample",
            ( [ AssumptionSentence (Assumption Axiom (Assums (Bare "typeLast" :| []) (Qualid (Bare "Prop"))))
              , AssumptionSentence (Assumption Axiom (Assums (Bare "typeFirst" :| []) (Qualid (Bare "Type"))))
              ]
            , [ AssumptionSentence (Assumption Axiom (Assums (Bare "termLast" :| []) (Qualid (Bare "bool"))))
              , AssumptionSentence (Assumption Axiom (Assums (Bare "termFirst" :| []) (Qualid (Bare "nat"))))
              ]))
        , (mkModuleName "Other", ([],
            [AssumptionSentence (Assumption Axiom (Assums (Bare "only" :| []) (Qualid (Bare "unit"))))]))
        ]) _additions
  , checkBuilt "repeated additions are allowed"
      [ AddEdit (mkModuleName "Sample") (RocqAxiomDef (Bare "extra", Qualid (Bare "nat"))) PhaseTerm
      , AddEdit (mkModuleName "Sample") (RocqAxiomDef (Bare "extra", Qualid (Bare "nat"))) PhaseTerm
      ]
      (M.singleton (mkModuleName "Sample") ([],
        [ AssumptionSentence (Assumption Axiom (Assums (Bare "extra" :| []) (Qualid (Bare "nat"))))
        , AssumptionSentence (Assumption Axiom (Assums (Bare "extra" :| []) (Qualid (Bare "nat"))))
        ])) _additions
  ]

scopeChecks :: [IO ()]
scopeChecks =
  [ checkBuilt "scoped edits accumulate independently, including nested in and local except" input
      (M.fromList
        [ (Bare "outer", mempty
            { _termination = M.singleton (Bare "loop") Corecursive
            , _skipped = S.singleton (Bare "helper")
            , _renamings = M.singleton (NamespacedIdent ExprNS (Bare "old")) (Bare "fresh")
            , _inEdits = M.singleton (Bare "inner") (mempty
                { _termination = M.singleton (Bare "nested") (StructOrderTA (StructId_ (Bare "x"))) })
            , _exceptInEdits = M.fromList
                [ (Bare "inner", mempty
                    { _renamings = M.singleton (NamespacedIdent ExprNS (Bare "old")) (Bare "fresh") })
                , (Bare "second", mempty
                    { _renamings = M.singleton (NamespacedIdent ExprNS (Bare "old")) (Bare "fresh") })
                ]
            })
        , (Bare "other", mempty { _skipped = S.singleton (Bare "helper") })
        ]) _inEdits
  , checkBuilt "scoped termination does not overwrite the global request" input
      (M.singleton (Bare "loop") Deferred) _termination
  , checkBuilt "scoped skips do not leak into the global set" input (S.singleton (Bare "globalOnly")) _skipped
  , checkBuilt "scoped except does not leak into global exclusions" input M.empty _exceptInEdits
  , assertEqual "duplicates within one scope retain the ordinary diagnostic"
      (Left "Duplicate skips for helper")
      (buildEdits [InEdit (Bare "outer") (SkipEdit (Bare "helper")),
        InEdit (Bare "outer") (SkipEdit (Bare "helper"))])
  , assertEqual "duplicates within a nested scope are diagnosed"
      (Left "Duplicate termination requests for loop")
      (buildEdits
        [ InEdit (Bare "outer") (InEdit (Bare "inner") (TerminationEdit (Bare "loop") Deferred))
        , InEdit (Bare "outer") (InEdit (Bare "inner") (TerminationEdit (Bare "loop") Corecursive))
        ])
  ]
  where
    input =
      [ TerminationEdit (Bare "loop") Deferred
      , SkipEdit (Bare "globalOnly")
      , InEdit (Bare "outer") (TerminationEdit (Bare "loop") Corecursive)
      , InEdit (Bare "outer") (SkipEdit (Bare "helper"))
      , InEdit (Bare "other") (SkipEdit (Bare "helper"))
      , InEdit (Bare "outer") (InEdit (Bare "inner")
          (TerminationEdit (Bare "nested") (StructOrderTA (StructId_ (Bare "x")))))
      , InEdit (Bare "outer") (ExceptInEdit (Bare "inner" :| [Bare "second"])
          (RenameEdit (NamespacedIdent ExprNS (Bare "old")) (Bare "fresh")))
      ]

-- Except subtraction is supported for these six components only.
exceptFields :: Edits -> (M.Map Qualid TerminationArgument, S.Set Pattern, Renamings,
                         [Rewrite], S.Set Qualid, S.Set Qualid)
exceptFields config =
  ( _termination config, S.map getNormalizedPattern (_skippedCasePatterns config)
  , _renamings config, _rewrites config, _polyrecs config, _equations config
  )

exceptChecks :: [IO ()]
exceptChecks =
  [ checkConfig "except directives install all six supported components globally" config allFields exceptFields
  , checkConfig "each excluded definition records all six components" config
      (M.fromList [(Bare "keep", excludedFields), (Bare "alsoKeep", excludedFields)])
      (M.map exceptFields . _exceptInEdits)
  , checkConfig "subtracting exclusions removes only the specified entries" withoutExcluded keptFields exceptFields
  , checkConfig "ordinary definitions retain all except edits" config allFields
      (\ed -> exceptFields (subtractEdits ed (M.findWithDefault mempty (Bare "ordinary") (_exceptInEdits ed))))
  , checkConfig "map subtraction removes a matching key regardless of its value"
      (subtractEdits <$> buildEdits [TerminationEdit (Bare "loop") Deferred]
                    <*> buildEdits [TerminationEdit (Bare "loop") Corecursive]) M.empty _termination
  , checkConfig "rewrite subtraction removes one occurrence and preserves the remaining order"
      (subtractEdits <$> buildEdits [RewriteEdit removedRule, RewriteEdit removedRule, RewriteEdit keptRule]
                    <*> buildEdits [RewriteEdit removedRule]) [keptRule, removedRule] _rewrites
  , assertEqual "overlapping except requests still diagnose per-file duplicates"
      (Left "Duplicate termination requests for loop")
      (buildEdits
        [ ExceptInEdit (Bare "keep" :| []) (TerminationEdit (Bare "loop") Deferred)
        , ExceptInEdit (Bare "keep" :| []) (TerminationEdit (Bare "loop") Corecursive)
        ])
  ]
  where
    removedRule = Rewrite ["x"]
      (App (Qualid (Bare "source")) (PosArg (Qualid (Bare "x")) :| []))
      (App (Qualid (Bare "target")) (PosArg (Qualid (Bare "x")) :| []))
    keptRule = Rewrite [] (Qualid (Bare "before")) (Qualid (Bare "after"))
    config = buildEdits $
      [ ExceptInEdit (Bare "keep" :| [Bare "alsoKeep"]) edit
      | edit <-
          [ TerminationEdit (Bare "loop") Deferred
          , SkipCasePatternEdit (ArgsPat (Bare "None") [])
          , RenameEdit (NamespacedIdent ExprNS (Bare "f")) (Bare "g")
          , RewriteEdit removedRule
          , PolyrecEdit (Bare "loop")
          , EquationsEdit (Bare "loop")
          ]
      ] ++
      [ TerminationEdit (Bare "other") (StructOrderTA (StructId_ (Bare "x")))
      , SkipCasePatternEdit (QualidPat (Bare "Other"))
      , RenameEdit (NamespacedIdent TypeNS (Bare "T")) (Bare "U")
      , RewriteEdit keptRule
      , PolyrecEdit (Bare "other")
      , EquationsEdit (Bare "other")
      ]
    withoutExcluded = do
      ed <- config
      case M.lookup (Bare "keep") (_exceptInEdits ed) of
        Nothing -> Left "missing exclusion entry for keep"
        Just excluded -> Right (subtractEdits ed excluded)
    excludedFields =
      ( M.singleton (Bare "loop") Deferred, S.singleton (QualidPat (Bare "None"))
      , M.singleton (NamespacedIdent ExprNS (Bare "f")) (Bare "g")
      , [removedRule], S.singleton (Bare "loop"), S.singleton (Bare "loop")
      )
    keptFields =
      ( M.singleton (Bare "other") (StructOrderTA (StructId_ (Bare "x"))), S.singleton (QualidPat (Bare "Other"))
      , M.singleton (NamespacedIdent TypeNS (Bare "T")) (Bare "U")
      , [keptRule], S.singleton (Bare "other"), S.singleton (Bare "other")
      )
    allFields =
      ( M.fromList [(Bare "loop", Deferred), (Bare "other", StructOrderTA (StructId_ (Bare "x")))]
      , S.fromList [QualidPat (Bare "None"), QualidPat (Bare "Other")]
      , M.fromList [(NamespacedIdent ExprNS (Bare "f"), Bare "g"), (NamespacedIdent TypeNS (Bare "T"), Bare "U")]
      , [keptRule, removedRule], S.fromList [Bare "loop", Bare "other"], S.fromList [Bare "loop", Bare "other"]
      )

mergeChecks :: [IO ()]
mergeChecks =
  [ checkConfig "independently built files merge maps with left-file precedence" merged
      (M.fromList
        [ (Bare "shared", Just (Qualid (Bare "nat")))
        , (Bare "leftOnly", Nothing)
        , (Bare "rightOnly", Just (Qualid (Bare "unit")))
        ]) _replacedTypes
  , checkConfig "reversing file order reverses map precedence" reversed
      (M.fromList
        [ (Bare "shared", Just (Qualid (Bare "bool")))
        , (Bare "leftOnly", Nothing)
        , (Bare "rightOnly", Just (Qualid (Bare "unit")))
        ]) _replacedTypes
  , checkConfig "renaming map collision selects the left file" merged
      (M.singleton (NamespacedIdent ExprNS (Qualified "Original" "f")) (Qualified "First" "f")) _renamings
  , checkConfig "file merge unions set components" merged
      (S.fromList [Bare "firstSkipped", Bare "secondSkipped"]) _skipped
  , checkConfig "file merge selects an entire additions entry for a repeated module" merged
      (M.fromList
        [ (mkModuleName "Sample", ([],
            [ AssumptionSentence (Assumption Axiom (Assums (Bare "leftLast" :| []) (Qualid (Bare "bool"))))
            , AssumptionSentence (Assumption Axiom (Assums (Bare "leftFirst" :| []) (Qualid (Bare "nat"))))
            ]))
        , (mkModuleName "Other", ([],
            [AssumptionSentence (Assumption Axiom (Assums (Bare "other" :| []) (Qualid (Bare "unit"))))]))
        ]) _additions
  , checkConfig "file merge selects the left prerequisite set for a repeated order key" merged
      (M.singleton (Bare "shared") (S.singleton (Bare "before"))) _orders
  , checkConfig "file merge selects a whole scoped config instead of merging its fields" merged
      (M.fromList
        [ (Bare "outer", mempty { _skipped = S.singleton (Bare "leftHelper") })
        , (Bare "other", mempty { _skipped = S.singleton (Bare "otherHelper") })
        ]) _inEdits
  , checkConfig "rewrite lists concatenate files after reversing each file" merged
      [ Rewrite ["x"]
          (App (Qualid (Qualified "Stage" "left")) (PosArg (Qualid (Bare "x")) :| []))
          (App (Qualid (Qualified "Result" "left")) (PosArg (Qualid (Bare "x")) :| []))
      , Rewrite ["x"]
          (App (Qualid (Qualified "First" "f")) (PosArg (Qualid (Bare "x")) :| []))
          (App (Qualid (Qualified "Stage" "left")) (PosArg (Qualid (Bare "x")) :| []))
      , Rewrite ["x"]
          (App (Qualid (Qualified "Stage" "left")) (PosArg (Qualid (Bare "x")) :| []))
          (App (Qualid (Qualified "Result" "right")) (PosArg (Qualid (Bare "x")) :| []))
      ] _rewrites
  , checkConfig "later file rules see results of earlier file rules" merged
      (App (Qualid (Qualified "Result" "right")) (PosArg (Num 9) :| []))
      (\ed -> rewrite (_rewrites ed) (App (Qualid (Qualified "First" "f")) (PosArg (Num 9) :| [])))
  , checkConfig "reversing files changes rewrite application order" reversed
      (App (Qualid (Qualified "Stage" "left")) (PosArg (Num 9) :| []))
      (\ed -> rewrite (_rewrites ed) (App (Qualid (Qualified "First" "f")) (PosArg (Num 9) :| [])))
  , assertEqual "the same map collision is rejected within a single file"
      (Left "Duplicate set types for shared")
      (parseConfig "set type shared : nat\nset type shared : bool\n")
  ]
  where
    firstFile = parseConfig (T.unlines
      [ "set type shared : nat"
      , "set type leftOnly no type"
      , "rename value Original.f = First.f"
      , "skip firstSkipped"
      , "add Sample Axiom leftFirst : nat."
      , "add Sample Axiom leftLast : bool."
      , "order before shared"
      , "in outer skip leftHelper"
      , "rewrite forall x, First.f x = Stage.left x"
      , "rewrite forall x, Stage.left x = Result.left x"
      ])
    secondFile = parseConfig (T.unlines
      [ "set type shared : bool"
      , "set type rightOnly : unit"
      , "rename value Original.f = Second.f"
      , "skip secondSkipped"
      , "add Sample Axiom ignored : unit."
      , "add Other Axiom other : unit."
      , "order alternate shared"
      , "in outer skip rightHelper"
      , "in other skip otherHelper"
      , "rewrite forall x, Stage.left x = Result.right x"
      ])
    merged = (<>) <$> firstFile <*> secondFile
    reversed = (<>) <$> secondFile <*> firstFile

rewriteChecks :: [IO ()]
rewriteChecks =
  [ checkConfig "per-file rewrite rules are stored in reverse source order" forward
      [ Rewrite [] (Qualid (Bare "third")) (Qualid (Bare "fourth"))
      , Rewrite [] (Qualid (Bare "second")) (Qualid (Bare "third"))
      , Rewrite [] (Qualid (Bare "first")) (Qualid (Bare "second"))
      ] _rewrites
  , checkConfig "rewrite traverses its list once in the stored order" forward (Qualid (Bare "second"))
      (\ed -> rewrite (_rewrites ed) (Qualid (Bare "first")))
  , checkConfig "reversing source rules permits a complete chain" backward (Qualid (Bare "fourth"))
      (\ed -> rewrite (_rewrites ed) (Qualid (Bare "first")))
  , checkBuilt "repeated rewrite rules are retained"
      [ RewriteEdit (Rewrite [] (Num 1) (Num 2)), RewriteEdit (Rewrite [] (Num 1) (Num 2)) ]
      [ Rewrite [] (Num 1) (Num 2), Rewrite [] (Num 1) (Num 2) ] _rewrites
  , assertEqual "renaming lookup supplies the head that matches a target-spelled rewrite"
      (Right (App (Qualid (Qualified "Target" "g")) (PosArg (Qualid (Bare "z")) :| [PosArg (Num 3)])))
      (do
        ed <- renamedConfig
        case M.lookup (NamespacedIdent ExprNS (Qualified "Original" "f")) (_renamings ed) of
          Nothing -> Left "missing Original.f renaming"
          Just name -> Right (rewrite (_rewrites ed)
            (App (Qualid name) (PosArg (Num 3) :| [PosArg (Qualid (Bare "z"))]))))
  , checkConfig "old-spelled rewrite does not match an already renamed head"
      (parseConfig "rename value Original.f = Target.f\nrewrite forall x, Original.f x = Wrong.f x\n")
      (App (Qualid (Qualified "Target" "f")) (PosArg (Num 3) :| []))
      (\ed -> rewrite (_rewrites ed) (App (Qualid (Qualified "Target" "f")) (PosArg (Num 3) :| [])))
  , checkConfig "rewrite patterns retain their own spelling despite renaming edits" renamedConfig
      [ Rewrite ["x"]
          (App (Qualid (Qualified "Original" "f")) (PosArg (Qualid (Bare "x")) :| []))
          (App (Qualid (Qualified "Wrong" "f")) (PosArg (Qualid (Bare "x")) :| []))
      , Rewrite ["x", "y"]
          (App (Qualid (Qualified "Target" "f"))
            (PosArg (Qualid (Bare "x")) :| [PosArg (Qualid (Bare "y"))]))
          (App (Qualid (Qualified "Target" "g"))
            (PosArg (Qualid (Bare "y")) :| [PosArg (Qualid (Bare "x"))]))
      ] _rewrites
  , checkConfig "rewrite flattens nested applications and substitutes both variables" renamedConfig
      (App (Qualid (Qualified "Target" "g")) (PosArg (Num 8) :| [PosArg (Num 5)]))
      (\ed -> rewrite (_rewrites ed)
        (App (App (Qualid (Qualified "Target" "f")) (PosArg (Num 5) :| [])) (PosArg (Num 8) :| [])))
  , checkConfig "rewrite rejects a different argument count" renamedConfig
      (App (Qualid (Qualified "Target" "f")) (PosArg (Num 5) :| []))
      (\ed -> rewrite (_rewrites ed) (App (Qualid (Qualified "Target" "f")) (PosArg (Num 5) :| [])))
  ]
  where
    forward = parseConfig (T.unlines
      [ "rewrite forall , first = second"
      , "rewrite forall , second = third"
      , "rewrite forall , third = fourth"
      ])
    backward = parseConfig (T.unlines
      [ "rewrite forall , third = fourth"
      , "rewrite forall , second = third"
      , "rewrite forall , first = second"
      ])
    renamedConfig = parseConfig (T.unlines
      [ "rename value Original.f = Target.f"
      , "rewrite forall x y, Target.f x y = Target.g y x"
      , "rewrite forall x, Original.f x = Wrong.f x"
      ])

definitionKeyChecks :: [IO ()]
definitionKeyChecks =
  [ checkBuilt (label ++ " redefinition key") [RedefinitionEdit def] (M.singleton name def) _redefinitions
  | (label, name, def) <-
      [ ("Definition", Bare "defined", RocqDefinitionDef
          (DefinitionDef Global (Bare "defined") [] Nothing (Num 1) NotExistingClass))
      , ("Let", Bare "local", RocqDefinitionDef (LetDef (Bare "local") [] Nothing (Num 2)))
      , ("Fixpoint uses its first body", Bare "first", RocqFixpointDef
          (Fixpoint (body "first" :| [body "second"]) []))
      , ("CoFixpoint", Bare "stream", RocqFixpointDef (CoFixpoint (body "stream" :| []) []))
      , ("Inductive uses its first body", Bare "First", RocqInductiveDef
          (Inductive (indBody "First" :| [indBody "Second"]) []))
      , ("CoInductive", Bare "Stream", RocqInductiveDef (CoInductive (indBody "Stream" :| []) []))
      , ("record Instance", Bare "recordInstance", RocqInstanceDef
          (InstanceDefinition (Bare "recordInstance") [] (Qualid (Bare "Class")) [(Bare "field", Num 3)] Nothing))
      , ("term Instance", Bare "termInstance", RocqInstanceDef
          (InstanceTerm (Bare "termInstance") [] (Qualid (Bare "Class")) (Qualid (Bare "parent")) Nothing))
      , ("proof Instance", Bare "proofInstance", RocqInstanceDef
          (InstanceProof (Bare "proofInstance") [] (Qualid (Bare "Class")) (ProofDefined "exact parent.")))
      , ("Axiom", Bare "axiomName", RocqAxiomDef (Bare "axiomName", Qualid (Bare "nat")))
      , ("assertion", Bare "lemmaName", RocqAssertionDef
          (Assertion Lemma (Bare "lemmaName") [] (Qualid (Bare "True")), ProofQed "exact I."))
      ]
  ]
  where
    body name = FixBody (Bare name) (ExplicitBinder (Ident (Bare "x")) :| []) Nothing Nothing (Qualid (Bare "x"))
    indBody name = IndBody (Bare name) [] (Sort Type) [] NotUnivPoly

invariantChecks :: [IO ()]
invariantChecks =
  [ checkBuilt ("invariant generates notation, sigma type, and predicate in type phase (" ++ label ++ ")")
      [invariant binders]
      (M.singleton (mkModuleName "Sample")
        ( [ NotationSentence (Abbreviation Local "MkBox" ["y"]
              (App (Qualid (Bare "@existT"))
                (PosArg Underscore :|
                  [ PosArg Underscore
                  , PosArg (App (Qualid (Qualified "Sample" "MkBox_Raw"))
                      (PosArg (Qualid (Bare "y")) :| []))
                  , PosArg Underscore
                  ])))
          , DefinitionSentence (DefinitionDef Global (Qualified "Sample" "Box") binders
              (Just (Qualid (Bare "Type")))
              (Sigma (Bare "x") (Just rawType)
                (App (Qualid (Qualified "Sample" "valid")) (PosArg (Qualid (Bare "x")) :| [])))
              NotExistingClass)
          , DefinitionSentence (DefinitionDef Global (Qualified "Sample" "valid")
              [ExplicitBinder (Ident (Bare "x"))] (Just (Qualid (Bare "Prop"))) (Qualid (Bare "True"))
              NotExistingClass)
          ], [])) _additions
  | (label, binders, rawType) <-
      [ ("parameterized", [Typed Ungeneralizable Explicit (Ident (Bare "a") :| []) (Qualid (Bare "Type"))],
          App (Qualid (Qualified "Sample" "RawBox")) (PosArg (Qualid (Bare "a")) :| []))
      , ("monomorphic", [], Qualid (Qualified "Sample" "RawBox"))
      ]
  ] ++
  [ checkBuilt "invariant renames the raw type and constructor in their separate namespaces"
      [invariant []] rawRenamings _renamings
  , checkBuilt "invariant exempts exactly the requested sigma-using definitions from raw renaming"
      [invariant []]
      (M.fromList [(Qualified "Sample" "pack", rawRenamings), (Qualified "Sample" "unpack", rawRenamings)])
      (M.map _renamings . _exceptInEdits)
  ]
  where
    invariant binders = InvariantEdit (mkModuleName "Sample") (Qualified "Sample" "Box") binders "MkBox"
      [Qualified "Sample" "pack", Qualified "Sample" "unpack"]
      (RocqDefinitionDef (DefinitionDef Global (Qualified "Sample" "valid")
        [ExplicitBinder (Ident (Bare "x"))] (Just (Qualid (Bare "Prop"))) (Qualid (Bare "True")) NotExistingClass))
    rawRenamings = M.fromList
      [ (NamespacedIdent TypeNS (Qualified "Sample" "Box"), Qualified "Sample" "RawBox")
      , (NamespacedIdent ExprNS (Qualified "Sample" "MkBox"), Qualified "Sample" "MkBox_Raw")
      ]

taskChecks :: [IO ()]
taskChecks =
  [ checkBuilt ("definitionTask: " ++ label) input expected $ \ed ->
      runReader (definitionTask (Qualified "Sample" "f"))
        (ModuleEnv ed Strict Rocq_8_20 (ModuleData (mkModuleName "Sample") [] mempty))
  | (label, input, expected) <-
      [ ("ordinary definitions translate", [], TranslateIt)
      , ("skip", [skip], SkipIt)
      , ("redefine", [redefine], RedefineIt replacement)
      , ("explicit axiom", [axiom], AxiomatizeIt SpecificAxiomatize)
      , ("module axiom", [moduleAxiom], AxiomatizeIt GeneralAxiomatize)
      , ("unaxiomatize opts out of module axiom", [moduleAxiom, concrete], TranslateIt)
      , ("unaxiomatize alone translates", [concrete], TranslateIt)
      , ("unaxiomatize does not cancel a specific axiom", [axiom, concrete], AxiomatizeIt SpecificAxiomatize)
      , ("module axiom takes the general mode", [moduleAxiom, axiom], AxiomatizeIt GeneralAxiomatize)
      , ("module opt-out takes precedence over a specific axiom", [moduleAxiom, axiom, concrete], TranslateIt)
      , ("redefine precedes every axiom request", [redefine, moduleAxiom, axiom, concrete], RedefineIt replacement)
      , ("skip precedes redefine and all axiom requests", [skip, redefine, moduleAxiom, axiom, concrete], SkipIt)
      , ("other modules do not axiomatize this module", [AxiomatizeModuleEdit (mkModuleName "Other")], TranslateIt)
      , ("other definitions do not axiomatize this definition",
          [AxiomatizeDefinitionEdit (Qualified "Sample" "other")], TranslateIt)
      ]
  ]
  where
    skip = SkipEdit (Qualified "Sample" "f")
    replacement = RocqAxiomDef (Qualified "Sample" "f", Qualid (Bare "nat"))
    redefine = RedefinitionEdit replacement
    axiom = AxiomatizeDefinitionEdit (Qualified "Sample" "f")
    moduleAxiom = AxiomatizeModuleEdit (mkModuleName "Sample")
    concrete = UnaxiomatizeDefinitionEdit (Qualified "Sample" "f")

programChecks :: [IO ()]
programChecks =
  [ checkBuilt ("useProgram: " ++ label) input expected (useProgram (Bare "loop"))
  | (label, input, expected) <-
      [ ("ordinary definition", [], False)
      , ("structural definition", [TerminationEdit (Bare "loop") (StructOrderTA (StructPos_ 1))], False)
      , ("deferred definition", [TerminationEdit (Bare "loop") Deferred], False)
      , ("corecursive definition", [TerminationEdit (Bare "loop") Corecursive], False)
      , ("measured definition", [TerminationEdit (Bare "loop")
          (WellFoundedTA (MeasureOrder_ (Qualid (Bare "size")) Nothing))], True)
      , ("well-founded definition", [TerminationEdit (Bare "loop")
          (WellFoundedTA (WFOrder_ (Qualid (Bare "lt")) (Bare "n")))], True)
      , ("obligations without termination", [ObligationsEdit (Bare "loop") "auto"], True)
      , ("definition-local well-founded helper", [InEdit (Bare "loop")
          (TerminationEdit (Bare "helper") (WellFoundedTA (MeasureOrder_ (Qualid (Bare "size")) Nothing)))], True)
      , ("another definition's local helper", [InEdit (Bare "other")
          (TerminationEdit (Bare "helper") (WellFoundedTA (MeasureOrder_ (Qualid (Bare "size")) Nothing)))], False)
      ]
  ]

main :: IO ()
main = do
  let checks =
        [ assertEqual label (Right [expected]) (parseWith parseEditList (source <> "\n"))
        | (label, source, expected) <- grammarCases ++ grammarBranchCases
        ] ++
        [ assertEqual "grammar inventory covers all 42 Edit constructors" 42
            (S.size (S.fromList [editKind expected | (_, _, expected) <- grammarCases]))
        ] ++
        [ assertEqual label (Right [RedefinitionEdit expected])
            (parseWith parseEditList ("redefine " <> source <> "\n"))
        | (label, source, expected) <- definitionCases
        ] ++
        [ assertEqual label (Right expected) (parseWith parseTerm source)
        | (label, source, expected) <- termCases
        ] ++ aliasChecks ++ rejectionChecks ++
        [ assertEqual ("duplicate " ++ label ++ " diagnostic") (Left expected) (buildEdits [first, second])
        | (label, first, second, expected) <- duplicateCases
        ] ++ mappingChecks ++ additionChecks ++ scopeChecks ++ exceptChecks ++ mergeChecks ++ rewriteChecks
          ++ definitionKeyChecks ++ invariantChecks ++ taskChecks ++ programChecks
  sequence_ checks
  putStrLn ("Edits checks passed (" ++ show (length checks) ++ " assertions).")
