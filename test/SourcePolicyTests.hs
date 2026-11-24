module SourcePolicyTests (runSourcePolicyTests) where

import Control.Exception (bracket)
import Control.Monad (unless)
import Data.List (isInfixOf)
import System.Directory
  ( createDirectory, getTemporaryDirectory, removeDirectoryRecursive, removeFile )
import System.Exit (die)
import System.FilePath ((</>))
import System.IO (hClose, openTempFile)

import SourcePolicy (runPolicy)

-- All tests exercise the public invocation boundary with real files. Parsing,
-- configuration building, scope handling, and diagnostics are production code.
data Expected = Accept | Reject FilePath [String]

withFixture :: (FilePath -> IO a) -> IO a
withFixture = bracket prepare removeDirectoryRecursive
  where
    prepare = do
      tmp <- getTemporaryDirectory
      (dir, handle) <- openTempFile tmp "source-policy-tests"
      hClose handle
      removeFile dir
      createDirectory dir
      pure dir

approval :: String
approval = "Data.PriorityQueue.FingerTree.minViewWithKey"

policy :: [(FilePath, String)] -> String
policy pins = unlines
  [ "approved-redefinitions:"
  , "  " ++ approval ++ ": ASSUMPTIONS.md#approved-translation-exception-minviewwithkey"
  , if null pins then "rewrites: {}" else "rewrites:"
  ] ++ concat ["  " ++ file ++ ": |\n" ++ unlines ["    " ++ line | line <- lines source]
              | (file, source) <- pins]

requiredNames :: String
requiredNames = unlines
  [ "Data.FingerTree.Eq___FingerTree", "Data.FingerTree.Eq___FingerTree_op_zeze__"
  , "Data.FingerTree.FingerTree", "Data.FingerTree.union", "Data.FingerTree.consTree"
  , approval, "Data.PriorityQueue.FingerTree.Ord__PQueue"
  ]

fixture :: String -> String -> [(FilePath, String)] -> [(FilePath, String)] -> Expected -> IO ()
fixture label config edits support = customFixture label config requiredNames edits support id

customFixture :: String -> String -> String -> [(FilePath, String)] -> [(FilePath, String)]
  -> ([String] -> [String]) -> Expected -> IO ()
customFixture label config required edits support arguments expected = withFixture $ \dir -> do
  let file = (dir </>)
  writeFile (file "source-policy.yaml") config
  writeFile (file "required.txt") required
  mapM_ (\(path, text) -> writeFile (file path) text) (edits ++ support)
  result <- runPolicy (arguments (["--policy", file "source-policy.yaml", "--required", file "required.txt"]
    ++ concat [["--edits", file path] | (path, _) <- edits]
    ++ concat [["--support", file path] | (path, _) <- support]))
  case (expected, result) of
    (Accept, Right ()) -> pure ()
    (Accept, Left message) -> die (label ++ ": unexpectedly rejected\n" ++ message)
    (Reject path fragments, Left message) ->
      unless (any (\line -> all (`isInfixOf` line) ([file path | not (null path)] ++ fragments)) (lines message)) $
        die (label ++ ": expected one diagnostic containing " ++ show (file path : fragments) ++ "\n" ++ message)
    (Reject _ _, Right ()) -> die (label ++ ": unexpectedly accepted")

badEdit :: String -> String -> String -> String -> IO ()
badEdit label source target violation = fixture label (policy []) [("owned.edits", source ++ "\n")] []
  (Reject "owned.edits" [target, violation])

goodEdit :: String -> String -> IO ()
goodEdit label source = fixture label (policy []) [("owned.edits", source ++ "\n")] [] Accept

badSupport :: String -> String -> String -> String -> IO ()
badSupport label source target violation = fixture label (policy []) [] [("midamble.v", source)]
  (Reject "midamble.v" [target, violation])

redefinitionCases :: [IO ()]
redefinitionCases =
  [ badEdit label (prefix ++ "redefine Definition " ++ target ++ " := 0.") target "not approved"
  | (label, prefix, target) <-
      [ ("top-level operation replacement", "", "Data.FingerTree.union")
      , ("scoped operation replacement", "in Data.FingerTree.outer ", "Data.FingerTree.union")
      , ("except replacement", "except in Data.FingerTree.keep ", "Data.FingerTree.union")
      , ("nested in/except replacement", "in Data.FingerTree.outer except in Data.FingerTree.keep ", "Data.FingerTree.union")
      , ("nested except/in replacement", "except in Data.FingerTree.keep in Data.FingerTree.outer ", "Data.FingerTree.union")
      , ("helper redefinitions also need approval", "", "Support.helper")
      , ("bare approved spelling is not a qualified approval", "", "minViewWithKey")
      ]
  ] ++
  [ goodEdit "approved ordinary definition" ("redefine Definition " ++ approval ++ " := 0.")
  , badEdit "aliases expand before policy"
      "alias module FT Data.FingerTree\nin FT.outer redefine Definition FT.union := 0."
      "Data.FingerTree.union" "not approved"
  , goodEdit "approved alias" ("alias module PQ Data.PriorityQueue.FingerTree\nredefine Definition PQ.minViewWithKey := 0.")
  , goodEdit "approved scoped definition" ("in Data.PriorityQueue.FingerTree.outer redefine Definition " ++ approval ++ " := 0.")
  , badEdit "skip cannot authorize a replacement"
      "skip Data.FingerTree.union\nredefine Definition Data.FingerTree.union := 0."
      "Data.FingerTree.union" "not approved"
  , badEdit "approved target cannot become an axiom" ("redefine Axiom " ++ approval ++ " : nat.")
      approval "not approved"
  , badEdit "mutual replacement cannot hide a second target"
      ("redefine Fixpoint " ++ approval ++ " (n : nat) : nat := n with Data.FingerTree.union (n : nat) : nat := n.")
      "Data.FingerTree.union" "not approved"
  , fixture "aliases reset for each file" (policy [])
      [("alias.edits", "alias module PQ Data.PriorityQueue.FingerTree\n"),
       ("owned.edits", "redefine Definition PQ.minViewWithKey := 0.\n")] []
      (Reject "owned.edits" ["PQ.minViewWithKey", "not approved"])
  , fixture "cross-file provenance" (policy [])
      [("innocent.edits", "skip Support.unused\n"),
       ("owned.edits", "redefine Definition Data.FingerTree.union := 0.\n")] []
      (Reject "owned.edits" ["Data.FingerTree.union", "not approved"])
  , fixture "shadowed scoped replacement is still rejected" (policy [])
      [("first.edits", "in Data.FingerTree.outer skip Support.unused\n"),
       ("owned.edits", "in Data.FingerTree.outer redefine Definition Data.FingerTree.union := 0.\n")] []
      (Reject "owned.edits" ["Data.FingerTree.union", "not approved"])
  ]

axiomCases :: [IO ()]
axiomCases =
  [ badEdit label source target "axiomatization is not approved"
  | (label, source, target) <-
      [ ("definition axiomatization", "axiomatize definition Data.FingerTree.union", "Data.FingerTree.union")
      , ("module axiomatization", "axiomatize module Data.FingerTree", "Data.FingerTree")
      , ("original module axiomatization", "axiomatize original module name Data.FingerTree", "Data.FingerTree")
      , ("scoped axiom", "in Data.FingerTree.outer axiomatize definition Data.FingerTree.union", "Data.FingerTree.union")
      , ("except original module axiom", "except in Data.FingerTree.keep axiomatize original module name Data.FingerTree", "Data.FingerTree")
      , ("aliased module axiom", "alias module FT Data.FingerTree\naxiomatize module FT", "Data.FingerTree")
      , ("unaxiomatize does not authorize", "unaxiomatize definition Data.FingerTree.union\naxiomatize definition Data.FingerTree.union", "Data.FingerTree.union")
      ]
  ] ++
  [ badEdit ("helper axiom addition: " ++ prefix) (prefix ++ "Axiom rogue : nat.") "rogue" "Axiom/assumption"
  | prefix <- ["add Data.FingerTree ", "add type Data.FingerTree ",
      "in Data.FingerTree.outer add Data.FingerTree ", "except in Data.FingerTree.keep add type Data.FingerTree "]
  ]
  ++ [fixture "shadowed scoped axiomatization is still rejected" (policy [])
        [("first.edits", "in Data.FingerTree.outer skip Support.unused\n"),
         ("owned.edits", "in Data.FingerTree.outer axiomatize module Data.FingerTree\n")] []
        (Reject "owned.edits" ["Data.FingerTree", "axiomatization is not approved"])]

additionCases :: [IO ()]
additionCases =
  [ badEdit label source "Eq___FingerTree" "required generated declaration"
  | (label, source) <-
      [ ("dictionary addition", "add Data.FingerTree Definition Eq___FingerTree := helper.")
      , ("type-phase dictionary addition", "add type Data.FingerTree Definition Eq___FingerTree := helper.")
      , ("scoped dictionary addition", "in Data.FingerTree.outer add Data.FingerTree Instance Eq___FingerTree : Class := helper.")
      , ("except dictionary addition", "except in Data.FingerTree.keep add Data.FingerTree Definition Eq___FingerTree := helper.")
      , ("aliased qualified dictionary addition", "alias module FT Data.FingerTree\nadd FT Definition FT.Eq___FingerTree := helper.")
      , ("generated method addition", "add Data.FingerTree Definition Eq___FingerTree_op_zeze__ := helper.")
      , ("constructor cannot supply dictionary", "add type Data.FingerTree Inductive Helper := Eq___FingerTree.")
      , ("mutual addition cannot hide dictionary", "add Data.FingerTree Fixpoint helper (n : nat) := n with Eq___FingerTree (n : nat) := n.")
      , ("lemma cannot supply dictionary", "add Data.FingerTree Lemma Eq___FingerTree : True. Proof. exact I. Qed.")
      ]
  ] ++
  [ badEdit "algorithm addition" "add Data.FingerTree Definition union := helper." "Data.FingerTree.union" "required generated declaration"
  , badEdit "approved redefine is not an addition approval"
      ("add Data.PriorityQueue.FingerTree Definition " ++ approval ++ " := helper.") approval "required generated declaration"
  , badEdit "invariant-generated additions also obey policy"
      "add invariant {module = Data.FingerTree, qid = Data.FingerTree.FingerTree, tyVars = [], constructor = Empty, useSigmaType = [Data.FingerTree.union], invariant = Definition Data.FingerTree.valid (x : Data.FingerTree.FingerTree) : Prop := True.}"
      "Data.FingerTree.FingerTree" "required generated declaration"
  , goodEdit "constructive Default, measure, and proof helpers" (unlines
      [ "add Data.FingerTree Instance DefaultTree : Default Data.FingerTree.FingerTree := helper."
      , "add type Data.FingerTree Definition size_measure (n : nat) := n."
      , "add Data.FingerTree Lemma helper_ok : True. Proof. exact I. Qed."
      ])
  , goodEdit "edit comment and string mentions" (unlines
      [ "# redefine Definition Data.FingerTree.union := 0."
      , "# axiomatize module Data.FingerTree"
      , "add Data.FingerTree Definition note := \"Axiom Eq___FingerTree. redefine Definition Data.FingerTree.union := 0.\"."
      , "add Data.FingerTree Lemma helper_ok : True. Proof. idtac \"Definition Eq___FingerTree\". exact I. Qed."
      ])
  , fixture "shadowed module additions are still checked" (policy [])
      [("first.edits", "add Data.FingerTree Definition helper := 0.\n"),
       ("owned.edits", "add Data.FingerTree Definition Eq___FingerTree := helper.\n")] []
      (Reject "owned.edits" ["Eq___FingerTree", "required generated declaration"])
  ]

renameCases :: [IO ()]
renameCases =
  [ fixture label (policy []) [("rename.edits", renaming ++ "\n"), ("owned.edits", addition ++ "\n")] []
      (Reject "owned.edits" [target, "required generated declaration"])
  | (label, renaming, addition, target) <-
      [ ("renamed addition", "rename value Data.FingerTree.union = Support.manualUnion",
          "add Support Definition manualUnion := 0.", "Support.manualUnion")
      , ("renamed source spelling", "rename value Support.manualUnion = Data.FingerTree.union",
          "add Support Definition manualUnion := 0.", "Support.manualUnion")
      , ("scoped rename cannot hide addition", "in Data.FingerTree.outer rename value Data.FingerTree.union = Support.manualUnion",
          "add Support Definition manualUnion := 0.", "Support.manualUnion")
      , ("except rename cannot hide addition", "except in Data.FingerTree.keep rename value Data.FingerTree.union = Support.manualUnion",
          "add type Support Definition manualUnion := 0.", "Support.manualUnion")
      , ("module renamed addition", "rename module Data.FingerTree Support",
          "add Support Definition Eq___FingerTree := 0.", "Support.Eq___FingerTree")
      , ("rename chain", "rename value Data.FingerTree.union = Support.first\nrename value Support.first = Support.last",
          "add Support Definition last := 0.", "Support.last")
      , ("bare rename spelling", "rename value Data.FingerTree.union = hidden",
          "add Data.FingerTree Definition hidden := 0.", "Data.FingerTree.hidden")
      , ("bare rename source", "rename value union = Support.manualUnion",
          "add Support Definition manualUnion := 0.", "Support.manualUnion")
      , ("cyclic protected rename stays bounded", "rename value Data.FingerTree.union = Support.cycle\nrename value Support.cycle = Data.FingerTree.union",
          "add Support Definition cycle := 0.", "Support.cycle")
      ]
  ] ++
  [ fixture label (policy []) [("rename.edits", renaming ++ "\n"),
      ("owned.edits", "redefine Definition " ++ approval ++ " := 0.\n")] []
      (Reject "rename.edits" [target, "renaming touches an approved redefinition"])
  | (label, renaming, target) <-
      [ ("approved-target hijack", "rename value Data.FingerTree.union = " ++ approval, "Data.FingerTree.union")
      , ("scoped approved-target hijack", "in Data.FingerTree.outer rename value Data.FingerTree.union = " ++ approval, "Data.FingerTree.union")
      , ("except approved-target hijack", "except in Data.FingerTree.keep rename value Data.FingerTree.union = " ++ approval, "Data.FingerTree.union")
      , ("approved source renamed away", "rename value " ++ approval ++ " = Support.hidden", approval)
      , ("approved module renamed away", "rename module Data.PriorityQueue.FingerTree Support", "Data.PriorityQueue.FingerTree")
      , ("approved module hijack", "rename module Support Data.PriorityQueue.FingerTree", "Support")
      ]
  ] ++
  [ goodEdit "ordinary current operator renames pass"
      "rename value Data.FingerTree.<| = Data.FingerTree.consTree\nrename value Data.FingerTree.|> = Data.FingerTree.snocTree"
  , goodEdit "approved self rename has no hijack"
      ("rename value " ++ approval ++ " = " ++ approval ++ "\nredefine Definition " ++ approval ++ " := 0.")
  , fixture "raw declaration renamed across files" (policy [])
      [("rename.edits", "rename value Data.FingerTree.union = Support.hidden\n")] [("midamble.v", "Definition hidden := 0.")]
      (Reject "midamble.v" ["hidden", "required generated declaration"])
  ]

rawCases :: [IO ()]
rawCases =
  [ badSupport ("raw " ++ keyword) (prefix ++ keyword ++ "\n Eq___FingerTree " ++ body)
      "Eq___FingerTree" "required generated declaration"
  | (keyword, body) <-
      [ ("Definition", ":= 0."), ("Let", ":= 0."), ("Instance", ": Class := helper.")
      , ("Fixpoint", "(n : nat) : nat := n."), ("CoFixpoint", "(n : nat) : Stream := helper n.")
      , ("Lemma", ": True. Proof. exact I. Qed."), ("Theorem", ": True. Proof. exact I. Qed.")
      , ("Remark", ": True. Proof. exact I. Qed."), ("Fact", ": True. Proof. exact I. Qed.")
      , ("Corollary", ": True. Proof. exact I. Qed."), ("Proposition", ": True. Proof. exact I. Qed.")
      , ("Example", ": True. Proof. exact I. Qed."), ("Inductive", ": Type := C.")
      , ("CoInductive", ": Type := C."), ("Variant", ": Type := C.")
      , ("Record", ": Type := { f : nat }."), ("Structure", ": Type := { f : nat }.")
      , ("Class", ": Type := { f : nat }."), ("Axiom", ": nat."), ("Parameter", ": nat.")
      , ("Hypothesis", ": nat.")
      ]
  , prefix <- ["", "#[local]\nProgram "]
  ] ++
  [ badSupport label source target violation
  | (label, source, target, violation) <-
      [ ("same-line boundary", "Definition ok := 0. Definition union := 0.", "union", "required generated declaration")
      , ("multiline attributes and comments", "#[local, universes(polymorphic)]\nProgram (* nested (* Definition hidden *) comment *)\nDefinition\n Eq___FingerTree := helper.", "Eq___FingerTree", "required generated declaration")
      , ("qualified declaration", "Local Definition Data.FingerTree.union := 0.", "Data.FingerTree.union", "required generated declaration")
      , ("spaced qualified path", "Definition Data .FingerTree .union := 0.", "Data.FingerTree.union", "required generated declaration")
      , ("universe prefixes", "Polymorphic Cumulative Definition union := 0.", "union", "required generated declaration")
      , ("raw method", "Definition Eq___FingerTree_op_zeze__ := helper.", "Eq___FingerTree_op_zeze__", "required generated declaration")
      , ("mutual fixpoint", "Fixpoint safe (n : nat) := n with union (n : nat) := n.", "union", "required generated declaration")
      , ("inductive constructor", "Inductive safe := Eq___FingerTree : safe.", "Eq___FingerTree", "required generated declaration")
      , ("record constructor", "Record safe := Eq___FingerTree { f : nat }.", "Eq___FingerTree", "required generated declaration")
      , ("record field", "Record safe := { f : nat; Eq___FingerTree : nat }.", "Eq___FingerTree", "required generated declaration")
      , ("class field", "Class safe := { Eq___FingerTree : nat }.", "Eq___FingerTree", "required generated declaration")
      , ("second assumption", "Variables safe Eq___FingerTree : nat.", "Eq___FingerTree", "required generated declaration")
      , ("grouped assumption", "Parameters (safe : nat) (Eq___FingerTree : nat).", "Eq___FingerTree", "required generated declaration")
      , ("helper Axiom", "Axiom rogue : nat.", "rogue", "not approved")
      , ("helper Axioms", "Axioms first rogue : nat.", "rogue", "not approved")
      , ("helper Parameter", "Parameter rogue : nat.", "rogue", "not approved")
      , ("helper Conjecture", "Conjecture rogue : nat.", "rogue", "not approved")
      ]
  ] ++
  [ fixture "raw comments, strings, references, and constructive helpers pass" (policy []) []
      [("midamble.v", unlines
        [ "(* Definition Eq___FingerTree := 0. (* Axiom rogue : nat. *) *)"
        , "#[local] Instance DefaultTree : Default Tree := {| default := Empty |}."
        , "Definition size_measure (n : nat) := n."
        , "Definition note := \"Definition Eq___FingerTree. \"\"Axiom rogue : nat.\"\"\"."
        , "Definition reference := Data.FingerTree.union."
        , "Check Data.FingerTree.Eq___FingerTree."
        , "Fixpoint measure (n : nat) := match n with O => Data.FingerTree.union | S m => measure m end."
        , "Inductive helper := C : Data.FingerTree.FingerTree -> helper."
        , "Record helper2 := { safe : Data.FingerTree.FingerTree }."
        , "Lemma helper_ok : True. Proof. idtac \"Definition Eq___FingerTree\". exact I. Qed."
        ])] Accept
  , fixture "record/class fields are not type references" (policy []) []
      [("midamble.v", "Record safe (n := Data.FingerTree.union) := { field : nat }. Class helper := Data.FingerTree.FingerTree.")]
      Accept
  , fixture "doubled quotes do not hide following declaration" (policy []) []
      [("midamble.v", "Definition note := \"\"\"Definition safe.\"\"\". Definition union := 0.")]
      (Reject "midamble.v" ["union", "required generated declaration"])
  , fixture "projection does not hide next command" (policy []) []
      [("midamble.v", "Definition safe := record.(field). Definition union := 0.")]
      (Reject "midamble.v" ["union", "required generated declaration"])
  , fixture "masked lines remain in diagnostic" (policy []) []
      [("preamble.v", "(* comment\n nested (* x *)\n*)\nDefinition\n union := 0.\n")]
      (Reject "preamble.v" [":5:", "union", "required generated declaration"])
  , badSupport "unterminated comment fails closed" "(* Definition union := 0." "" "unterminated Rocq comment"
  , badSupport "unterminated string fails closed" "Definition note := \"oops" "" "unterminated Rocq string"
  ]

quotedCommentCases :: [IO ()]
quotedCommentCases =
  [ fixture "quoted comment delimiters do not hide an Axiom" (policy []) []
      [("midamble.v", "(* \"*)\" *)\nAxiom hidden_assumption : False.\n(* \"(*\" *)\n")]
      (Reject "midamble.v" [":2:", "hidden_assumption", "Axiom/Parameter/Conjecture declarations are not approved"])
  ] ++
  [ fixture (label ++ " before " ++ keyword) (policy []) []
      [("midamble.v", comment ++ keyword ++ " " ++ target ++ body ++ "\n")]
      (Reject "midamble.v" [":2:", target, violation])
  | (label, comment) <- comments
  , (keyword, target, body, violation) <-
      [ ("Definition", "union", " : nat := 0.", "required generated declaration")
      , ("Axiom", "hidden_assumption", " : False.", "Axiom/Parameter/Conjecture declarations are not approved")
      , ("Parameter", "hidden_assumption", " : False.", "Axiom/Parameter/Conjecture declarations are not approved")
      , ("Conjecture", "hidden_assumption", " : False.", "Axiom/Parameter/Conjecture declarations are not approved")
      ]
  ] ++
  [ fixture (label ++ " in harmless documentation") (policy []) []
      [("midamble.v", comment ++ "Definition harmless : nat := 0.\n")] Accept
  | (label, comment) <- comments
  ] ++
  [ fixture "quoted documentation mentions are ignored" (policy []) []
      [("midamble.v", unlines
        [ "(* \"Definition union := 0. Axiom hidden_assumption : False. *)\""
        , "   (* \"Parameter secret : False. (*\" *)"
        , "   \"Conjecture doubled\"\"quote : False.\" *)"
        , "Definition harmless : nat := 0."
        ])] Accept
  , fixture "multiline quoted comments retain declaration line numbers" (policy []) []
      [("preamble.v", unlines
        [ "(* documentation"
        , " \"*)"
        , " (*"
        , " \""
        , " (* nested \"*)\" *)"
        , "*)"
        , "Definition"
        , " union : nat := 0."
        ])]
      (Reject "preamble.v" [":8:", "union", "required generated declaration"])
  ] ++
  [ fixture label (policy []) [] [("midamble.v", source)] (Reject "midamble.v" [diagnostic])
  | (label, source, diagnostic) <-
      [ ("unterminated comment after quoted closing delimiter", "\n(* \"*)\"\n", ": 2: unterminated Rocq comment")
      , ("unterminated outer comment after nested quoted delimiter", "\n(* outer\n (* \"(*\" *)\n", ": 2: unterminated Rocq comment")
      , ("unterminated string after quoted comment", "(* \"*)\" *)\n\nDefinition note := \"oops", ": 3: unterminated Rocq string")
      , ("unterminated string inside comment fails closed", "\n(* documentation\n \"*)\n*)\n", ": 3: unterminated Rocq string")
      ]
  ]
  where
    comments =
      [ ("quoted closing delimiter", "(* \"*)\" *)\n")
      , ("quoted opening delimiter", "(* \"(*\" *)\n")
      , ("quoted opening and closing delimiters", "(* \"(* and *)\" *)\n")
      , ("nested quoted delimiters", "(* outer (* \"*)\" \"(*\" *) tail \"*)\" *)\n")
      , ("doubled quotes in comment", "(* \"\"\"*)\"\" and \"\"(*\"\"\" *)\n")
      ]

rewriteCases :: [IO ()]
rewriteCases =
  [ badEdit "new rewrite requires decision" rule "Data.FingerTree.union" "not pinned"
  , fixture "current pinned rewrite" pinned [("owned.edits", rule)] [] Accept
  , fixture "rewrite formatting is immaterial" pinned
      [("owned.edits", "# only syntax matters\nrewrite forall x , Data.FingerTree.union   x = Support.first x\n")] [] Accept
  , fixture "rewrite alias resolves to pinned rule" pinned
      [("owned.edits", "alias module FT Data.FingerTree\nrewrite forall x, FT.union x = Support.first x\n")] [] Accept
  , fixture "changed RHS" pinned [("owned.edits", changed)] []
      (Reject "owned.edits" ["Data.FingerTree.union", "changed", "not pinned"])
  , fixture "changed rewrite scope" pinned [("owned.edits", "in Data.FingerTree.outer " ++ rule)] []
      (Reject "owned.edits" ["in Data.FingerTree.outer", "Data.FingerTree.union", "not pinned"])
  , fixture "pinned rewrite removal" pinned [("owned.edits", "")] []
      (Reject "owned.edits" ["Data.FingerTree.union", "pinned rewrite is missing"])
  , fixture "duplicate rewrite" pinned [("owned.edits", rule ++ rule)] []
      (Reject "owned.edits" ["Data.FingerTree.union", "not pinned"])
  , fixture "rewrite order is pinned" (policy [("owned.edits", rule ++ second)])
      [("owned.edits", second ++ rule)] [] (Reject "owned.edits" ["rewrite", "reordered", "not pinned"])
  , fixture "rewrite order across files is pinned"
      (policy [("first.edits", rule), ("second.edits", second)])
      [("second.edits", second), ("first.edits", rule)] []
      (Reject "second.edits" ["rewrite", "input order"])
  , fixture "In/Except wrappers are pinned" (policy [("owned.edits", scoped)]) [("owned.edits", scoped)] [] Accept
  , fixture "changed Except exclusions" (policy [("owned.edits", scoped)])
      [("owned.edits", "in Data.FingerTree.outer except in Data.FingerTree.changed " ++ rule)] []
      (Reject "owned.edits" ["except in Data.FingerTree.changed", "Data.FingerTree.union", "not pinned"])
  , fixture "moving rewrite across files changes provenance" pinned
      [("owned.edits", ""), ("other.edits", rule)] []
      (Reject "other.edits" ["Data.FingerTree.union", "not pinned"])
  , fixture "shadowed scope cannot hide a changed rule" (policy [("first.edits", scoped), ("second.edits", scoped)])
      [("first.edits", scoped), ("second.edits", "in Data.FingerTree.outer except in Data.FingerTree.keep " ++ changed)] []
      (Reject "second.edits" ["Data.FingerTree.union", "not pinned"])
  , fixture "missing pinned input is rejected" pinned [] []
      (Reject "source-policy.yaml" ["missing pinned rewrite input", "owned.edits"])
  , fixture "policy pins use the actual edits parser" (policy [("owned.edits", "rewrite bad syntax\n")]) [] []
      (Reject "source-policy.yaml" ["rewrites[owned.edits]", "unexpected"])
  , fixture "policy cannot smuggle a redefine in a rewrite pin"
      (policy [("owned.edits", "redefine Definition Data.FingerTree.union := 0.\n")]) [] []
      (Reject "source-policy.yaml" ["rewrites[owned.edits]", "only rewrite rules"])
  ]
  where
    rule = "rewrite forall x, Data.FingerTree.union x = Support.first x\n"
    changed = "rewrite forall x, Data.FingerTree.union x = Support.other x\n"
    second = "rewrite forall x, Support.first x = Support.last x\n"
    scoped = "in Data.FingerTree.outer except in Data.FingerTree.keep " ++ rule
    pinned = policy [("owned.edits", rule)]

inputCases :: [IO ()]
inputCases =
  [ fixture "parse error has real filename" (policy []) [("broken.edits", "nonsense Data.FingerTree.union\n")] []
      (Reject "broken.edits" ["unexpected"])
  , fixture "buildEdits error has real filename" (policy [])
      [("broken.edits", "skip Data.FingerTree.union\nskip Data.FingerTree.union\n")] []
      (Reject "broken.edits" ["Duplicate", "Data.FingerTree.union"])
  , fixture "malformed YAML is rejected" "approved-redefinitions: [\n" [] []
      (Reject "source-policy.yaml" ["YAML"])
  , customFixture "required inventory must not be empty" (policy []) "\n" [] [] id
      (Reject "required.txt" ["inventory is empty"])
  , customFixture "required inventory must be qualified" (policy []) "union\n" [] [] id
      (Reject "required.txt" ["fully qualified", "union"])
  , customFixture "unknown option rejected" (policy []) requiredNames [] []
      (++ ["--unknown", "file"]) (Reject "" ["unknown option"])
  , customFixture "missing input has filename" (policy []) requiredNames [] []
      (\args -> args ++ ["--edits", last args ++ ".missing"]) (Reject "required.txt.missing" [])
  ]

runSourcePolicyTests :: IO ()
runSourcePolicyTests = do
  let checks = redefinitionCases ++ axiomCases ++ additionCases ++ renameCases ++ rawCases ++ quotedCommentCases ++ rewriteCases ++ inputCases
  sequence_ checks
  putStrLn ("Source policy checks passed (" ++ show (length checks) ++ " cases).")
