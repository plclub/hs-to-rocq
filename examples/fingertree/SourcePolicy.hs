{-# LANGUAGE OverloadedStrings #-}

-- | Bounded source-policy checks for finger-tree-owned guidance and support.
--
-- Each edits file (including each YAML rewrite block) uses the translator's
-- parser and buildEdits independently. Aliases are therefore file scoped. We
-- inspect every built in/except configuration, even shadowed ones. Renaming
-- checks conservatively combine all scopes/files: a replacement cannot hide
-- behind a rename that happens to be inactive in another scope. Renaming the
-- approved replacement or its module is deliberately unsupported and rejected
-- with an actionable diagnostic. Other renames expand the protected-name set.
-- Rewrite pins are per input file, relative to the policy file, and compare
-- parsed rules with their complete In/Except wrappers in source order. This
-- also preserves the builder's reversed per-file rule order and file boundaries.
-- Rewrite-bearing inputs must follow lexical policy-key order, so reordering
-- files cannot silently change cross-file rewrite precedence.
-- Pins are existing guidance, not approvals for additional algorithm bodies.
--
-- Raw support has a lexical declaration scan, not a Rocq parser. Nested comments
-- and strings (including doubled quotes) are masked, retaining whitespace and
-- line numbers. Command-start named Definition/Let/Instance, Fixpoint/CoFixpoint,
-- theorem varieties, Inductive/CoInductive/Variant, Record/Structure/Class, and
-- assumption headers are supported, with Program, locality, universe prefixes,
-- and #[...] attributes. Ordinary mutual heads, inductive constructors, and
-- record/class fields are checked too. Full stops distinguish qualified paths
-- and bracketed expressions; multiline and same-line commands both work.
-- Unqualified raw declarations conservatively match any protected local name.
-- This does not expand notation, Ltac, plugin commands, Include, or module
-- aliases, nor recognize arbitrary vernacular control wrappers. Such ways of
-- creating declarations need review and an explicit scanner extension. Bodies
-- are not parsed or checked for semantic equivalence or proof assumptions; the
-- existing exact assumption audit remains responsible for those dependencies.
module SourcePolicy (runPolicy) where

import Control.Monad (forM, unless)
import Control.Monad.Except (ExceptT(..), runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.Char (GeneralCategory(NonSpacingMark), generalCategory, isAlpha, isAlphaNum, isDigit, isSpace)
import Data.List (intercalate, nub)
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Yaml as Y
import System.Directory (canonicalizePath)
import System.FilePath ((</>), takeDirectory)
import System.IO.Error (tryIOError)

import HsToRocq.Edits.Parser (parseEditList, prettyParseError)
import HsToRocq.Edits.ParserState (runParser)
import HsToRocq.Edits.Types
  ( Edit(..), Edits(..), NamespacedIdent(..), RocqDefinition(..), Rewrite(..), buildEdits )
import qualified HsToRocq.Rocq.Gallina as G
import HsToRocq.Rocq.Gallina.Util (qualidToIdent)
import HsToRocq.Rocq.FreeVars (definedBy)
import HsToRocq.Rocq.Pretty (showP)
import HsToRocq.Util.GHC.Module (moduleNameString)

data Policy = Policy
  { approvedRedefinitions :: M.Map String String
  , pinnedRewrites :: M.Map FilePath T.Text
  }

instance Y.FromJSON Policy where
  parseJSON = Y.withObject "source policy" $ \o ->
    Policy <$> o Y..: "approved-redefinitions" <*> o Y..: "rewrites"

data Options = Options
  { policyFile :: FilePath
  , requiredFile :: FilePath
  , editFiles :: [FilePath]
  , supportFiles :: [FilePath]
  }

usage :: String
usage = "usage: check-source-policy.hs --policy PATH --required PATH"
  ++ " [--edits PATH ...] [--support PATH ...]"

options :: [String] -> Either String Options
options args = do
  flags <- pairs args
  policy <- single "--policy" flags
  required <- single "--required" flags
  pure (Options policy required (values "--edits" flags) (values "--support" flags))
  where
    values flag = map snd . filter ((== flag) . fst)
    single flag flags = case values flag flags of
      [file] -> Right file
      _ -> Left (flag ++ " is required exactly once\n" ++ usage)
    pairs [] = Right []
    pairs (flag:file:rest)
      | flag `elem` ["--policy", "--required", "--edits", "--support"]
      , not (null file), take 2 file /= "--" = ((flag, file) :) <$> pairs rest
    pairs (flag:_) = Left ("unknown option or missing path: " ++ flag ++ "\n" ++ usage)

data Input = Input FilePath FilePath [Edit] Edits

-- | Public invocation boundary. Failures include the actual input filename;
-- the thin Main turns Left into a nonzero exit. No compiler or generated base
-- is needed. Only the explicitly supplied owner inputs are inspected.
runPolicy :: [String] -> IO (Either String ())
runPolicy args = do
  result <- tryIOError (runExceptT check)
  pure (either (Left . show) id result)
  where
    check = do
      opts <- fromEither (options args)
      policy <- ExceptT $ fmap (either (Left . ((policyFile opts ++ ": ") ++) . Y.prettyPrintParseException) Right)
        (Y.decodeFileEither (policyFile opts))
      required <- liftIO (T.readFile (requiredFile opts)) >>= fromEither . readRequired (requiredFile opts)
      unless (all (\(name, anchor) -> qualifiedName name && not (all isSpace anchor))
        (M.toList (approvedRedefinitions policy))) $
        throwError (policyFile opts ++ ": approvals require qualified targets and nonempty decision anchors")
      inputs <- forM (editFiles opts) $ \file -> do
        source <- liftIO (T.readFile file)
        (edits, config) <- fromEither (parseConfig file source)
        absolute <- liftIO (canonicalizePath file)
        pure (Input file absolute edits config)
      pins <- forM (M.toList (pinnedRewrites policy)) $ \(relative, source) -> do
        let label = policyFile opts ++ ": rewrites[" ++ relative ++ "]"
        (edits, _) <- fromEither (parseConfig label source)
        unless (all pinDirective edits) $
          throwError (label ++ ": only rewrite rules, scope wrappers, and parser aliases belong in a rewrite pin")
        absolute <- liftIO (canonicalizePath (takeDirectory (policyFile opts) </> relative))
        pure (absolute, mapMaybe rewriteEdit edits)
      let scopes = [(file, scope, config') | Input file _ _ config <- inputs,
                      (scope, config') <- configurations [] config]
          renames = [(file, name (niId from), name to) |
                      (file, _, config) <- scopes, (from, to) <- M.toList (_renamings config)]
          modules = [(file, moduleNameString from, moduleNameString to) |
                      (file, _, config) <- scopes, (from, to) <- M.toList (_renamedModules config)]
          protected = expandNames renames modules required
          approved = M.keysSet (approvedRedefinitions policy)
          approvalVariants = expandNames renames modules approved
          errors = duplicateInputs inputs ++ checkPins (policyFile opts) pins inputs
            ++ checkApprovalRenames approvalVariants renames modules
            ++ concat [checkConfig approved protected file scope config | (file, scope, config) <- scopes]
      rawErrors <- forM (supportFiles opts) $ \file -> do
        source <- liftIO (T.readFile file)
        fromEither (checkSupport protected file (T.unpack source))
      case nub (errors ++ concat rawErrors) of
        [] -> pure ()
        messages -> throwError (unlines messages)

fromEither :: Either String a -> ExceptT String IO a
fromEither = either throwError pure

parseConfig :: FilePath -> T.Text -> Either String ([Edit], Edits)
parseConfig file source = do
  edits <- either (Left . unlines . map (prettyParseError file)) Right
    (runParser parseEditList source)
  config <- either (Left . ((file ++ ": ") ++)) Right (buildEdits edits)
  pure (edits, config)

name :: G.Qualid -> String
name = T.unpack . qualidToIdent

identifierStart :: Char -> Bool
identifierStart c = isAlpha c || c == '_' || c == '\160'

identifierContinue :: Char -> Bool
identifierContinue c = isAlphaNum c || c `elem` ['_', '\'', '\160'] || generalCategory c == NonSpacingMark

qualifiedName :: String -> Bool
qualifiedName text = case splitName text of
  (Just modName, base) -> all valid (splitDots modName ++ [base])
  _ -> False
  where
    valid (c:cs) = identifierStart c && all identifierContinue cs
    valid [] = False
    splitDots s = case break (== '.') s of
      (part, []) -> [part]
      (part, _:rest) -> part : splitDots rest

splitName :: String -> (Maybe String, String)
splitName text = case break (== '.') (reverse text) of
  (_, []) -> (Nothing, text)
  (base, _:modName) -> (Just (reverse modName), reverse base)

readRequired :: FilePath -> T.Text -> Either String (S.Set String)
readRequired file source
  | null names = Left (file ++ ": required generated-name inventory is empty")
  | otherwise = case filter (not . qualifiedName) names of
      bad:_ -> Left (file ++ ": expected fully qualified generated declaration: " ++ bad)
      [] -> Right (S.fromList names)
  where names = filter (not . null) (map (T.unpack . T.strip) (T.lines source))

configurations :: [String] -> Edits -> [([String], Edits)]
configurations scope config = (scope, config) : concat
  [ configurations (scope ++ [prefix ++ name target]) nested
  | (prefix, entries) <- [("in ", _inEdits config), ("except in ", _exceptInEdits config)]
  , (target, nested) <- M.toList entries
  ]

rewriteEdit :: Edit -> Maybe Edit
rewriteEdit edit@RewriteEdit{} = Just edit
rewriteEdit (InEdit target edit) = InEdit target <$> rewriteEdit edit
rewriteEdit (ExceptInEdit targets edit) = ExceptInEdit targets <$> rewriteEdit edit
rewriteEdit _ = Nothing

pinDirective :: Edit -> Bool
pinDirective RewriteEdit{} = True
pinDirective AliasModuleEdit{} = True
pinDirective (InEdit _ edit) = pinDirective edit
pinDirective (ExceptInEdit _ edit) = pinDirective edit
pinDirective _ = False

duplicateInputs :: [Input] -> [String]
duplicateInputs inputs = [file ++ ": edits input supplied more than once" |
  (i, Input file absolute _ _) <- zip [0 :: Int ..] inputs,
  any (\(Input _ other _ _) -> absolute == other) (take i inputs)]

checkPins :: FilePath -> [(FilePath, [Edit])] -> [Input] -> [String]
checkPins policy pins inputs = concatMap checkInput inputs ++ orderErrors ++
  [ policy ++ ": missing pinned rewrite input " ++ absolute
  | (absolute, _) <- pins, not (any (\(Input _ path _ _) -> path == absolute) inputs)]
  where
    activePaths = [path | (path, rules) <- pins, not (null rules)]
    orderedInputs = [input | input@(Input _ path _ _) <- inputs, path `elem` activePaths]
    orderErrors =
      [ file ++ ": rewrite input order differs from lexical policy-key order in " ++ policy
      | (expected, Input file actual _ _) <- zip activePaths orderedInputs, expected /= actual]
    checkInput (Input file absolute edits _) =
      mismatch file (mapMaybe rewriteEdit edits) (maybe [] id (lookup absolute pins))
    mismatch _ [] [] = []
    mismatch file (actual:as) (expected:es)
      | actual == expected = mismatch file as es
    mismatch file (actual:_) _ =
      [file ++ ": " ++ rewriteLabel actual ++ ": new, changed, or reordered rewrite is not pinned; deliberately update " ++ policy]
    mismatch file [] (expected:_) =
      [file ++ ": " ++ rewriteLabel expected ++ ": pinned rewrite is missing; deliberately update " ++ policy]

rewriteLabel :: Edit -> String
rewriteLabel (RewriteEdit (Rewrite _ lhs _)) = "rewrite " ++ showP lhs
rewriteLabel (InEdit target edit) = "in " ++ name target ++ " " ++ rewriteLabel edit
rewriteLabel (ExceptInEdit targets edit) = "except in " ++ intercalate ", " (map name (foldr (:) [] targets))
  ++ " " ++ rewriteLabel edit
rewriteLabel _ = "rewrite"

-- A finite, bidirectional closure: module substitutions match whole module
-- names, not prefixes. Bare renames conservatively also match local spellings.
expandNames :: [(FilePath, String, String)] -> [(FilePath, String, String)] -> S.Set String -> S.Set String
expandNames renames modules initial = go initial (S.toList initial)
  where
    go seen [] = seen
    go seen (current:rest) =
      let fresh = S.fromList (neighbors current) S.\\ seen
      in go (seen <> fresh) (S.toList fresh ++ rest)
    neighbors current = concat
      [ replace current from to ++ replace current to from | (_, from, to) <- renames] ++
      [ to ++ "." ++ base | (_, from, to) <- bothWays modules, let (modName, base) = splitName current,
                            modName == Just from]
    replace current from to
      | current == from || (fst (splitName from) == Nothing && snd (splitName current) == from) =
          to : [modName ++ "." ++ to | Just modName <- [fst (splitName current)], fst (splitName to) == Nothing]
      | otherwise = []
    bothWays triples = triples ++ [(file, to, from) | (file, from, to) <- triples]

checkApprovalRenames :: S.Set String -> [(FilePath, String, String)] -> [(FilePath, String, String)] -> [String]
checkApprovalRenames approved renames modules =
  [ problem file (from ++ " -> " ++ to)
  | (file, from, to) <- renames, from /= to, any (touches approved) [from, to]] ++
  [ problem file ("module " ++ from ++ " -> " ++ to)
  | (file, from, to) <- modules, from /= to,
    any (\target -> fst (splitName target) `elem` [Just from, Just to]) (S.toList approved)]
  where
    problem file target = file ++ ": " ++ target
      ++ ": renaming touches an approved redefinition; keep its original target/module spelling or deliberately update the policy/checker"

touches :: S.Set String -> String -> Bool
touches protected target = target `S.member` protected ||
  (fst (splitName target) == Nothing && any ((== target) . snd . splitName) (S.toList protected))

checkConfig :: S.Set String -> S.Set String -> FilePath -> [String] -> Edits -> [String]
checkConfig approved protected file scope config =
  [ problem target "redefinition is not approved"
  | def <- M.elems (_redefinitions config), target <- map name (definedBy def),
    target `S.notMember` approved || not (ordinaryDefinition def)] ++
  [ problem target "axiomatization is not approved"
  | target <- map name (S.toList (_axiomatizedDefinitions config))
      ++ map moduleNameString (S.toList (_axiomatizedModules config))
      ++ map moduleNameString (S.toList (_axiomatizedOriginalModuleNames config))] ++
  concat [checkAddition (moduleNameString owner) sentence
         | (owner, (types, terms)) <- M.toList (_additions config), sentence <- types ++ terms]
  where
    problem target violation = file ++ ": " ++ target ++ ": " ++ violation
      ++ if null scope then "" else " (" ++ intercalate "; " scope ++ ")"
    ordinaryDefinition (RocqDefinitionDef G.DefinitionDef{}) = True
    ordinaryDefinition _ = False
    qualify owner target = case target of
      G.Bare base -> owner ++ "." ++ T.unpack base
      _ -> name target
    checkAddition owner sentence =
      [ problem (qualify owner target) "Axiom/assumption additions are not approved"
      | assumption sentence, target <- definedBy sentence] ++
      [ problem (qualify owner target) "required generated declaration cannot be supplied by an addition"
      | target <- definedBy sentence,
        touches protected (qualify owner target) || name target `S.member` protected]
    assumption G.AssumptionSentence{} = True
    assumption (G.ProgramSentence sentence _) = assumption sentence
    assumption _ = False

checkSupport :: S.Set String -> FilePath -> String -> Either String [String]
checkSupport protected file source = do
  masked <- either (Left . ((file ++ ": ") ++)) Right (maskRocq source)
  pure
    [ file ++ ":" ++ show line ++ ": " ++ target ++ ": " ++ violation
    | command <- commands (tokens 1 masked)
    , (Token line target, isAssumption) <- declarations command
    , violation <- ["Axiom/Parameter/Conjecture declarations are not approved" | isAssumption]
        ++ ["required generated declaration cannot be supplied by handwritten support" | touches protected target]
    ]

data Mask = Code | Comment Int Int | Quoted Int Mask

maskRocq :: String -> Either String String
maskRocq = go Code 1
  where
    blank c = if isSpace c then c else ' '
    go Code _ [] = Right []
    go (Comment _ start) _ [] = Left (show start ++ ": unterminated Rocq comment")
    go (Quoted start _) _ [] = Left (show start ++ ": unterminated Rocq string")
    go Code line ('(':'*':rest) = ("  " ++) <$> go (Comment 1 line) line rest
    go Code line ('"':rest) = (' ' :) <$> go (Quoted line Code) line rest
    go state@Comment{} line ('"':rest) = (' ' :) <$> go (Quoted line state) line rest
    go (Comment depth start) line ('(':'*':rest) =
      ("  " ++) <$> go (Comment (depth + 1) start) line rest
    go (Comment depth start) line ('*':')':rest) =
      ("  " ++) <$> go (if depth == 1 then Code else Comment (depth - 1) start) line rest
    go state@(Quoted _ _) line ('"':'"':rest) = ("  " ++) <$> go state line rest
    go (Quoted _ outer) line ('"':rest) = (' ' :) <$> go outer line rest
    go state line (c:rest) = ((case state of Code -> c; _ -> blank c) :) <$>
      go state (if c == '\n' then line + 1 else line) rest

data Token = Token Int String deriving (Eq, Show)

tokenText :: Token -> String
tokenText (Token _ text) = text

isNameToken :: Token -> Bool
isNameToken (Token _ (c:cs)) = identifierStart c && all (\x -> identifierContinue x || x == '.') cs
isNameToken _ = False

tokens :: Int -> String -> [Token]
tokens _ [] = []
tokens line (c:rest)
  | isSpace c = tokens (if c == '\n' then line + 1 else line) rest
  | identifierStart c =
      let (base, after) = span identifierContinue rest
          (text, consumed, remaining) = path (c:base) after
      in Token line text : tokens (line + length (filter (== '\n') consumed)) remaining
  | isDigit c = let (digits, after) = span isDigit rest in case after of
      '.':d:more | isDigit d -> let (fraction, remaining) = span isDigit more in
        Token line (c:digits ++ "." ++ d:fraction) : tokens line remaining
      _ -> Token line (c:digits) : tokens line after
  | c == '.', '(':more <- rest = Token line ".(" : tokens line more
  | c == '.' = let (dots, after) = span (== '.') rest in
      Token line (c:dots) : tokens line after
  | (c:take 1 rest) `elem` [":=", ":>", "=>", "->"] =
      Token line (c:take 1 rest) : tokens line (drop 1 rest)
  | otherwise = Token line [c] : tokens line rest
  where
    path base after =
      let (spaces, next) = span isSpace after in case next of
        '.':d:more | identifierStart d ->
          let (component, following) = span identifierContinue more
              (text, consumed, remaining) = path (base ++ "." ++ d:component) following
          in (text, spaces ++ "." ++ d:component ++ consumed, remaining)
        _ -> (base, "", after)

-- Only full stops outside delimiters end commands. Projection .( opens a
-- delimiter, and runs of dots are notation tokens rather than command ends.
commands :: [Token] -> [[Token]]
commands = go [] []
  where
    go acc _ [] = [reverse acc | not (null acc)]
    go acc stack (token:rest)
      | tokenText token == ".", null stack = reverse acc : go [] [] rest
      | otherwise = go (token:acc) (delimiters stack (tokenText token)) rest

delimiters :: [String] -> String -> [String]
delimiters stack text = case text of
  "(" -> ")" : stack
  ".(" -> ")" : stack
  "[" -> "]" : stack
  "{" -> "}" : stack
  _ | text `elem` [")", "]", "}"], next:rest <- stack, text == next -> rest
  _ -> stack

stripPrefixes :: [Token] -> [Token]
stripPrefixes (hash:open:rest) | tokenText hash == "#", tokenText open == "[" =
  stripPrefixes (afterGroup "]" rest)
stripPrefixes (token:rest) | tokenText token `elem`
  ["Local", "Global", "Export", "Program", "Polymorphic", "Monomorphic", "Cumulative", "NonCumulative", "Private"] =
    stripPrefixes rest
stripPrefixes rest = rest

afterGroup :: String -> [Token] -> [Token]
afterGroup close = go [close]
  where
    go _ [] = []
    go stack (token:rest) = case delimiters stack (tokenText token) of
      [] -> rest
      next -> go next rest

declarations :: [Token] -> [(Token, Bool)]
declarations input = case stripPrefixes input of
  keyword:rest
    | kind `elem` assumptions -> [(target, kind `elem` globalAssumptions) | target <- assumptionNames rest]
    | kind `elem` named, target:_ <- rest, isNameToken target ->
        (target, False) : [(extra, False) | extra <- extras kind rest]
    where kind = tokenText keyword
  _ -> []
  where
    globalAssumptions = ["Axiom", "Axioms", "Parameter", "Parameters", "Conjecture", "Conjectures"]
    assumptions = globalAssumptions ++ ["Variable", "Variables", "Hypothesis", "Hypotheses"]
    named = ["Definition", "Let", "Instance", "Fixpoint", "CoFixpoint", "Theorem", "Lemma", "Remark", "Fact",
      "Corollary", "Proposition", "Example", "Inductive", "CoInductive", "Variant", "Record", "Structure", "Class"]
    extras kind rest
      | kind `elem` ["Record", "Structure", "Class"] = recordNames rest
      | kind `elem` ["Fixpoint", "CoFixpoint", "Inductive", "CoInductive", "Variant"] =
          let top = topLevel rest in
          [target | (marker, target) <- zip top (drop 1 top), tokenText marker == "with", isNameToken target] ++
          [target | kind `elem` ["Inductive", "CoInductive", "Variant"],
            (marker, target) <- zip top (drop 1 top), tokenText marker `elem` [":=", "|"], isNameToken target]
      | otherwise = []

assumptionNames :: [Token] -> [Token]
assumptionNames (open:rest) | tokenText open == "(" =
  takeWhile isNameToken rest ++ assumptionNames (afterGroup ")" rest)
assumptionNames rest = takeWhile isNameToken rest

-- Restrict mutual/constructor markers to the outer syntax, excluding match,
-- local let, and bracketed bodies. This is not general term parsing.
topLevel :: [Token] -> [Token]
topLevel = go []
  where
    go _ [] = []
    go stack (token:rest)
      | text `elem` ["match", "lazymatch", "multimatch", "let"] =
          go ((if text == "let" then "in" else "end") : stack) rest
      | next:more <- stack, text == next = go more rest
      | otherwise = [token | null stack] ++ go (delimiters stack text) rest
      where text = tokenText token

recordNames :: [Token] -> [Token]
recordNames input = case afterAssignment [] input of
  constructor:open:fields | isNameToken constructor, tokenText open == "{" ->
    constructor : mapMaybe fieldName (splitFields fields)
  open:fields | tokenText open == "{" -> mapMaybe fieldName (splitFields fields)
  field:colon:_ | isNameToken field, tokenText colon `elem` [":", ":>"] -> [field]
  _ -> []
  where
    afterAssignment _ [] = []
    afterAssignment stack (token:rest)
      | null stack, tokenText token == ":=" = rest
      | otherwise = afterAssignment (delimiters stack (tokenText token)) rest
    fieldName fields = case stripPrefixes fields of
      target:_ | isNameToken target -> Just target
      _ -> Nothing
    splitFields = go [] []
    go acc _ [] = [reverse acc]
    go acc stack (token:rest)
      | null stack, tokenText token == ";" = reverse acc : go [] [] rest
      | null stack, tokenText token == "}" = [reverse acc]
      | otherwise = go (token:acc) (delimiters stack (tokenText token)) rest
