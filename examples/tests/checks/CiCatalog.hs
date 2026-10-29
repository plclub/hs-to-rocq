{-# LANGUAGE OverloadedStrings #-}

-- Run from the repository root; yaml is already a translator dependency.
-- stack exec -- runghc -package=yaml examples/tests/checks/CiCatalog.hs --self-test
module Main (main) where

import Control.Exception (bracket)
import Control.Monad (forM, forM_, unless)
import Data.Char (isSpace)
import Data.List (group, isInfixOf, isPrefixOf, sort, stripPrefix)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Yaml as Yaml
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import System.Directory (findExecutable, getTemporaryDirectory, removeFile)
import System.Environment (getArgs)
import System.Exit (ExitCode(..), die)
import System.IO (hClose, hPutStr, openTempFile)
import System.IO.Error (catchIOError)
import System.Process (readProcessWithExitCode)

type Settings = Map.Map String Yaml.Value
data Job = Job { needs :: [String], steps :: [Settings], settings :: Settings }
newtype Workflow = Workflow (Map.Map String Job)

instance Yaml.FromJSON Workflow where
  parseJSON = Yaml.withObject "workflow" $ \o -> Workflow <$> o Yaml..: "jobs"

instance Yaml.FromJSON Job where
  parseJSON value = do
    fields <- Yaml.parseJSON value
    dependencies <- case Map.lookup "needs" fields of
      Nothing -> pure []
      Just (Yaml.String name) -> pure [Text.unpack name]
      Just names -> Yaml.parseJSON names
    commands <- maybe (pure []) Yaml.parseJSON (Map.lookup "steps" fields)
    pure (Job dependencies commands fields)

workflowPath, catalogPath, fixPath, guardCommand :: String
workflowPath = ".github/workflows/hs-to-rocq.yml"
catalogPath = ".claude/commands/ci.md"
fixPath = ".claude/commands/ci-fix.md"
guardCommand = "stack exec -- runghc -package=yaml examples/tests/checks/CiCatalog.hs --self-test"

buildChecks :: [String]
buildChecks =
  [ guardCommand
  , "stack exec -- runghc -package=hs-to-rocq examples/tests/checks/RocqVersion.hs"
  , "bash examples/tests/checks/harness.sh"
  , "bash examples/tests/checks/concurrent.sh"
  ]

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

normalise :: String -> String
normalise = unwords . filter (/= "--allow-different-user") . words

-- Section boundaries keep prose and other tables out of the selection check.
sections :: String -> [(String, [String])]
sections input = go (lines input)
  where
    go [] = []
    go (line:rest) = case stripPrefix "## " line of
      Nothing -> go rest
      Just heading -> let (body, following) = break (isPrefixOf "## ") rest
                      in (heading, body) : go following

selectionRows :: String -> [(String, [String])]
selectionRows input =
  [ (init name, cells)
  | body <- [b | ("Select jobs", b) <- sections input]
  , line <- body
  , let cells = map trim (splitCells line)
  , first:_ <- [cells]
  , Just name <- [stripPrefix "`" first]
  , not (null name), last name == '`'
  ]
  where
    splitCells "|" = []
    splitCells ('|':rest) = case break (== '|') rest of
      (cell, following) -> cell : splitCells following
    splitCells _ = []

idErrors :: String -> [String] -> [String] -> [String]
idErrors label expected actual =
  [label ++ ": missing " ++ name | name <- expected, name `notElem` actual] ++
  [label ++ ": unknown " ++ name | name <- actual, name `notElem` expected] ++
  [label ++ ": duplicate " ++ name | name:_:_ <- group (sort actual)]

-- Recognize the known success fallbacks even with quotes or line continuations.
-- This is a catalog policy check, not a general-purpose shell parser.
hasMask :: String -> Bool
hasMask input = any (`isInfixOf` compact)
  [ "||test$?-eq2", "||test2-eq$?", "||[$?-eq2]", "||[[$?-eq2]]"
  , "||true", "||:", "||exit0"
  ]
  where compact = filter (\c -> not (isSpace c) && c `notElem` ("\"'\\" :: String)) input

conditional :: Settings -> Bool
conditional fields = Map.member "if" fields ||
  maybe False (/= Yaml.Bool False) (Map.lookup "continue-on-error" fields)

runLines :: Settings -> [String]
runLines fields = case Map.lookup "run" fields of
  Just (Yaml.String command) -> lines (Text.unpack command)
  _ -> []

catalogErrors :: Workflow -> String -> String -> [String]
catalogErrors (Workflow jobs) catalog fix =
  idErrors "job headings" names headings ++
  idErrors "selection table" names (map fst rows) ++
  concatMap dependencyErrors rows ++
  [path ++ ": failure masking" | (path, text) <- [(catalogPath, catalog), (fixPath, fix)], hasMask text] ++
  ["ci-fix must delegate to " ++ catalogPath | not (catalogPath `isInfixOf` fix)] ++
  ["ci-fix duplicates the job catalog" |
    any (isPrefixOf "Job: " . fst) (sections fix) || not (null (selectionRows fix)) ||
    any (`elem` jobCommands) (executableLines (lines fix))] ++
  concatMap wiringErrors buildChecks
  where
    names = Map.keys jobs
    headings = mapMaybe (stripPrefix "Job: " . fst) (sections catalog)
    rows = selectionRows catalog
    dependencyErrors (name, cells) = case Map.lookup name jobs of
      Nothing -> [] -- Reported as an unknown selection above.
      Just job ->
        ["selection prerequisites: " ++ name | drop 2 cells /= [if null (needs job) then "No" else "Yes"]] ++
        ["unsupported prerequisites: " ++ name | needs job `notElem` [[], ["build-haskell"]]]
    executableLines = either (const []) (map normalise . concatMap lines) . bashBlocks . unlines
    jobCommands = [command | (heading, body) <- sections catalog, "Job: " `isPrefixOf` heading,
      command <- executableLines body, any (`isPrefixOf` command) ["stack ", "make ", "git ", "coqc ", "hlint ", "(cd ", "opam lint "]]
    buildBody = executableLines (concat [body | ("Job: build-haskell", body) <- sections catalog])
    build = Map.lookup "build-haskell" jobs
    checkSteps command = [s | job <- maybe [] pure build, s <- steps job, map normalise (runLines s) == [normalise command]]
    wiringErrors command =
      ["catalog build-haskell check: " ++ command | length (filter ((== normalise command) . normalise) buildBody) /= 1] ++
      ["workflow build-haskell check: " ++ command | length (checkSteps command) /= 1] ++
      ["workflow check must be unconditional and fail-fast: " ++ command |
        any conditional (checkSteps command) || maybe False (conditional . settings) build]

bashBlocks :: String -> Either String [String]
bashBlocks = go . lines
  where
    go [] = Right []
    go ("```bash":rest) = case break (== "```") rest of
      (_, []) -> Left "unterminated bash fence"
      (body, _:following) -> (unlines body :) <$> go following
    go (_:rest) = go rest

-- bash -n treats heredoc contents as data. Parse the inner scripts separately.
shellParts :: String -> [String]
shellParts block = block :
  [ unlines (takeWhile (/= "BASH") body)
  | (_:body) <- [dropWhile (not . isInfixOf "<<'BASH'") (lines block)]
  ]

shellResult :: FilePath -> [String] -> String -> IO (Either String ())
shellResult bash args input = catchIOError run (pure . Left . show)
  where
    run = do
      (status, _, diagnostic) <- readProcessWithExitCode bash args input
      pure $ if status == ExitSuccess && null diagnostic then Right ()
             else Left (show status ++ ": " ++ diagnostic)

syntaxErrors :: FilePath -> String -> String -> IO [String]
syntaxErrors bash path text = case bashBlocks text of
  Left problem -> pure [path ++ ": " ++ problem]
  Right blocks -> fmap concat $ forM (zip [1 :: Int ..] (concatMap shellParts blocks)) $ \(number, block) -> do
    result <- shellResult bash ["-n"] block
    pure [path ++ ": bash snippet " ++ show number ++ ": " ++ problem | Left problem <- [result]]

readWorkflow :: FilePath -> IO (Either String Workflow)
readWorkflow path = catchIOError load (pure . Left . show)
  where
    load = do
      result <- Yaml.decodeFileWithWarnings path
      pure $ case result of
        Left problem -> Left (Yaml.prettyPrintParseException problem)
        Right ([], workflow) -> Right workflow
        Right (warnings, _) -> Left ("workflow YAML warnings: " ++ show warnings)

assert :: String -> Bool -> IO ()
assert label passed = unless passed (die ("not ok - " ++ label))

withWorkflow :: String -> (FilePath -> IO a) -> IO a
withWorkflow input action = bracket create removeFile action
  where
    create = do
      tmp <- getTemporaryDirectory
      (path, handle) <- openTempFile tmp "hs-to-rocq-ci-catalog.yaml"
      hPutStr handle input
      hClose handle
      pure path

-- A missing mutation anchor must fail the regression, not silently test the
-- unchanged document. Pinned fixtures do not depend on checkout history depth.
replaceOnce :: String -> String -> String -> String
replaceOnce old new input = case stripPrefix old input of
  Just rest -> new ++ rest
  Nothing -> case input of
    [] -> error ("missing mutation anchor: " ++ old)
    c:rest -> c : replaceOnce old new rest

selfTests :: FilePath -> Workflow -> String -> String -> IO ()
selfTests bash workflow catalog fix = do
  let rejected label needle ci repair = do
        assert label (any (isInfixOf needle) (catalogErrors workflow ci repair))
        putStrLn ("ok - " ++ label)
      mutate label needle old new = rejected label needle (replaceOnce old new catalog) fix
  -- Exact .claude/commands/ci.md snapshot at 9cd1a34c679cd9db904f75108a37e21a494f9251.
  old <- Text.unpack <$> Text.readFile "examples/tests/checks/ci-catalog-old-head.md"
  rejected "pinned 9cd1a34 old HEAD catalog" "job headings: missing" old fix
  forM_ ["hlint", "build-haskell", "test-coq-files", "tests", "test-rocq9", "test-rocq9-translation", "test-translation"] $ \name -> do
    let heading = "## Job: " ++ name ++ "\n"
        row = "| `" ++ name ++ "` |"
    mutate ("missing heading " ++ name) "job headings: missing" heading "## Omitted\n"
    mutate ("duplicate heading " ++ name) "job headings: duplicate" heading (heading ++ heading)
    mutate ("missing selection " ++ name) "selection table: missing" row "| omitted |"
    mutate ("duplicate selection " ++ name) "selection table: duplicate" row (row ++ " | No |\n" ++ row)
  mutate "incorrect prerequisite" "selection prerequisites" "| `tests` | | Yes |" "| `tests` | | No |"
  forM_ ["|| test $? -eq 2", "|| test \"$?\" -eq 2", "|| [ $? -eq 2 ]", "|| true"] $ \mask -> do
    rejected ("ci mask " ++ mask) "failure masking"
      (replaceOnce "make -C examples/tests\n" ("make -C examples/tests " ++ mask ++ "\n") catalog) fix
    rejected ("ci-fix mask " ++ mask) "failure masking" catalog
      (replaceOnce "-- make -C examples/tests Simple.pass\n" ("-- make -C examples/tests Simple.pass " ++ mask ++ "\n") fix)
  rejected "missing ci-fix delegation" "ci-fix must delegate" catalog (replaceOnce catalogPath "elsewhere.md" fix)
  rejected "duplicated ci-fix catalog" "ci-fix duplicates" catalog (fix ++ "\n" ++ catalog)
  rejected "duplicated ci-fix commands without headings" "ci-fix duplicates" catalog (fix ++ "\n```bash\nstack build\n```\n")
  mutate "catalog guard unwired" "catalog build-haskell check" guardCommand "# removed catalog guard"

  yaml <- Text.unpack <$> Text.readFile workflowPath
  let yamlRejected label needle input = withWorkflow input $ \path -> do
        parsed <- readWorkflow path
        let problems = either pure (\w -> catalogErrors w catalog fix) parsed
        assert label (any (isInfixOf needle) problems)
        putStrLn ("ok - " ++ label)
  let withoutHlint = unlines $ case break (== "  hlint:") (lines yaml) of
        (before, _:rest) -> before ++ dropWhile (\line -> null line || "    " `isPrefixOf` line) rest
        _ -> error "missing workflow mutation anchor: hlint"
  yamlRejected "missing workflow job" "unknown hlint" withoutHlint
  yamlRejected "duplicate workflow job key" "DuplicateKey" (yaml ++ "\n  hlint:\n    runs-on: ubuntu-latest\n")
  yamlRejected "workflow guard unwired" "workflow build-haskell check" (replaceOnce ("run: stack --allow-different-user exec -- runghc -package=yaml") "run: removed" yaml)
  yamlRejected "workflow guard masks failures" "unconditional and fail-fast" (replaceOnce "      - name: Check local CI catalog and regressions\n" "      - name: Check local CI catalog and regressions\n        continue-on-error: true\n" yaml)
  yamlRejected "workflow guard can be skipped" "unconditional and fail-fast" (replaceOnce "      - name: Check local CI catalog and regressions\n" "      - name: Check local CI catalog and regressions\n        if: false\n" yaml)

  forM_ [("ci syntax", catalog), ("ci-fix syntax", fix)] $ \(label, text) -> do
    problems <- syntaxErrors bash label text
    assert label (null problems)
  broken <- syntaxErrors bash "broken heredoc" (replaceOnce "stack build\n" "if then\n" catalog)
  assert "heredoc body syntax is checked" (not (null broken))
  missingBash <- syntaxErrors "" "missing Bash" catalog
  assert "missing checker prerequisite cannot pass" (not (null missingBash))
  missingWorkflow <- readWorkflow ""
  assert "missing workflow prerequisite cannot pass" (either (const True) (const False) missingWorkflow)
  putStrLn "ok - syntax errors and missing checker prerequisites cannot pass"

  -- Run only stubbed tools: an unusable PATH blocks all external commands other
  -- than the explicitly selected Bash. cd is also stubbed, so no output trees
  -- or Git state can change. The real harness/concurrent checks never run here.
  let stubs = unlines
        [ "export PATH=/dev/null REAL_BASH='" ++ bash ++ "' COQ820_SWITCH=stub ROCQ90_SWITCH=stub"
        , "cd() { :; }; git() { :; }; coqc() { :; }; hlint() { :; }"
        , "stack() { if [[ $BLOCK == stack ]]; then return 127; fi; if [[ $* == build && $FAIL == stack ]]; then return 2; fi; }"
        , "coq_makefile() { if [[ $BLOCK == coq_makefile ]]; then return 127; fi; }"
        , "make() { if [[ $* == '-C examples/tests' && $FAIL == make ]]; then return 2; fi; }"
        , "opam() { if [[ $BLOCK == opam ]]; then return 127; fi; if [[ $1 == lint ]]; then return 0; fi; while [[ $# -gt 0 && $1 != -- ]]; do shift; done; shift; \"$@\"; }"
        , "bash() { case $1 in examples/tests/checks/harness.sh|examples/tests/checks/concurrent.sh) return 0;; *) \"$REAL_BASH\" \"$@\";; esac; }"
        , "export -f cd git coqc hlint stack coq_makefile make opam bash"
        ]
      jobBlock name = case lookup ("Job: " ++ name) (sections catalog) >>= either (const Nothing) Just . bashBlocks . unlines of
        Just [block] -> block
        _ -> error ("expected one bash block for " ++ name)
      runStubbed label name setup expected = do
        (status, _, diagnostic) <- readProcessWithExitCode bash [] (stubs ++ setup ++ "\n" ++ jobBlock name)
        assert (label ++ ": " ++ show status ++ " " ++ diagnostic) (expected status)
        putStrLn ("ok - " ++ label)
  forM_ [name | (heading, _) <- sections catalog, Just name <- [stripPrefix "Job: " heading]] $ \name ->
    runStubbed ("stubbed success " ++ name) name "export BLOCK= FAIL=" (== ExitSuccess)
  runStubbed "build failure is not green" "build-haskell" "export BLOCK= FAIL=stack" (== ExitFailure 2)
  runStubbed "Make exit 2 is not green" "tests" "export BLOCK= FAIL=make" (== ExitFailure 2)
  forM_ [("build-haskell", "stack"), ("tests", "opam"), ("tests", "coq_makefile")] $ \(name, tool) ->
    runStubbed ("blocked " ++ tool ++ " is not green") name ("export BLOCK=" ++ tool ++ " FAIL=") (== ExitFailure 127)
  forM_ [("tests", "COQ820_SWITCH"), ("test-rocq9", "ROCQ90_SWITCH")] $ \(name, switch) ->
    runStubbed ("unset " ++ switch ++ " is not green") name ("export BLOCK= FAIL=; unset " ++ switch) (/= ExitSuccess)

main :: IO ()
main = catchIOError run (die . ("CI catalog prerequisite failed: " ++) . show)
  where
    run = do
      setLocaleEncoding utf8
      args <- getArgs
      unless (args `elem` [[], ["--self-test"]]) (die "Usage: CiCatalog.hs [--self-test] (from repository root)")
      bash <- findExecutable "bash" >>= maybe (die "CI catalog prerequisite failed: Bash is missing") pure
      workflow <- readWorkflow workflowPath >>= either (die . ("CI catalog workflow failed: " ++)) pure
      catalog <- Text.unpack <$> Text.readFile catalogPath
      fix <- Text.unpack <$> Text.readFile fixPath
      syntax <- (++) <$> syntaxErrors bash catalogPath catalog <*> syntaxErrors bash fixPath fix
      let problems = catalogErrors workflow catalog fix ++ syntax
      unless (null problems) (die (unlines ("CI catalog failed:" : problems)))
      unless (null args) (selfTests bash workflow catalog fix)
      putStrLn "CI catalog: PASS (workflow, /ci, /ci-fix, Bash syntax)"
