{-# LANGUAGE OverloadedStrings #-}

-- Run from the package root with stack test hs-to-rocq:ci-catalog.
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
  parseJSON value = do
    fields <- Yaml.parseJSON value
    -- Root defaults also govern inherited shells and relative check paths.
    if unsafeRunSettings (nestedSettings "run" (nestedSettings "defaults" fields))
      then fail "workflow run defaults must be fail-fast at the repository root"
      else Yaml.withObject "workflow" (\o -> Workflow <$> o Yaml..: "jobs") value

instance Yaml.FromJSON Job where
  parseJSON value = do
    fields <- Yaml.parseJSON value
    dependencies <- case Map.lookup "needs" fields of
      Nothing -> pure []
      Just (Yaml.String name) -> pure [Text.unpack name]
      Just names -> Yaml.parseJSON names
    commands <- maybe (pure []) Yaml.parseJSON (Map.lookup "steps" fields)
    pure (Job dependencies commands fields)

workflowPath, catalogPath, fixPath, guardCommand, auditCommand :: String
workflowPath = ".github/workflows/hs-to-rocq.yml"
catalogPath = ".claude/commands/ci.md"
fixPath = ".claude/commands/ci-fix.md"
guardCommand = "stack test"
auditCommand = "python3 test/assumptions.py"

-- These remain the same seven jobs, with the same build prerequisites.
jobNeeds :: [(String, [String])]
jobNeeds =
  [ ("hlint", []), ("build-haskell", []), ("test-coq-files", [])
  , ("tests", ["build-haskell"]), ("test-rocq9", ["build-haskell"])
  , ("test-rocq9-translation", ["build-haskell"]), ("test-translation", ["build-haskell"])
  ]

buildChecks :: [String]
buildChecks =
  [ guardCommand
   , "bash test/harness.sh"
   , "bash test/concurrent.sh"
   , auditCommand
   ]

rocq90Checks, rocq92Checks, rocq92Cleans, rocq92Setup :: [String]
rocq90Checks =
  [ "make -C examples/rocq9.0 clean"
  , "make -j2 -C examples/rocq9.0 base"
  , "make -C examples/rocq9.0/tests"
  ]
rocq92Checks = [rocq92Audit] ++ rocq92Cleans ++ [rocq92Foundations, rocq92Proof]
rocq92Cleans = map (inSwitch "ROCQ92_SWITCH")
  [ "make -C examples/fingertree clean"
  , "make -C examples/rocq9.2 clean"
  ]
rocq92Setup =
  [ "opam switch create \"$ROCQ92_SWITCH\" ocaml-base-compiler.4.14.2 --no-switch -y"
  , "opam install --switch=\"$ROCQ92_SWITCH\" -y rocq-prover.meta.1 rocq-core.9.2.0 rocq-runtime.9.2.0 rocq-stdlib.9.2.0"
  ]

rocq92Audit, rocq92Foundations, rocq92Proof :: String
rocq92Audit = inSwitch "ROCQ92_SWITCH" (auditCommand ++ " --rocq rocq")
rocq92Foundations = inSwitch "ROCQ92_SWITCH" "make -j2 -C examples/rocq9.2 check"
rocq92Proof = inSwitch "ROCQ92_SWITCH"
  "make -j2 -C examples/fingertree kernel-check core-check interval-check priority-check"

inSwitch :: String -> String -> String
inSwitch switch command = "opam exec --switch=\"$" ++ switch ++ "\" -- " ++ command

rocqSubmodules, failFastBash, rocq90Install :: String
rocqSubmodules = "examples/ghc/ghc examples/fingertree/fingertree"
failFastBash = "bash -e -o pipefail <<'BASH'"
rocq90Install = "opam install -y rocq-prover.9.0.0 rocq-core.9.0.0 rocq-runtime.9.0.0 rocq-stdlib.9.0.0 rocq-equations.1.3.1+9.0"

rocqCatalogScript :: [String]
rocqCatalogScript =
  [ failFastBash
  , ": \"${ROCQ90_SWITCH:?Select a Rocq 9.0 switch}\""
  , ": \"${ROCQ92_SWITCH:?Select a Rocq 9.2 switch}\""
  , "git submodule update --init " ++ rocqSubmodules
  ] ++ map (inSwitch "ROCQ90_SWITCH") rocq90Checks ++ rocq92Checks ++ ["BASH"]

-- The two clean commands share a step; all other new checks have their own.
rocqWorkflowScripts :: [[String]]
rocqWorkflowScripts =
  [ ["eval $(opam env)"] ++ take 2 rocq90Checks
  , ["eval $(opam env)", last rocq90Checks]
  , rocq92Setup
  , [rocq92Audit], rocq92Cleans, [rocq92Foundations], [rocq92Proof]
  ]

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

normalise :: String -> String
normalise = unwords . filter (/= "--allow-different-user") . words

-- Join only shell line continuations, not arbitrary shell constructs. Exact
-- scripts below deliberately reject conditionals, pipelines and extra flags.
commandLines :: String -> [String]
commandLines = filter (\line -> not (null line) && not ("#" `isPrefixOf` line)) .
  map normalise . lines . Text.unpack . Text.replace "\\\n" " " . Text.pack

nestedSettings :: String -> Settings -> Settings
nestedSettings key fields = maybe Map.empty id (Map.lookup key fields >>= Yaml.parseMaybe Yaml.parseJSON)

stringSetting :: String -> Settings -> String
stringSetting key fields = case Map.lookup key fields of
  Just (Yaml.String value) -> Text.unpack value
  _ -> ""

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

runCommands :: Settings -> [String]
runCommands = commandLines . unlines . runLines

executableLines :: [String] -> [String]
executableLines = either (const []) (concatMap commandLines) . bashBlocks . unlines

jobBlocks :: String -> String -> Either String [String]
jobBlocks name = bashBlocks . unlines . concatMap snd .
  filter ((== "Job: " ++ name) . fst) . sections

-- Default Actions shells fail on a nonzero simple command. Custom shell
-- templates must retain that behavior, especially for the two-command clean.
unsafeRunSettings :: Settings -> Bool
unsafeRunSettings fields = Map.member "working-directory" fields ||
  maybe False (`notElem` map Yaml.String ["bash", "sh", "bash -e -o pipefail {0}", "sh -e {0}"])
    (Map.lookup "shell" fields)

workflowScriptErrors :: Map.Map String Job -> String -> [[String]] -> [String]
workflowScriptErrors jobs name scripts = concatMap check scripts
  where
    job = Map.lookup name jobs
    check script =
      ["workflow " ++ name ++ " script (exactly once): " ++ unwords script | length matching /= 1] ++
      ["workflow check must be unconditional and fail-fast: " ++ unwords script |
        maybe False (conditional . settings) job || any conditional matching ||
        any unsafeRunSettings matching ||
        maybe False (unsafeRunSettings . nestedSettings "run" . nestedSettings "defaults" . settings) job] ++
      ["workflow command must occur exactly once in " ++ name ++ ": " ++ command |
        command <- script,
        -- eval is shared by the existing 9.0 steps, not a standalone check.
        command /= "eval $(opam env)",
        [owner | (owner, ownerJob) <- Map.toList jobs, s <- steps ownerJob,
          line <- runCommands s, line == normalise command] /= [name]]
      where matching = [s | j <- maybe [] pure job, s <- steps j, runCommands s == map normalise script]

setupErrors :: Map.Map String Job -> String -> [String] -> [String]
setupErrors jobs name submodules =
  ["workflow " ++ name ++ " setup composite must be unconditional and unique" |
    length setup /= 1 || any conditional setup || maybe False (conditional . settings) job] ++
  ["workflow " ++ name ++ " setup must install python3" |
    not (any (elem "python3" . words . stringSetting "extra-apt-packages" . nestedSettings "with") setup)] ++
  ["workflow " ++ name ++ " setup must initialize pinned submodules: " ++ unwords submodules |
    not (null submodules), not (any ((== sort submodules) . sort . words . stringSetting "submodules" . nestedSettings "with") setup)] ++
  ["workflow " ++ name ++ " setup must precede its checks" |
    [i | (i, s) <- indexed, stringSetting "uses" s == "./.github/actions/setup-hs-to-rocq"] >=
      take 1 [i | (i, s) <- indexed, not (null (runLines s))]]
  where
    job = Map.lookup name jobs
    indexed = zip [0 :: Int ..] (maybe [] steps job)
    setup = [s | (_, s) <- indexed, stringSetting "uses" s == "./.github/actions/setup-hs-to-rocq"]

rocqErrors :: Map.Map String Job -> String -> [String]
rocqErrors jobs catalog =
  ["catalog test-rocq9 must be one unconditional fail-fast script with ordered, isolated 9.0/9.2 checks" |
    either (const True) ((/= [rocqCatalogScript]) . map commandLines) (jobBlocks "test-rocq9" catalog)] ++
  workflowScriptErrors jobs "test-rocq9" rocqWorkflowScripts ++
  setupErrors jobs "test-rocq9" (words rocqSubmodules) ++
  ["workflow test-rocq9 must set ROCQ92_SWITCH: rocq92" |
    maybe True ((/= "rocq92") . stringSetting "ROCQ92_SWITCH" . nestedSettings "env" . settings) job] ++
  ["workflow test-rocq9 steps must not override ROCQ92_SWITCH" |
    any (Map.member "ROCQ92_SWITCH" . nestedSettings "env") jobSteps] ++
  ["workflow test-rocq9 must install pinned Rocq 9.0 before its checks" |
    length installs /= 1 || any (\(_, s) -> conditional s || unsafeRunSettings s) installs ||
    map fst installs >= take 1 positions] ++
  ["workflow test-rocq9 order: 9.0, isolated 9.2 setup, audit, cleans, foundations, proofs" |
    length positions == length rocqWorkflowScripts, positions /= sort positions]
  where
    job = Map.lookup "test-rocq9" jobs
    jobSteps = maybe [] steps job
    indexed = zip [0 :: Int ..] jobSteps
    installs = [(i, s) | (i, s) <- indexed, rocq90Install `elem` runCommands s]
    positions = [i | script <- rocqWorkflowScripts, (i, s) <- indexed, runCommands s == script]

catalogErrors :: Workflow -> String -> String -> [String]
catalogErrors (Workflow jobs) catalog fix =
  idErrors "workflow jobs" (map fst jobNeeds) names ++
  ["workflow prerequisites: " ++ name | (name, expected) <- jobNeeds,
    Just job <- [Map.lookup name jobs], needs job /= expected] ++
  idErrors "job headings" names headings ++
  idErrors "selection table" names (map fst rows) ++
  concatMap dependencyErrors rows ++
  [path ++ ": failure masking" | (path, text) <- [(catalogPath, catalog), (fixPath, fix)], hasMask text] ++
  ["ci-fix must delegate to " ++ catalogPath | not (catalogPath `isInfixOf` fix)] ++
  ["ci-fix duplicates the job catalog" |
    any (isPrefixOf "Job: " . fst) (sections fix) || not (null (selectionRows fix)) ||
    any (`elem` jobCommands) (executableLines (lines fix))] ++
  concatMap wiringErrors buildChecks ++
  workflowScriptErrors jobs "build-haskell" (map pure buildChecks) ++
  setupErrors jobs "build-haskell" [] ++
  ["catalog build-haskell must be one unconditional fail-fast script" | not buildScriptMatches] ++
  ["catalog command must occur exactly once in " ++ name ++ ": " ++ command |
    (name, commands) <- [("build-haskell", buildChecks), ("test-rocq9", rocq92Checks)], command <- commands,
    [owner | (heading, body) <- sections catalog, Just owner <- [stripPrefix "Job: " heading],
      line <- executableLines body, line == command] /= [name]] ++
  rocqErrors jobs catalog
  where
    names = Map.keys jobs
    headings = mapMaybe (stripPrefix "Job: " . fst) (sections catalog)
    rows = selectionRows catalog
    dependencyErrors (name, cells) = case Map.lookup name jobs of
      Nothing -> [] -- Reported as an unknown selection above.
      Just job ->
        ["selection prerequisites: " ++ name | drop 2 cells /= [if null (needs job) then "No" else "Yes"]] ++
        ["unsupported prerequisites: " ++ name | needs job `notElem` [[], ["build-haskell"]]]
    jobCommands = [command | (heading, body) <- sections catalog, "Job: " `isPrefixOf` heading,
      command <- executableLines body, any (`isPrefixOf` command) ["stack ", "make ", "git ", "coqc ", "hlint ", "(cd ", "opam lint ", "python3 ", "opam exec "]]
    buildBody = executableLines (concat [body | ("Job: build-haskell", body) <- sections catalog])
    buildScriptMatches = case jobBlocks "build-haskell" catalog of
      Right [block] -> case commandLines block of
        header:rest -> header == failFastBash && not (null rest) && last rest == "BASH" &&
          sort (init rest) == sort (["stack build", "stack exec -- ghc --numeric-version"] ++ buildChecks)
        _ -> False
      _ -> False
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

changeCatalogJob :: String -> (String -> String) -> String -> String
changeCatalogJob name change = unlines . go . lines
  where
    go [] = error ("missing catalog mutation anchor: " ++ name)
    go (heading:rest)
      | heading == "## Job: " ++ name =
          let (body, following) = break (isPrefixOf "## ") rest
          in heading : lines (change (unlines body)) ++ following
      | otherwise = heading : go rest

changeJob :: String -> (Job -> Job) -> Workflow -> Workflow
changeJob name change (Workflow jobs)
  | Map.member name jobs = Workflow (Map.adjust change name jobs)
  | otherwise = error ("missing workflow mutation anchor: " ++ name)

changeStep :: [String] -> (Settings -> Settings) -> Job -> Job
changeStep script change job = case filter ((== script) . runCommands) (steps job) of
  [_] -> job { steps = [if runCommands s == script then change s else s | s <- steps job] }
  _ -> error ("missing or duplicate workflow script mutation anchor: " ++ unwords script)

setRun :: [String] -> Settings -> Settings
setRun = Map.insert "run" . Yaml.String . Text.pack . unlines

selfTests :: FilePath -> Workflow -> String -> String -> IO ()
selfTests bash workflow catalog fix = do
  let rejected label needle ci repair = do
        assert label (any (isInfixOf needle) (catalogErrors workflow ci repair))
        putStrLn ("ok - " ++ label)
      mutate label needle old new = rejected label needle (replaceOnce old new catalog) fix
  -- Exact .claude/commands/ci.md snapshot at 9cd1a34c679cd9db904f75108a37e21a494f9251.
  old <- Text.unpack <$> Text.readFile "test/ci-catalog-old-head.md"
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
  forM_ [auditCommand, rocq92Proof] $ \command ->
    rejected ("duplicated ci-fix command " ++ command) "ci-fix duplicates" catalog
      (fix ++ "\n```bash\n" ++ command ++ "\n```\n")
  mutate "catalog guard unwired" "catalog build-haskell check" guardCommand "# removed catalog guard"
  mutate "catalog fast audit unwired" "catalog build-haskell check" (auditCommand ++ "\n") "# removed audit\n"

  let mutateRocq label old new = rejected label "catalog test-rocq9"
        (changeCatalogJob "test-rocq9" (replaceOnce old new) catalog) fix
  forM_ rocq92Checks $ \command -> do
    mutateRocq ("catalog missing " ++ command) (command ++ "\n") ""
    mutateRocq ("catalog duplicate " ++ command) command (command ++ "\n" ++ command)
    mutateRocq ("catalog conditional " ++ command) command ("if false; then\n" ++ command ++ "\nfi")
    mutateRocq ("catalog wrong switch " ++ command) command (replaceOnce "$ROCQ92_SWITCH" "$ROCQ90_SWITCH" command)
  forM_ ["ROCQ90_SWITCH", "ROCQ92_SWITCH"] $ \switch ->
    mutateRocq ("catalog missing switch assertion " ++ switch)
      (": \"${" ++ switch ++ ":?Select a Rocq " ++ (if switch == "ROCQ90_SWITCH" then "9.0" else "9.2") ++ " switch}\"\n") ""
  mutateRocq "catalog missing pinned fingertree submodule" rocqSubmodules "examples/ghc/ghc"
  mutateRocq "catalog submodule update follows remote" "git submodule update --init" "git submodule update --init --remote"
  mutateRocq "catalog loses pipefail" failFastBash "bash -e <<'BASH'"
  mutateRocq "catalog masks proof exit 2" rocq92Proof (rocq92Proof ++ " || test $? -eq 2")
  let swapLines a b = unlines . map (\line -> if normalise line == a then b else if normalise line == b then a else line) . lines
  forM_ ([(clean, rocq92Foundations) | clean <- rocq92Cleans] ++ [(rocq92Foundations, rocq92Proof)]) $ \(a, b) ->
    rejected ("catalog reorders " ++ a) "catalog test-rocq9"
      (changeCatalogJob "test-rocq9" (swapLines a b) catalog) fix
  rejected "catalog duplicates proof in another job" "catalog command must occur exactly once"
    (changeCatalogJob "tests" (replaceOnce "make -C examples/tests\n" ("make -C examples/tests\n" ++ rocq92Proof ++ "\n")) catalog) fix
  forM_ ["if false; then\n" ++ auditCommand ++ "\nfi", auditCommand ++ " || true"] $ \replacement ->
    rejected ("catalog fast audit wrapper " ++ replacement) "catalog build-haskell must be one"
      (changeCatalogJob "build-haskell" (replaceOnce (auditCommand ++ "\n") (replacement ++ "\n")) catalog) fix
  forM_ rocq90Checks $ \command ->
    mutateRocq ("catalog loses Rocq 9.0 check " ++ command) (inSwitch "ROCQ90_SWITCH" command ++ "\n") ""

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
  yamlRejected "workflow guard unwired" "workflow build-haskell check" (replaceOnce "run: stack --allow-different-user test" "run: removed" yaml)
  yamlRejected "workflow guard masks failures" "unconditional and fail-fast" (replaceOnce "      - name: Run Haskell test suites\n" "      - name: Run Haskell test suites\n        continue-on-error: true\n" yaml)
  yamlRejected "workflow guard can be skipped" "unconditional and fail-fast" (replaceOnce "      - name: Run Haskell test suites\n" "      - name: Run Haskell test suites\n        if: false\n" yaml)
  yamlRejected "workflow-level shell can mask failed cleans" "workflow run defaults must be fail-fast"
    (yaml ++ "\ndefaults:\n  run:\n    shell: bash {0}\n")
  yamlRejected "workflow-level working directory changes check paths" "workflow run defaults must be fail-fast"
    (yaml ++ "\ndefaults:\n  run:\n    working-directory: examples\n")
  withWorkflow (yaml ++ "\ndefaults:\n  run:\n    shell: bash\n") $ \path -> do
    parsed <- readWorkflow path
    assert "fail-fast workflow-level shell remains accepted"
      (either (const False) (\w -> null (catalogErrors w catalog fix)) parsed)
  putStrLn "ok - fail-fast workflow-level shell remains accepted"

  let workflowRejected label needle change = do
        assert label (any (isInfixOf needle) (catalogErrors (change workflow) catalog fix))
        putStrLn ("ok - " ++ label)
      buildMutation label needle change = workflowRejected label needle (changeJob "build-haskell" change)
      rocqMutation label needle change = workflowRejected label needle (changeJob "test-rocq9" change)
      alterRun old new = changeStep old (setRun new)
      setupStep job = case [s | s <- steps job, stringSetting "uses" s == "./.github/actions/setup-hs-to-rocq"] of
        [s] -> s
        _ -> error "missing or duplicate setup mutation anchor"
      changeSetup change job = let original = setupStep job
        in job { steps = [if s == original then change s else s | s <- steps job] }
      setNested key field value fields = Map.insert key
        (Yaml.toJSON (Map.insert field value (nestedSettings key fields))) fields
      swapScripts left right job =
        let find script = case filter ((== script) . runCommands) (steps job) of
              [s] -> s
              _ -> error "missing or duplicate script order mutation anchor"
            a = find left
            b = find right
        in job { steps = [if s == a then b else if s == b then a else s | s <- steps job] }

  buildMutation "workflow loses fast audit" "workflow build-haskell check" (alterRun [auditCommand] ["true"])
  buildMutation "workflow fast audit is duplicated" "exactly once" (\job -> job { steps = steps job ++ [setRun [auditCommand] Map.empty] })
  forM_ [("if", Yaml.Bool False), ("continue-on-error", Yaml.Bool True)] $ \(key, value) ->
    buildMutation ("workflow fast audit " ++ key) "unconditional and fail-fast" (changeStep [auditCommand] (Map.insert key value))
  buildMutation "workflow masks fast audit" "workflow build-haskell check" (alterRun [auditCommand] [auditCommand ++ " || true"])
  buildMutation "workflow build setup loses python3" "setup must install python3"
    (changeSetup (setNested "with" "extra-apt-packages" (Yaml.String "")))
  workflowRejected "workflow duplicates proof in another job" "workflow command must occur exactly once"
    (changeJob "tests" (\job -> job { steps = steps job ++ [setRun [rocq92Proof] Map.empty] }))

  -- Every new step, including compiler setup and the paired clean, is protected.
  forM_ (drop 2 rocqWorkflowScripts) $ \script -> do
    rocqMutation ("workflow missing script " ++ unwords script) "workflow test-rocq9 script" (alterRun script ["true"])
    forM_ [("if", Yaml.Bool False), ("continue-on-error", Yaml.Bool True)] $ \(key, value) ->
      rocqMutation ("workflow " ++ key ++ " " ++ unwords script) "unconditional and fail-fast" (changeStep script (Map.insert key value))
    rocqMutation ("workflow masks " ++ unwords script) "workflow test-rocq9 script"
      (alterRun script (init script ++ [last script ++ " || true"]))
    rocqMutation ("workflow switch override " ++ unwords script) "must not override ROCQ92_SWITCH"
      (changeStep script (setNested "env" "ROCQ92_SWITCH" (Yaml.String "default")))
  rocqMutation "workflow proof is duplicated" "exactly once"
    (\job -> job { steps = steps job ++ [setRun [rocq92Proof] Map.empty] })
  rocqMutation "workflow missing 9.2 switch" "must set ROCQ92_SWITCH"
    (\job -> job { settings = Map.delete "env" (settings job) })
  rocqMutation "workflow wrong 9.2 switch" "must set ROCQ92_SWITCH"
    (\job -> job { settings = setNested "env" "ROCQ92_SWITCH" (Yaml.String "default") (settings job) })
  rocqMutation "workflow job is conditional" "unconditional and fail-fast"
    (\job -> job { settings = Map.insert "if" (Yaml.Bool False) (settings job) })
  rocqMutation "workflow setup loses pinned fingertree submodule" "initialize pinned submodules"
    (changeSetup (setNested "with" "submodules" (Yaml.String "examples/ghc/ghc")))
  rocqMutation "workflow Rocq setup loses python3" "setup must install python3"
    (changeSetup (setNested "with" "extra-apt-packages" (Yaml.String "")))
  rocqMutation "workflow setup is conditional" "setup composite must be unconditional"
    (changeSetup (Map.insert "if" (Yaml.Bool False)))
  forM_ rocq92Checks $ \command -> do
    let script = if command `elem` rocq92Cleans then rocq92Cleans else [command]
    rocqMutation ("workflow wrong compiler " ++ command) "workflow test-rocq9 script"
      (alterRun script (map (replaceOnce "$ROCQ92_SWITCH" "$ROCQ90_SWITCH") script))
  forM_ ["kernel-check", "core-check", "interval-check", "priority-check"] $ \target -> do
    let proof = rocq92Proof
        weakened = replaceOnce (" " ++ target) "" proof
    mutateRocq ("catalog weakens proof targets: " ++ target) proof weakened
    rocqMutation ("workflow weakens proof targets: " ++ target) "workflow test-rocq9 script" (alterRun [proof] [weakened])
  forM_ [("rocq-prover.meta.1", "rocq-prover.9.2.0"), ("rocq-core.9.2.0", "rocq-core.9.0.0"),
    ("rocq-runtime.9.2.0", "rocq-runtime"), ("rocq-stdlib.9.2.0", "rocq-stdlib"),
    (" --no-switch", ""), ("--switch=\"$ROCQ92_SWITCH\"", "--switch=default"),
    ("ocaml-base-compiler.4.14.2", "ocaml-base-compiler")] $ \(old, new) ->
      rocqMutation ("workflow weakens isolated setup: " ++ old) "workflow test-rocq9 script"
        (alterRun rocq92Setup (lines (replaceOnce old new (unlines rocq92Setup))))
  forM_ [rocq92Cleans, [rocq92Foundations]] $ \script ->
    rocqMutation ("workflow proofs precede " ++ unwords script) "workflow test-rocq9 order"
      (swapScripts script [rocq92Proof])
  rocqMutation "workflow switches compiler before old checks" "workflow test-rocq9 order"
    (swapScripts rocq92Setup (rocqWorkflowScripts !! 1))
  rocqMutation "workflow foundations precede cleans" "workflow test-rocq9 order"
    (swapScripts rocq92Cleans [rocq92Foundations])
  forM_ (take 2 rocqWorkflowScripts) $ \script ->
    rocqMutation ("workflow loses old check " ++ unwords script) "workflow test-rocq9 script" (alterRun script ["true"])
  rocqMutation "workflow clean uses non-fail-fast shell" "unconditional and fail-fast"
    (changeStep rocq92Cleans (Map.insert "shell" (Yaml.String "bash {0}")))
  rocqMutation "workflow proofs use wrong working directory" "unconditional and fail-fast"
    (changeStep [rocq92Proof] (Map.insert "working-directory" (Yaml.String "examples")))
  rocqMutation "workflow loses old compiler setup" "install pinned Rocq 9.0"
    (\job -> job { steps = map (\s -> setRun (map (\line -> if line == rocq90Install then "true" else line) (runCommands s)) s)
      (steps job) })
  workflowRejected "workflow drops build prerequisite" "workflow prerequisites"
    (changeJob "test-rocq9" (\job -> job { needs = [] }))
  forM_ (map fst jobNeeds) $ \name ->
    workflowRejected ("workflow loses required job " ++ name) "workflow jobs: missing"
      (\(Workflow jobs) -> Workflow (Map.delete name jobs))
  let wrappedSetup = take 1 rocq92Setup ++ [replaceOnce " -y " " -y \\\n  " (last rocq92Setup)]
  assert "backslash-wrapped setup remains accepted"
    (null (catalogErrors (changeJob "test-rocq9" (alterRun rocq92Setup wrappedSetup) workflow) catalog fix))
  putStrLn "ok - backslash-wrapped setup remains accepted"

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
  -- or Git state can change. Neither the real scripts (including assumptions.py)
  -- nor a compiler, translator, Make recipe or tool installer can run here.
  let stubs = unlines
        [ "export PATH=/dev/null REAL_BASH='" ++ bash ++ "' COQ820_SWITCH=stub820 ROCQ90_SWITCH=stub90 ROCQ92_SWITCH=stub92"
        , "unset STUB_SWITCH"
        , "cd() { :; }; git() { :; }; coqc() { :; }; hlint() { :; }"
        , "stack() { if [[ $BLOCK == stack ]]; then return 127; fi; if [[ $* == build && $FAIL == stack || $* == test && $FAIL == haskell-tests ]]; then return 2; fi; }"
        , "coq_makefile() { if [[ $BLOCK == coq_makefile ]]; then return 127; fi; }"
        , "make() {"
        , "  case $* in"
        , "    '-C examples/rocq9.0 clean'|'-j2 -C examples/rocq9.0 base'|'-C examples/rocq9.0/tests') [[ $STUB_SWITCH == stub90 ]] || return 127;;"
        , "    *examples/fingertree*|*examples/rocq9.2*) [[ $STUB_SWITCH == stub92 ]] || return 127;;"
        , "  esac"
        , "  if [[ $* == '-C examples/tests' && $FAIL == make || $* == '-j2 -C examples/fingertree kernel-check core-check interval-check priority-check' && $FAIL == proof ]]; then return 2; fi"
        , "}"
        , "python3() {"
        , "  if [[ $BLOCK == python3 ]]; then return 127; fi"
        , "  case $* in"
        , "    'test/assumptions.py') if [[ $FAIL == fast-audit ]]; then return 1; fi;;"
        , "    'test/assumptions.py --rocq rocq') [[ $STUB_SWITCH == stub92 ]] || return 127; if [[ $FAIL == audit-negative ]]; then return 1; fi;;"
        , "    *) return 127;;"
        , "  esac"
        , "}"
        , "opam() {"
        , "  if [[ $BLOCK == opam ]]; then return 127; fi"
        , "  if [[ $1 == lint ]]; then return 0; fi"
        , "  [[ $1 == exec ]] || return 127; shift"
        , "  local selected="
        , "  while [[ $# -gt 0 && $1 != -- ]]; do"
        , "    case $1 in --switch=*) selected=${1#--switch=};; *) return 127;; esac; shift"
        , "  done"
        , "  [[ $# -gt 0 && -n $selected ]] || return 127; shift"
        , "  (export STUB_SWITCH=\"$selected\"; \"$@\")"
        , "}"
        , "bash() { case $1 in test/harness.sh|test/concurrent.sh) return 0;; *) \"$REAL_BASH\" \"$@\";; esac; }"
        , "export -f cd git coqc hlint stack coq_makefile make python3 opam bash"
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
  runStubbed "Haskell test failure is not green" "build-haskell" "export BLOCK= FAIL=haskell-tests" (== ExitFailure 2)
  runStubbed "fast audit failure is not green" "build-haskell" "export BLOCK= FAIL=fast-audit" (== ExitFailure 1)
  runStubbed "Make exit 2 is not green" "tests" "export BLOCK= FAIL=make" (== ExitFailure 2)
  runStubbed "audit negative-check failure is not green" "test-rocq9" "export BLOCK= FAIL=audit-negative" (== ExitFailure 1)
  runStubbed "proof Make exit 2 is not green" "test-rocq9" "export BLOCK= FAIL=proof" (== ExitFailure 2)
  forM_ [("build-haskell", "stack"), ("tests", "opam"), ("tests", "coq_makefile"),
    ("build-haskell", "python3"), ("test-rocq9", "python3"), ("test-rocq9", "opam")] $ \(name, tool) ->
    runStubbed ("blocked " ++ tool ++ " is not green") name ("export BLOCK=" ++ tool ++ " FAIL=") (== ExitFailure 127)
  forM_ [("tests", "COQ820_SWITCH"), ("test-rocq9", "ROCQ90_SWITCH"), ("test-rocq9", "ROCQ92_SWITCH")] $ \(name, switch) ->
    runStubbed ("unset " ++ switch ++ " is not green") name ("export BLOCK= FAIL=; unset " ++ switch) (/= ExitSuccess)
  runStubbed "9.2 commands in a 9.0 switch cannot pass" "test-rocq9" "export BLOCK= FAIL= ROCQ92_SWITCH=stub90" (== ExitFailure 127)

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
      selfTests bash workflow catalog fix
      putStrLn "CI catalog: PASS (workflow, /ci, /ci-fix, Bash syntax)"
