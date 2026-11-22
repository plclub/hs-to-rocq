{-# LANGUAGE DataKinds, GADTs, TypeApplications #-}

-- Inspect the same Haskell endpoints before and after the Cond repair.
module Main where

import Choreography.Choreo2
import Choreography.Network
import Control.Monad.Trans.Reader (runReaderT)
import Control.Monad.Tree
import GHC.TypeLits.Singletons
import System.Environment (getArgs)
import Text.Read (readMaybe)

program :: Choreo IO p (At () "B" p)
program = cond (At (const True) :: At Bool "A" p) $ \_ ->
  (At (const ()) :: At () "A" p) ~> SSymbol @"B"

-- Follow the witness schedule at the owner. No network or IO handler is run.
data Action = SendTo String String | Broadcast String | ReceiveFrom String
  deriving (Eq, Show)

observe :: Network IO a -> ([Action], Maybe a)
observe (Pure a) = ([], Just a)
observe (Bind t k) = case observe t of
  (prefix, Nothing) -> (prefix, Nothing)
  (prefix, Just x) -> let (suffix, y) = observe (k x) in (prefix ++ suffix, y)
observe (App f x) =
  let (right, arg) = observe x
      (left, fun) = observe f
  in (right ++ left, fun <*> arg)
observe (Perf (Send Root x dst)) = ([SendTo dst (show x)], Just ())
observe (Perf (BCast Root x)) = ([Broadcast (show x)], Just ())
observe (Perf (Recv Root src)) = ([ReceiveFrom src], Nothing)
observe _ = error "unexpected action or non-Root session"

main :: IO ()
main = do
  args <- getArgs
  let owner = runReaderT (unEpp (epp program (SSymbol @"A"))) Root
      peer  = runReaderT (unEpp (epp program (SSymbol @"B"))) Root
  expected <- case args of
    ["original"] -> checkOriginal owner
    ["repaired"] -> checkRepaired owner
    _ -> fail "expected mode: original or repaired"
  case (observe owner, observe peer) of
    ((as, Just _), (bs@[ReceiveFrom "A"], Nothing))
      | as == expected, readMaybe @Bool "()" == Nothing -> print (as, bs)
    _ -> fail "endpoint observations changed"

checkOriginal :: Network IO a -> IO [Action]
checkOriginal owner = case owner of
    App left right -> case (observe left, observe right) of
      ((ls@[Broadcast "True"], Just _), (rs@[SendTo "B" "()"], Just _)) -> do
        putStrLn ("A: App { left = " ++ show ls ++ ", right = " ++ show rs ++ " }")
        pure (rs ++ ls)
      _ -> fail "unexpected branches of the owner's App"
    _ -> fail "expected App at the root of A's projected endpoint"

checkRepaired :: Network IO a -> IO [Action]
checkRepaired owner = case owner of
    Bind before k -> case observe before of
      (bs@[Broadcast "True"], Just x) -> case observe (k x) of
        (as@[SendTo "B" "()"], Just _) -> do
          putStrLn ("A: Bind { before = " ++ show bs ++ ", continuation = " ++ show as ++ " }")
          pure (bs ++ as)
        _ -> fail "expected the continuation to send to B"
      _ -> fail "expected the choice broadcast before the continuation"
    _ -> fail "expected Bind at the root of A's projected endpoint"
