{-# LANGUAGE DataKinds, GADTs, TypeApplications #-}

-- Inspect the original Haskell endpoints independently of the Rocq translation.
-- The proof uses the generated Rocq terms; this diagnostic explains their shape.
module Main where

import Choreography.Choreo2
import Choreography.Network
import Control.Monad.Trans.Reader (runReaderT)
import Control.Monad.Tree
import GHC.TypeLits.Singletons
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
  let owner = runReaderT (unEpp (epp program (SSymbol @"A"))) Root
      peer  = runReaderT (unEpp (epp program (SSymbol @"B"))) Root
  case owner of
    App left right -> case (observe left, observe right) of
      ((ls@[Broadcast "True"], Just _), (rs@[SendTo "B" "()"], Just _)) ->
        putStrLn ("A: App { left = " ++ show ls ++ ", right = " ++ show rs ++ " }")
      _ -> fail "unexpected branches of the owner's App"
    _ -> fail "expected App at the root of A's projected endpoint"
  case (observe owner, observe peer) of
    ((as@[SendTo "B" "()", Broadcast "True"], Just _), (bs@[ReceiveFrom "A"], Nothing))
      | readMaybe @Bool "()" == Nothing -> print (as, bs)
    _ -> fail "pinned endpoint observations changed"
