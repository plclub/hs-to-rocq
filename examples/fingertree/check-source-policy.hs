module Main (main) where

import SourcePolicy (runPolicy)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = getArgs >>= runPolicy >>= either die (const (putStrLn "Source policy passed."))
