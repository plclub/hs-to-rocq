module EditCli where

data Token = MkToken

value :: Bool -> Bool
value x = x

useValue :: Bool -> Bool
useValue x = value x

sourceA, sourceB, sourceC :: Bool
sourceA = True
sourceB = False
sourceC = True

probe :: Bool
probe = sourceA

dropped, skippedAxiom, replacement, ordinary, restored, skipRestored :: Bool
dropped = True
skippedAxiom = True
replacement = True
ordinary = True
restored = True
skipRestored = True

copyList :: [Bool] -> [Bool]
copyList [] = []
copyList (x : xs) = x : copyList xs
