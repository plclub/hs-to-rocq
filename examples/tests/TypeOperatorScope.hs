{-# LANGUAGE TypeOperators #-}
module TypeOperatorScope where

-- Both operator names occur in constructor types before either notation
-- is in scope. Subsequent declarations can use their infix notations.
data a @ b = End a b | Next (a :*: b)
data a :*: b = Box (a @ b)

sample :: Bool @ Bool
sample = Next (Box (End True False))
