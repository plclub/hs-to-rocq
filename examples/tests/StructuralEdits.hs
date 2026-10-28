module StructuralEdits where

named :: [a] -> [b] -> [b]
named xs ys = case xs of
  [] -> []
  _ : rest -> case ys of
    [] -> []
    y : more -> y : named rest more

positional :: [a] -> [b] -> [b]
positional xs ys = case xs of
  [] -> []
  _ : rest -> case ys of
    [] -> []
    y : more -> y : positional rest more

polyShape :: [a] -> [Bool] -> Bool
polyShape xs fuel = go xs fuel
  where
    -- Each recursive call changes the element type from b to [b].
    go :: [b] -> [Bool] -> Bool
    go ys [] = case ys of
      [] -> False
      _ : _ -> True
    go ys (_ : rest) = not (go [ys] rest)

collapsed :: [Bool] -> [Bool]
-- Collapsing must redirect both the local fixpoint and the outer recursion.
collapsed = let go xs = case xs of
                 [] -> []
                 True : rest -> True : go rest
                 False : rest -> False : collapsed rest
            in go
