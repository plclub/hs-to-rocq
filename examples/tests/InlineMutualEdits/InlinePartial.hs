module InlinePartial where

run :: [Bool] -> [Bool]
run input = go input
  where
    go ys = case ys of
      [] -> []
      z:rest -> z : (\resume -> resume rest) helper
    helper zs = go zs
