module RecursionEdits where

copy :: [a] -> [a]
copy [] = []
copy (x : xs) = x : copy xs

byWf :: [Bool] -> [Bool]
-- copy preserves length but hides the structural subterm from the guard checker.
byWf xs = case xs of
  [] -> []
  _ : rest -> True : byWf (copy rest)

byMeasure :: [Bool] -> Bool
byMeasure xs = case xs of
  [] -> False
  _ : rest -> not (byMeasure (copy rest))

data Stream a = More a (Stream a)

repeatStream :: a -> Stream a
repeatStream x = More x (repeatStream x)

headStream :: Stream a -> a
headStream (More x _) = x

tailStream :: Stream a -> Stream a
tailStream (More _ rest) = rest
