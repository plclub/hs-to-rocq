module InlineMutualEdits where

marker :: [a] -> [a]
marker xs = xs

post :: [a] -> [a]
post xs = marker xs

walk :: [Bool] -> [Bool]
walk [] = []
walk (x : xs) = x : post (forward xs)

forward :: [Bool] -> [Bool]
forward xs = relay xs

relay :: [Bool] -> [Bool]
relay xs = walk xs

-- The local SCC becomes one well-founded recursive function after merge2 is
-- inlined. The outer result uses the retained nonrecursive helper too.
localMeasured :: [Bool] -> [Bool]
localMeasured xs = merge2 xs
  where
    go ys = case ys of
      [] -> []
      z : rest -> z : merge2 rest
    merge2 zs = go zs

peelOne :: [a] -> ([a], [a])
peelOne [] = ([], [])
peelOne (x:xs) = ([x], xs)

-- Both helpers inspect their own inputs and split a list before recurring.
-- Decrease relies on the actual merge2 arguments, not arbitrary inner lists.
localSplit :: [Bool] -> [Bool] -> [Bool]
localSplit left right = merge1 left right
  where
    merge1 as bs = case as of
      [] -> bs
      a:as' -> let (l, r) = peelOne bs
               in l ++ (a : merge2 as' r)
    merge2 :: [Bool] -> [Bool] -> [Bool]
    merge2 as bs = case bs of
      [] -> as
      b:bs' -> let (l, r) = peelOne as
               in l ++ (b : merge1 r bs')

-- The helper closes over the outer seed, whose spelling also challenges the
-- fresh-name supply. Call-site and helper-local bindings reuse its name,
-- a parameter name, and the name of the inlined function.
localShadow :: Bool -> [Bool] -> [Bool]
localShadow inlined_0__ input = main input
  where
    main ys = case ys of
      [] -> []
      value:rest -> case value of
        True -> let bridge z = [z] in bridge value
        False -> let inlined_0__ = value in bridge value rest
    bridge bit zs = case zs of
      [] -> [inlined_0__]
      value:more -> let zs = [value] in bit : (main more ++ zs)
