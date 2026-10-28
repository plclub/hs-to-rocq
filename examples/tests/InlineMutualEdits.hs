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
