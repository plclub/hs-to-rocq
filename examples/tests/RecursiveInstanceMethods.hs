{-# LANGUAGE FlexibleInstances #-}

module RecursiveInstanceMethods where

orFlag :: Bool -> Bool -> Bool
orFlag True _ = True
orFlag False y = y

andFlag :: Bool -> Bool -> Bool
andFlag True y = y
andFlag False _ = False

notFlag :: Bool -> Bool
notFlag True = False
notFlag False = True

data Pair a = MkPair a a

-- Both arguments are ordinary parameters; recursive occurrences change a.
data Nest tag a = NEmpty | NLeaf tag a
                | NBranch tag (Pair a) (Nest tag (Pair a)) (Pair a)

class Tag tag where
  enabled :: tag -> Bool

instance Tag Bool where
  enabled x = x

class FoldLike f where
  foldLike :: (a -> Bool) -> f a -> Bool
  foldDefault :: (a -> Bool) -> f a -> Bool
  foldDefault f t = foldLike f t
  foldNegated :: (a -> Bool) -> f a -> Bool
  foldNegated f t = notFlag (foldLike f t)
  foldEvery :: (a -> Bool) -> f a -> Bool
  foldEvery f t = notFlag (foldLike (\x -> notFlag (f x)) t)
  takeFlags :: f a -> [Bool] -> [Bool]
  takeFlags t ys = ys

instance FoldLike Pair where
  foldLike f (MkPair x y) = orFlag (f x) (f y)

instance Tag tag => FoldLike (Nest tag) where
  foldLike f NEmpty = False
  foldLike f (NLeaf tag x) = andFlag (enabled tag) (f x)
  foldLike f (NBranch tag left middle right) =
    andFlag (enabled tag)
      (orFlag (foldLike f left)
        (orFlag (foldLike (foldLike f) middle) (foldLike f right)))

instance FoldLike [] where
  foldLike f [] = False
  foldLike f (x:xs) = orFlag (f x) (foldLike f xs)
  takeFlags xs ys = case xs of
    [] -> []
    _ : rest -> case ys of
      [] -> []
      y : more -> y : takeFlags rest more

middleTrue :: Nest Bool Bool
middleTrue = NBranch True (MkPair False False)
               (NLeaf True (MkPair False True)) (MkPair False False)

deepTrue :: Nest Bool Bool
deepTrue = NBranch True (MkPair False False)
             (NBranch True (MkPair (MkPair False False) (MkPair False False))
                (NLeaf True (MkPair (MkPair False False) (MkPair False True)))
                (MkPair (MkPair False False) (MkPair False False)))
             (MkPair False False)
