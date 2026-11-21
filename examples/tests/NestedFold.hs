{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, NoImplicitPrelude #-}
module NestedFold where

data Tree f a where
  Perform :: f a -> Tree f a
  Return :: a -> Tree f a
  Then :: Tree f a -> (a -> Tree f b) -> Tree f b

after :: (b -> c) -> (a -> b) -> a -> c
after f k x = f (k x)

interpret :: (forall x. f x -> x) -> Tree f a -> a
interpret h (Perform e) = h e
interpret _ (Return x) = x
interpret h (Then t k) = after (interpret h) k (interpret h t)

data Op p a where
  Branch :: x -> (x -> Tree (Op p) a) -> Op p a
  Inspect :: (p -> a) -> Op p a
  Stored :: a -> Op p a

project :: forall a p. Tree (Op p) a -> p -> a
project t p = interpret step t where
  step :: forall x. Op p x -> x
  step (Branch v k) = project (k v) p
  step (Inspect value_0__) =
    let supply :: p
        supply = p
    in value_0__ supply
  step (Stored p) = p
