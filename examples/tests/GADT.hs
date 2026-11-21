{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes     #-}

module GADT where

import Data.Kind (Type)

data O
data C

data MaybeO ex t where
  JustO    :: t -> MaybeO O t
  NothingO ::      MaybeO C t

data Foo a :: * -> * where
  Bar :: O -> Foo a O
  Baz :: a -> Foo a C

foo :: Foo Bool a -> Bool
foo (Bar _) = True
foo (Baz b) = b

data Nested f a where
  Leaf :: f a -> Nested f a
  Pair :: Nested f (a, a) -> Nested f a

-- The handler must instantiate at the branch's index and stay polymorphic
-- when passed to the recursive call at a different index.
walk :: (forall x. f x -> Bool) -> Nested f a -> Bool
walk h (Leaf x) = h x
walk h (Pair t) = walk h t

type Endo = forall a. a -> a

-- The alias hides a type binder between two value arguments. Both
-- saturation and partial application must preserve the Haskell type.
keep :: Bool -> Endo
keep b x = x

keepBool :: Bool -> Bool
keepBool b = keep b b

keepPoly :: Endo
keepPoly = keep True

data Equal a :: Type -> Type where
  Same :: Equal a a
data Outcome proof = Yes proof | No

transport :: Outcome (Equal a b) -> a -> b -> b
transport outcome x y = case outcome of
  Yes Same -> x
  No -> y
