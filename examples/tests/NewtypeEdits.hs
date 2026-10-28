{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module NewtypeEdits where

class Toggle a where
  turn :: a -> a

instance Toggle Bool where
  turn True = False
  turn False = True

newtype Wrapped = Wrap { originalField :: Bool }
  deriving Toggle

-- The edited constructor metadata names this translated Haskell accessor.
unwrapped :: Wrapped -> Bool
unwrapped (Wrap value) = value
