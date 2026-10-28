{-# LANGUAGE ViewPatterns #-}

module ClassEdits where

data Mark = LeftMark | RightMark
data OtherMark = OtherLeft | OtherRight

class Hidden a where
  hidden :: a -> a

instance Hidden Mark where
  hidden x = x

instance Hidden OtherMark where
  hidden x = x

identity :: a -> a
identity x = x

class Trimmed a where
  keep :: a -> a
  removed :: a -> a
  -- Skipping the method must avoid translating its default body.
  removed (identity -> x) = x

instance Trimmed Mark where
  keep _ = LeftMark
  -- Skipping the method must also avoid translating explicit instance bodies.
  removed (identity -> x) = x

instance Trimmed OtherMark where
  keep _ = OtherRight

class BodyOnly a where
  bodyKept :: a -> a
  bodyOnly :: a -> a
  -- Skipping only this default must leave a field for the explicit instance.
  bodyOnly (identity -> x) = x

instance BodyOnly Mark where
  bodyKept _ = LeftMark
  bodyOnly _ = RightMark
