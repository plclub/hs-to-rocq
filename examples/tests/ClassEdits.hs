{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE NoPolyKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module ClassEdits where

class First m where
  first :: m a -> m a

class First m => Second m where
  second :: m a -> m a

class (forall m. Second m => Second (t m)) => Lift t where
  lift :: Second m => m a -> t m a

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

-- The checked instance must match both parameters, even when the first
-- parameter is identical. Methods use the two different result types.
class Choose a b where
  choose :: a -> b -> b

instance Choose Mark Mark where
  choose _ _ = RightMark

instance Choose Mark OtherMark where
  choose _ _ = OtherLeft

data Steps = Last Mark | Step Steps

class Result a where
  result :: a -> Mark

instance Result Mark where
  result _ = RightMark

instance Result Steps where
  result (Last m) = result m
  result (Step t) = result t

-- Neither operation is a Prelude method. The qualified do block must
-- call the two operators chosen by GHC's renamer.
(>>=) :: Mark -> (Mark -> Mark) -> Mark
x >>= f = f x

(>>) :: Mark -> Mark -> Mark
LeftMark >> _ = RightMark
RightMark >> x = x

qualifiedDo :: Mark -> Mark
qualifiedDo firstMark = ClassEdits.do
  x <- firstMark
  x
  LeftMark
