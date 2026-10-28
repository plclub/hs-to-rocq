module ScopedMethodSource where

data Mark = MarkFirst | MarkSecond
data Other = OtherFirst | OtherSecond

class Flags a where
  sibling :: a -> Bool
  caller :: a -> Bool
  unscoped :: a -> Bool

instance Flags Mark where
  sibling _ = False
  caller x = sibling x
  unscoped x = sibling x

instance Flags Other where
  sibling OtherFirst = True
  sibling OtherSecond = False
  caller x = sibling x
  unscoped x = sibling x

chooseScoped :: a -> Bool
chooseScoped _ = True
