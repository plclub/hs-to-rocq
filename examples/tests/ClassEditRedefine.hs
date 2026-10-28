module ClassEditRedefine where

data Result = FromSource | FromDefault | FromInstance
data DefaultCase = DefaultInput
data InstanceCase = InstanceInput
data PlainCase = PlainInput

class Patched a where
  result :: a -> Result
  result _ = FromSource

instance Patched DefaultCase

instance Patched InstanceCase where
  result _ = FromSource

instance Patched PlainCase where
  result _ = FromSource
