{-# LANGUAGE MagicHash #-}
module TagBuiltin where
import GHC.Exts (dataToTag#)
data Outer = Wrap Bool
class Probe a where
  probe :: a -> Bool -> Bool
instance Probe Outer where
  probe ignored value = case dataToTag# value of
    0# -> True
    _ -> False
