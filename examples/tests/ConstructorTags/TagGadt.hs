{-# LANGUAGE FlexibleInstances, GADTs, MagicHash #-}
module TagGadt where
import GHC.Exts (dataToTag#)
data G a where
  MkG :: Bool -> G Bool
class Probe a where
  probe :: a -> Bool
instance Probe (G Bool) where
  probe value = case dataToTag# value of
    0# -> True
    _ -> False
