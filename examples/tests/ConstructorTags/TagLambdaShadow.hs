{-# LANGUAGE MagicHash #-}
module TagLambdaShadow where
import GHC.Exts (dataToTag#)
data Other = A | B
data Outer = Wrap Other
class Probe a where
  probe :: a -> Bool
instance Probe Outer where
  probe x = (\x -> case dataToTag# x of
    0# -> True
    _ -> False) B
