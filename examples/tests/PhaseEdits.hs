module PhaseEdits where

data Token = MkToken Bool

promotedSeed :: Bool
promotedSeed = True

promotedLeaf :: Bool
promotedLeaf = promotedSeed

ordinaryValue :: Bool
ordinaryValue = False

opaqueIdentity :: Bool -> Bool
opaqueIdentity x = x

transparentIdentity :: Bool -> Bool
transparentIdentity x = x
