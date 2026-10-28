module InvariantEdits where

data Flag = MkFlag Bool

valid :: Flag -> Bool
valid (MkFlag value) = value

enabled :: Flag
enabled = MkFlag True

keep :: Flag -> Flag
keep value = value
