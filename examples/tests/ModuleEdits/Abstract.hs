module ModuleEdits.Abstract where

data Payload = Pack Bool

opaqueOriginal :: Bool -> Bool
opaqueOriginal x = x
