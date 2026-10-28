module ModuleEdits.Support where

supportMarker :: Bool
supportMarker = True

infixl 6 <+>
(<+>) :: Bool -> Bool -> Bool
x <+> _ = x
