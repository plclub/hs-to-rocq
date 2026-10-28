module ModuleEdits where

import qualified ModuleEdits.Abstract as Abstract
import qualified ModuleEdits.Support as Support

originalMarker :: Bool
originalMarker = True

externalValue :: Bool
externalValue = Support.supportMarker

operatorChoice :: Bool
operatorChoice = False Support.<+> True

transparentIdentity :: Bool -> Bool
transparentIdentity x = x

abstractUse :: Bool -> Bool
abstractUse x = Abstract.opaqueOriginal x

boxed :: Abstract.Payload
boxed = Abstract.Pack True
