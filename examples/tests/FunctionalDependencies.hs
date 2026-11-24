{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}

module FunctionalDependencies where

data Mark = Off | On
data Element = MkElement Bool
data OtherElement = MkOtherElement Bool
data Box a = MkBox a

class Flag v where
  flag :: v -> Bool

instance Flag Mark where
  flag Off = False
  flag On = True

instance Flag Bool where
  flag x = x

-- The ordinary CPS encoding keeps both parameters and the superclass.
class Flag v => Measured v a | a -> v where
  measure :: a -> v
  marked :: a -> Bool
  marked x = flag (measure x)

instance Measured Mark Element where
  measure (MkElement False) = Off
  measure (MkElement True) = On

instance Measured Bool Bool where
  measure x = x
  marked _ = False

-- These instances share their first parameter, but compute different values.
instance Measured Mark OtherElement where
  measure (MkOtherElement False) = On
  measure (MkOtherElement True) = Off

instance Flag v => Measured v (Box v) where
  measure (MkBox x) = x

-- Here v occurs only in the constraint: GHC needs a -> v to accept this.
observeElement :: Measured v a => a -> Bool
observeElement x = flag (measure x)

-- The element argument determines the result parameter and its dictionary.
inferred = observeElement (MkElement True)

-- The edits select the direct encoding for this two-way dependency.
class Flag v => Codec v a | a -> v, v -> a where
  encode :: a -> v
  decode :: v -> a
  encodedFlag :: a -> Bool
  encodedFlag x = flag (encode x)

instance Codec Mark Element where
  encode (MkElement False) = Off
  encode (MkElement True) = On
  decode Off = MkElement False
  decode On = MkElement True

instance Codec Bool Bool where
  encode x = x
  decode x = x
  encodedFlag _ = False

-- Conversely, GHC needs v -> a because a occurs only in the constraint.
observeCode :: Codec v a => v -> Bool
observeCode x = encodedFlag (decode x)

roundTrip :: Codec v a => a -> a
roundTrip x = decode (encode x)

-- No dependency makes either argument sufficient to select these dictionaries.
-- The edits select the direct encoding, including its inherited default.
class Collision a b where
  collision :: a -> b -> Bool
  collisionDefault :: a -> b -> Bool
  collisionDefault x y = collision x y

instance Collision Mark Element where
  collision _ _ = True

instance Collision Mark Bool where
  collision _ _ = False

instance Collision Bool Element where
  collision x _ = x

instance Collision [a] Mark where
  collision _ _ = False

instance Collision [a] Bool where
  collision _ _ = True
