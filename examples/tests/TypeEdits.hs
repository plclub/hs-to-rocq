{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GADTs #-}

module TypeEdits where

type Small = Bool

data Product a b = MkProduct a b

data Scoped = ScopedBool Bool | DefaultUnit Bool

data Trimmed a where
  MkTrimmed :: forall a b. a -> Trimmed a

keepBoth :: forall a b. a -> b -> a
keepBoth x _ = x

explicitSignature :: Bool
explicitSignature = False

inferredOverride = True

erasedSignature :: Bool
erasedSignature = True

scopedValue :: Bool
scopedValue = True

defaultValue :: Bool
defaultValue = True
