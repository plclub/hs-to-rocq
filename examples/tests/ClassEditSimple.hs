module ClassEditSimple where

data Mark = First | Second

class Direct a where
  choose :: a -> a
  through :: a -> a
  through x = choose x

instance Direct Mark where
  choose _ = Second
