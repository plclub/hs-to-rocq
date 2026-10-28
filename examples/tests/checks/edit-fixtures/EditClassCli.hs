module EditClassCli where

data Token = MkToken

class Identity a where
  identityMethod :: a -> a
  identityMethod x = x

instance Identity Token where
  identityMethod x = x
