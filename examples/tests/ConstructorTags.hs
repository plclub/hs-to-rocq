{-# LANGUAGE FlexibleInstances, MagicHash, NoPolyKinds #-}

module ConstructorTags where

import GHC.Exts (dataToTag#, tagToEnum#, (==#), (<#), (/=#))

-- Source order is deliberately different from constructor-name order.
data Choice p = Zulu | Alpha Bool | Middle Bool Bool
data Other = Zed | Ay | Eight | Two | Seven | Three | Six | Four | Five

class Tags a where
  sameTag :: a -> a -> Bool
  beforeTag :: a -> a -> Bool
  differentTag :: a -> a -> Bool
  minTag :: a -> a -> a
  minTag x y = if beforeTag x y then x else y
  maxTag :: a -> a -> a
  maxTag x y = if beforeTag x y then y else x
  -- The receiver of dataToTag# is Other, not the class's parameter a.
  otherFirst :: a -> Other -> Bool
  otherFirst ignored value = tagToEnum# (dataToTag# value ==# 0#)
  ascribedFirst :: a -> Bool
  ascribedFirst ignored = tagToEnum# (dataToTag# (Zed :: Other) ==# 0#)
  tagStop :: a -> [Bool] -> Bool
  tagStop value flags = sameTag value value

instance Tags (Choice p) where
  sameTag x y = tagToEnum# (dataToTag# x ==# dataToTag# y)
  beforeTag x y = tagToEnum# (dataToTag# x <# dataToTag# y)
  differentTag x y = tagToEnum# ((dataToTag# x /=# dataToTag# y) ==# 1#)
  tagStop value flags = case flags of
    [] -> tagToEnum# (dataToTag# value ==# 0#)
    _ : rest -> tagStop value rest

instance Tags Other where
  sameTag x y = tagToEnum# (dataToTag# x ==# dataToTag# y)
  beforeTag x y = tagToEnum# (dataToTag# x <# dataToTag# y)
  differentTag x y = tagToEnum# ((dataToTag# x /=# dataToTag# y) ==# 1#)
