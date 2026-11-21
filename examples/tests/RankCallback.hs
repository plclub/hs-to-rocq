{-# LANGUAGE RankNTypes, TypeApplications #-}
module RankCallback where

type Unwrap = forall a. a -> a

-- Keep the same lambda-bound callback at two distinct specializations.
applyAtTwoTypes :: ((Unwrap -> Bool) -> Bool) -> Bool
applyAtTwoTypes locally = locally (\un -> if un True then empty (un @[Bool] []) else False)
  where empty [] = True
        empty _  = False

-- The constructor carries no information about the element type. Preserve
-- the explicit specialization even though Rocq cannot infer it from Nothing.
type Test = forall a. Maybe a -> Bool
atUnit :: ((Test -> Bool) -> Bool) -> Bool
atUnit locally = locally (\test -> test @() Nothing)

underRecursion :: ((Unwrap -> Bool) -> Bool) -> [Bool] -> Bool
underRecursion _ [] = True
underRecursion locally (b:bs) =
  locally (\un -> if un b then underRecursion locally bs else False)
