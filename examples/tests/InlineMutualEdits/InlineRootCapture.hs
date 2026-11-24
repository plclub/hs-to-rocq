module InlineRootCapture where

run :: Bool -> [Bool] -> [Bool]
run seed input = main input
  where
    main seed = case seed of
      [] -> []
      _ : rest -> helper rest
    helper xs = case xs of
      [] -> [seed]
      _ : rest -> main rest
