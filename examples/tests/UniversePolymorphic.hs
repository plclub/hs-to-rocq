module UniversePolymorphic where

data MyList a = Nil | Cons a (MyList a)

data Pair a b = MkPair a b

data Template a = MkTemplate a

data Tree a = Leaf a | Node (Tree a) (Tree a)

data Either_ a b = Left_ a | Right_ b

data Maybe_ a = Nothing_ | Just_ a

data Box a = MkBox a

data Stream a = SCons a (Stream a)

data Rose a = MkRose a (Forest a)
data Forest a = NilF | ConsF (Rose a) (Forest a)
