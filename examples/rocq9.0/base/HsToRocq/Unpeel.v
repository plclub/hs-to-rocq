(* Unpeel class: A directed form of Coercible, where a is the newtype type,
   and b the base type *)
Class Unpeel a b :=
  { unpeel : a -> b
  ; repeel : b -> a }.

#[global]
Instance Unpeel_refl a : Unpeel a a := Build_Unpeel _ _ (fun x => x) (fun x => x).

#[global]
Instance Unpeel_arrow
  a b c d
  `{Unpeel b a}
  `{Unpeel c d}
  : Unpeel (b -> c) (a -> d) :=
  { unpeel f x := unpeel (f (repeel x))
  ; repeel f x := repeel (f (unpeel x))
  }.

#[global]
Instance Unpeel_pair
  a b c d
  `{Unpeel a b}
  `{Unpeel c d}
  : Unpeel (a * c) (b * d) :=
  { unpeel '(x,y) := (unpeel x, unpeel y)
  ; repeel '(x,y) := (repeel x, repeel y)
  }.


Require Stdlib.Lists.List.

#[global]
Instance Unpeel_list a b
   `{Unpeel a b} : Unpeel (list a) (list b) :=
  { unpeel x := Stdlib.Lists.List.map unpeel x
  ; repeel x := Stdlib.Lists.List.map repeel x
  }.
