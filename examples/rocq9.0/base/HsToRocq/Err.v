Require Import GHC.Base.
Require Import GHC.Num.

Class Default (a :Type) := {
  default : a
}.

#[global] Instance default_num {a} `{ Num a} : Default a := { default := #0 }.
#[global] Instance default_bool : Default bool := { default := false }.
#[global] Instance default_monoid {a} `{ Monoid a } : Default a :=
  { default := mempty }.
#[global] Instance default_applicative {a}{f} `{Default a} `{Applicative f}
  : Default (f a ) := { default := pure default }.
#[global] Instance default_pair {a}{b}`{Default a}`{Default b} : Default (a * b)%type :=
  { default := pair default default }.


#[global] Instance default_arr {a}{b} `{Default b} : Default (a -> b) := { default := fun x => default }.
#[global] Instance default_option {a} : Default (option a) := { default := None }.
#[global] Instance default_list {a} : Default (list a) := { default := nil } .

