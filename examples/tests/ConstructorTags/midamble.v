Require Import Coq.Lists.List Coq.Arith.PeanoNat Coq.ZArith.ZArith.
Import ListNotations.

Definition matrix {A B} (f : A -> A -> B) (xs : list A) :=
  map (fun x => map (f x) xs) xs.

Definition tag_checks {A} `{Tags A} (cases : list (A * nat)) : Prop :=
  let xs := map fst cases in
  let ranks := map snd cases in
  matrix sameTag xs = matrix Nat.eqb ranks /\
  matrix beforeTag xs = matrix Nat.ltb ranks /\
  matrix differentTag xs = matrix (fun i j => negb (Nat.eqb i j)) ranks /\
  matrix minTag xs =
    matrix (fun xi yj => if Nat.ltb (snd xi) (snd yj) then fst xi else fst yj) cases /\
  matrix maxTag xs =
    matrix (fun xi yj => if Nat.ltb (snd xi) (snd yj) then fst yj else fst xi) cases.

Definition shape_cases : list (Shape unit * nat) :=
  [(CtorZ, 0); (CtorA false, 1); (CtorA true, 1);
   (CtorM false false, 2); (CtorM false true, 2);
   (CtorM true false, 2); (CtorM true true, 2)].

Definition other_cases : list (OtherShape * nat) :=
  [(ZZ, 0); (AA, 1); (Eight, 2); (Two, 3); (Seven, 4);
   (Three, 5); (Six, 6); (Four, 7); (Five, 8)].
