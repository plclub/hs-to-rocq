(* State the unfolding law independently of the moved theorem's name. *)
Definition fixEqType : Type :=
  forall (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R)
    (P : A -> Type)
    (F_sub : forall x : A,
      (forall y : {y : A | R y x}, P (proj1_sig y)) -> P x) (x : A),
  Coq.Program.Wf.Fix_sub A R Rwf P F_sub x =
  F_sub x (fun y => Coq.Program.Wf.Fix_sub A R Rwf P F_sub (proj1_sig y)).
(* The typed alias check follows its add-edit definition, after this midamble. *)
