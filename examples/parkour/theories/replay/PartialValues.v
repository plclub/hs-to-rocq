From Stdlib Require Import Lists.List Logic.Eqdep_dec.
Require Import Parkour.Symbol DeadlockWellFormed.

(* Extract a family only on the finite roles that have returned. In
   particular, this requires neither global choice nor a default value
   for a blocked role's type. *)
Section FiniteValues.
Variable A : Symbol -> Type.
Variable P : forall p, A p -> Prop.

Definition add_value r (x : A r) rs
    (v : values A (fun p => In p rs)) : values A (fun p => In p (r :: rs)).
Proof.
  intros p member. destruct (List.list_eq_dec BinNat.N.eq_dec r p) as [same |
    other].
  - exact (eq_rect r A x p same).
  - apply v. destruct member; [contradiction|assumption].
Defined.

Lemma add_value_valid r x rs v :
  P r x -> (forall p d, P p (v p d)) ->
  forall p d, P p (add_value r x rs v p d).
Proof.
  intros Hx Hv p d. unfold add_value.
  destruct (List.list_eq_dec BinNat.N.eq_dec r p) as [e|ne].
  - now destruct e.
  - apply Hv.
Qed.

Theorem select_returned rs :
  (forall p, In p rs -> exists x : A p, P p x) ->
  exists v : values A (fun p => In p rs), forall p d, P p (v p d).
Proof.
  induction rs as [|r rs IH]; intro completed.
  - exists (fun p (d : False) => False_rect (A p) d).
    intros p d; contradiction.
  - destruct (completed r (or_introl eq_refl)) as [x Hx].
    destruct IH as [v Hv].
    { intros p d. apply completed. now right. }
    exists (add_value r x rs v). now apply add_value_valid.
Qed.
End FiniteValues.

(* Membership witnesses can index continuations. On a duplicate-free roster
   both witnesses select the same cons cell, and equality of symbols has UIP
   by decidability. No proof irrelevance for arbitrary propositions is needed.
   *)
Lemma roster_member_unique (rs : list Symbol) :
  NoDup rs -> forall p (i j : In p rs), i = j.
Proof.
  induction 1 as [|r rs Fresh ND IH]; intros p i j; [contradiction|].
  cbn in i,j. destruct i as [e|i], j as [f|j].
  - f_equal. apply UIP_dec. apply List.list_eq_dec. exact BinNat.N.eq_dec.
  - subst; contradiction.
  - subst; contradiction.
  - f_equal. apply IH.
Qed.
