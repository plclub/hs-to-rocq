(* Raw VarSets are not an implementation of FSetInterface.WS.  Operation
   specifications below expose the representation evidence they need. *)
Set Warnings "-notation-overridden".
From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Coq.Lists.List Coq.Classes.Morphisms Coq.Classes.RelationClasses.
Require Import GHC.Base Core.
Require Import Proofs.GHC.Base Proofs.Axioms Proofs.Unique Proofs.Var.
Require Export Proofs.VarSetInvariant.
Import GHC.Base.ManualNotations.

Module VarSetFSet.
  Module E := Var_as_DT.
  Definition elt := Var.
  Definition t := VarSet.
  Definition In x (s : VarSet) := elemVarSet x s = true.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.
  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
  Definition eq : t -> t -> Prop := Equal.
  Definition empty : t := emptyVarSet.
  Definition is_empty : t -> bool := isEmptyVarSet.
  Definition mem : elt -> t -> bool := elemVarSet.
  Definition add x s := extendVarSet s x.
  Definition singleton x := unitVarSet x.
  Definition remove x s := delVarSet s x.
  Definition union := unionVarSet.
  Definition diff := minusVarSet.
  Definition subset := subVarSet.
  Definition exists_ := anyVarSet.
  Definition for_all := allVarSet.
  Definition filter := filterVarSet.
  Definition cardinal := sizeVarSet.
  Definition inter := intersectVarSet.

  (* Evidence is deliberately separate from extensional equality: Equal does
     not imply either WF or validity on the raw carrier. *)
  Definition WF (s : t) := IntMapProofs.WF (VarSet_IntMap s).

  Lemma eq_refl s : eq s s. Proof. intro a; reflexivity. Qed.
  Lemma eq_sym s s' : eq s s' -> eq s' s.
  Proof. intros H a; symmetry; apply H. Qed.
  Lemma eq_trans s s' s'' : eq s s' -> eq s' s'' -> eq s s''.
  Proof. intros H H' a; transitivity (In a s'); auto. Qed.
  #[export] Instance Equal_equiv : Equivalence Equal.
  Proof. split; [exact eq_refl | exact eq_sym | exact eq_trans]. Qed.
  #[export] Instance Subset_preorder : PreOrder Subset.
  Proof. split; unfold Subset; firstorder. Qed.

  Lemma In_1 s x y : E.eq x y -> In x s -> In y s.
  Proof.
    unfold E.eq, E.eqb, In. intro H. rewrite eq_unique in H.
    destruct s as [[m]]. unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    rewrite H. auto.
  Qed.
  Lemma In_eq_iff s x y : E.eq x y -> (In x s <-> In y s).
  Proof. intro H; split; apply In_1; [exact H | symmetry; exact H]. Qed.
  #[export] Instance In_m : Proper (E.eq ==> Equal ==> iff) In.
  Proof. intros x y H s t K. rewrite (In_eq_iff s x y H). apply K. Qed.
End VarSetFSet.
Export VarSetFSet.

(* Only construction-preservation lemmas belong in this database.  In
   particular, there is no default witness for a free raw set. *)
#[export] Hint Resolve emptyVarSet_WF unitVarSet_WF mkVarSet_WF
  extendVarSet_WF delVarSet_WF filterVarSet_WF
  extendVarSetList_WF delVarSetList_WF
  emptyVarSet_valid unitVarSet_valid mkVarSet_valid
  extendVarSet_valid delVarSet_valid filterVarSet_valid
  extendVarSetList_valid delVarSetList_valid
  unionVarSet_WF unionVarSet_valid minusVarSet_WF minusVarSet_valid
  unionVarSets_WF unionVarSets_valid mapUnionVarSet_WF mapUnionVarSet_valid : varset_inv.
#[export] Hint Resolve intersectVarSet_WF intersectVarSet_valid : varset_inv.
Ltac solve_varset_inv := solve [
  unfold VarSetFSet.WF, add, remove, singleton, union, diff, filter, empty, inter in *;
  lazymatch goal with
  | |- IntMapProofs.WF _ => eauto 12 with varset_inv
  | |- ValidVarSet _ => eauto 12 with varset_inv
  end].

Module VarSetFacts.
  Definition eqb := E.eqb.
  Definition eq_dec := E.eq_dec.
  Lemma mem_iff s x : In x s <-> mem x s = true.
  Proof. reflexivity. Qed.
  Lemma not_mem_iff s x : ~ In x s <-> mem x s = false.
  Proof. unfold In, mem; destruct (elemVarSet x s); intuition discriminate. Qed.
  Lemma empty_iff x : In x empty <-> False.
  Proof. unfold In, empty; rewrite elemVarSet_empty; intuition discriminate. Qed.
  Lemma singleton_iff x y : In y (singleton x) <-> E.eq x y.
  Proof.
    unfold In, singleton, E.eq, E.eqb. rewrite -> elemVarSet_unit, Eq_sym. reflexivity.
  Qed.
  Lemma add_iff s x y : WF s ->
    (In y (add x s) <-> E.eq x y \/ In y s).
  Proof.
    intro W. unfold In, add, E.eq, E.eqb.
    rewrite -> (elemVarSet_extend_eq s x y W), Eq_sym, Bool.orb_true_iff. reflexivity.
  Qed.
  Lemma remove_iff s x y : WF s ->
    (In y (remove x s) <-> In y s /\ ~ E.eq x y).
  Proof.
    intro W. unfold In, remove, E.eq, E.eqb.
    rewrite -> (elemVarSet_del s x y W). rewrite <- Var_eq_key.
    rewrite -> Eq_sym, Bool.andb_true_iff, Bool.negb_true_iff.
    destruct (x == y) eqn:K; unfold is_true; intuition.
    unfold E.t in H. rewrite -> K in H. discriminate H.
  Qed.
  Lemma filter_iff s x f : WF s -> ValidVarSet s ->
    RespectsVar f -> (In x (filter f s) <-> In x s /\ f x = true).
  Proof.
    intros W V R. unfold In, filter.
    rewrite -> (elemVarSet_lookup _ _ (filterVarSet_WF f s W)),
      (lookupVarSet_filter f s x W), (elemVarSet_lookup s x W).
    destruct (lookupVarSet s x) as [v|] eqn:L; [|simpl; intuition discriminate].
    assert (F : f x = f v) by (apply R; exact (V x v L)).
    rewrite F. destruct (f v); simpl; intuition discriminate.
  Qed.
  Lemma union_iff s t x : WF s -> WF t ->
    (In x (union s t) <-> In x s \/ In x t).
  Proof. intros W T. unfold In, union. rewrite -> elemVarSet_union by assumption. apply Bool.orb_true_iff. Qed.
  Lemma diff_iff s t x : WF s -> WF t ->
    (In x (diff s t) <-> In x s /\ ~ In x t).
  Proof.
    intros W T. unfold In, diff. rewrite -> elemVarSet_minus by assumption.
    rewrite -> Bool.andb_true_iff, Bool.negb_true_iff.
    destruct (elemVarSet x t); intuition discriminate.
  Qed.
  Lemma subset_iff s t : WF s -> WF t ->
    (Subset s t <-> subset s t = true).
  Proof. intros W T. symmetry. apply subVarSet_spec; assumption. Qed.
  Lemma is_empty_iff s : WF s ->
    (Empty s <-> is_empty s = true).
  Proof.
    intros W. unfold Empty, In, is_empty.
    rewrite -> isEmptyVarSet_spec by assumption.
    split; intros H x; specialize (H x); destruct (elemVarSet x s); intuition discriminate.
  Qed.
  Lemma add_b s x y : WF s -> mem y (add x s) = eqb x y || mem y s.
  Proof. intro W. unfold mem, add, eqb, E.eqb. rewrite -> elemVarSet_extend_eq by exact W. rewrite Eq_sym. reflexivity. Qed.
  Lemma remove_b s x y : WF s -> mem y (remove x s) = negb (eqb x y) && mem y s.
  Proof. intro W. unfold mem, remove, eqb, E.eqb. rewrite -> elemVarSet_del by exact W. rewrite <- Var_eq_key. rewrite Eq_sym. reflexivity. Qed.
  Lemma union_b s t x : WF s -> WF t -> mem x (union s t) = mem x s || mem x t.
  Proof. apply elemVarSet_union. Qed.
  Lemma diff_b s t x : WF s -> WF t -> mem x (diff s t) = mem x s && negb (mem x t).
  Proof. apply elemVarSet_minus. Qed.
  Lemma inter_iff s t x : WF s -> WF t ->
    (In x (inter s t) <-> In x s /\ In x t).
  Proof. intros W T. unfold In, inter. rewrite -> elemVarSet_intersect by assumption. apply Bool.andb_true_iff. Qed.
  Lemma inter_b s t x : WF s -> WF t -> mem x (inter s t) = mem x s && mem x t.
  Proof. apply elemVarSet_intersect. Qed.
  Lemma for_all_iff s f : WF s -> ValidVarSet s -> RespectsVar f ->
    (For_all (fun x => f x = true) s <-> for_all f s = true).
  Proof. intros W V R. symmetry. apply allVarSet_spec; assumption. Qed.
  Lemma exists_iff s f : WF s -> ValidVarSet s -> RespectsVar f ->
    (Exists (fun x => f x = true) s <-> exists_ f s = true).
  Proof. intros W V R. symmetry. apply anyVarSet_spec; assumption. Qed.
  Lemma disjoint_iff s t : WF s -> WF t ->
    (disjointVarSet s t = true <-> forall x, In x s -> ~ In x t).
  Proof.
    intros W T. rewrite -> (disjointVarSet_spec s t W T).
    unfold In. split; intros H x M; specialize (H x M).
    - rewrite H; discriminate.
    - apply Bool.not_true_is_false; exact H.
  Qed.
End VarSetFacts.
Export VarSetFacts.

Lemma InE (s : t) (x : elt) : elemVarSet x s <-> In x s.
Proof. reflexivity. Qed.
Lemma emptyVarSet_empty : emptyVarSet = empty. Proof. reflexivity. Qed.
Lemma delVarSet_remove x s : delVarSet s x = remove x s. Proof. reflexivity. Qed.
Lemma extendVarSet_add x s : extendVarSet s x = add x s. Proof. reflexivity. Qed.
Lemma unitVarSet_singleton : unitVarSet = singleton. Proof. reflexivity. Qed.
Lemma unionVarSet_union : unionVarSet = union. Proof. reflexivity. Qed.
Lemma minusVarSet_diff : minusVarSet = diff. Proof. reflexivity. Qed.
Lemma filterVarSet_filter : filterVarSet = filter. Proof. reflexivity. Qed.
Lemma intersectVarSet_inter : intersectVarSet = inter. Proof. reflexivity. Qed.
Lemma SubsetE s t : WF s -> WF t ->
  (subVarSet s t <-> s [<=] t).
Proof. intros W T. symmetry. apply subset_iff; assumption. Qed.
Lemma EmptyE s : WF s -> (isEmptyVarSet s <-> Empty s).
Proof. intros W. symmetry. apply is_empty_iff; assumption. Qed.

Module VarSetProperties.
  Lemma equal_refl s : s [=] s. Proof. reflexivity. Qed.
  Lemma equal_sym s s' : s [=] s' -> s' [=] s. Proof. symmetry; auto. Qed.
  Lemma equal_trans s s' s'' : s [=] s' -> s' [=] s'' -> s [=] s''.
  Proof. intros H K; transitivity s'; assumption. Qed.
  Lemma subset_equal s s' : s [=] s' -> s [<=] s'.
  Proof. intros H a A. exact (proj1 (H a) A). Qed.
  Lemma Subset_refl s : s [<=] s. Proof. reflexivity. Qed.
  Lemma Subset_trans s s' s'' : s [<=] s' -> s' [<=] s'' -> s [<=] s''.
  Proof. unfold Subset; firstorder. Qed.
  Lemma subset_antisym s s' : s [<=] s' -> s' [<=] s -> s [=] s'.
  Proof. unfold Subset, Equal; firstorder. Qed.
  Lemma add_equal s x : WF s -> In x s -> add x s [=] s.
  Proof.
    intros W H y. rewrite -> add_iff by exact W. split; [|auto].
    intros [E|K]; [eapply In_1; eauto | exact K].
  Qed.
  Lemma remove_equal s x : WF s -> ~ In x s -> remove x s [=] s.
  Proof.
    intros W H y. rewrite -> remove_iff by exact W. split; [tauto|].
    intro K; split; [exact K|]. intro E; apply H.
    eapply In_1; [symmetry; exact E | exact K].
  Qed.
  Lemma in_subset s t x : In x s -> s [<=] t -> In x t.
  Proof. unfold Subset; auto. Qed.
  Lemma subset_add_2 s t x : WF t -> s [<=] t -> s [<=] add x t.
  Proof. intros W H y K. rewrite -> add_iff by exact W. right; apply H; exact K. Qed.
  Lemma subset_add_3 s t x : WF s -> In x t -> s [<=] t -> add x s [<=] t.
  Proof.
    intros W H K y M. rewrite -> add_iff in M by exact W.
    destruct M as [E|M]; [eapply In_1; eauto|apply K; exact M].
  Qed.
  Lemma remove_add s x : WF s -> ~ In x s -> remove x (add x s) [=] s.
  Proof.
    intros W H y. rewrite -> remove_iff by (apply extendVarSet_WF; exact W).
    rewrite -> add_iff by exact W. split; [tauto|].
    intro K; split; [auto|]. intro E; apply H.
    eapply In_1; [symmetry; exact E|exact K].
  Qed.
  Lemma add_remove s x : WF s -> In x s -> add x (remove x s) [=] s.
  Proof.
    intros W H y. rewrite -> add_iff by (apply delVarSet_WF; exact W).
    rewrite -> remove_iff by exact W. split.
    - intros [E|[K _]]; [eapply In_1; eauto|exact K].
    - intro K. destruct (E.eq_dec x y); tauto.
  Qed.
End VarSetProperties.
Export VarSetProperties.

(* Evidence-aware congruences, NOT unrestricted Proper instances. *)
Lemma extendVarSet_m s t x y : WF s -> WF t ->
  s [=] t -> x == y -> extendVarSet s x [=] extendVarSet t y.
Proof.
  intros W T H E z. rewrite -> !extendVarSet_add, !add_iff by assumption.
  rewrite H. unfold E.eq, E.eqb. rewrite eq_unique in E.
  rewrite -> !Var_eq_key, E. reflexivity.
Qed.
Lemma delVarSet_m s t x y : WF s -> WF t ->
  s [=] t -> x == y -> delVarSet s x [=] delVarSet t y.
Proof.
  intros W T H E z. rewrite -> !delVarSet_remove, !remove_iff by assumption.
  rewrite H. unfold E.eq, E.eqb. rewrite eq_unique in E.
  rewrite -> !Var_eq_key, E. reflexivity.
Qed.
Lemma unionVarSet_m s t s' t' : WF s -> WF t -> WF s' -> WF t' ->
  s [=] t -> s' [=] t' -> unionVarSet s s' [=] unionVarSet t t'.
Proof.
  intros W T W' T' E E' x. rewrite -> !unionVarSet_union, !union_iff by assumption.
  rewrite -> E, E'. reflexivity.
Qed.
Lemma minusVarSet_m s t s' t' : WF s -> WF t -> WF s' -> WF t' ->
  s [=] t -> s' [=] t' -> minusVarSet s s' [=] minusVarSet t t'.
Proof.
  intros W T W' T' E E' x. rewrite -> !minusVarSet_diff, !diff_iff by assumption.
  rewrite -> E, E'. reflexivity.
Qed.
Lemma intersectVarSet_m s t s' t' : WF s -> WF t -> WF s' -> WF t' ->
  s [=] t -> s' [=] t' -> intersectVarSet s s' [=] intersectVarSet t t'.
Proof.
  intros W T W' T' E E' x. rewrite -> !intersectVarSet_inter, !inter_iff by assumption.
  rewrite -> E, E'. reflexivity.
Qed.

(* Rewriting only proceeds when the operation's premises can actually be
   proved.  Failure leaves the operation visible rather than inventing WF. *)
Ltac set_b_iff :=
  unfold is_true in *;
  try rewrite -> !emptyVarSet_empty in *;
  try rewrite -> !delVarSet_remove in *;
  try rewrite -> !extendVarSet_add in *;
  try rewrite -> !unionVarSet_union in *;
  try rewrite -> !minusVarSet_diff in *;
  try rewrite -> !filterVarSet_filter in *;
  try rewrite -> !intersectVarSet_inter in *;
  try rewrite -> !unitVarSet_singleton in *;
  repeat first [progress rewrite <- not_mem_iff in *
    | progress rewrite <- mem_iff in *
    | progress rewrite <- subset_iff in * by solve_varset_inv
    | progress rewrite <- is_empty_iff in * by solve_varset_inv
    | progress rewrite InE in *
    | progress rewrite -> SubsetE in * by solve_varset_inv
    | progress rewrite -> EmptyE in * by solve_varset_inv
    | progress rewrite -> disjoint_iff in * by solve_varset_inv].
Ltac set_iff :=
  repeat first [progress rewrite -> empty_iff in *
    | progress rewrite -> singleton_iff in *
    | progress rewrite -> add_iff in * by solve_varset_inv
    | progress rewrite -> remove_iff in * by solve_varset_inv
    | progress rewrite -> union_iff in * by solve_varset_inv
    | progress rewrite -> diff_iff in * by solve_varset_inv
    | progress rewrite -> inter_iff in * by solve_varset_inv
    | progress rewrite -> filter_iff in * by (solve_varset_inv || assumption)].
Module VarSetDecide.
  Ltac fsetdec := intros; set_b_iff;
    unfold Equal, Subset, Empty in *; intros;
    unfold elt, E.t in *;
    set_iff; unfold elt, E.t in *; try reflexivity;
    firstorder using E.eq_refl, E.eq_sym, E.eq_trans;
    try solve [eauto using In_1].
End VarSetDecide.
Export VarSetDecide.
(* Familiar names are retained, but their signatures are premise-aware. *)
Module VarSetBasicFacts.
  Lemma mem_1 s x : In x s -> mem x s = true. Proof. auto. Qed.
  Lemma mem_2 s x : mem x s = true -> In x s. Proof. auto. Qed.
  Lemma empty_1 : Empty empty. Proof. fsetdec. Qed.
  Lemma subset_1 s t : WF s -> WF t ->
    Subset s t -> subset s t = true.
  Proof. intros W T. apply (proj1 (subset_iff s t W T)). Qed.
  Lemma subset_2 s t : WF s -> WF t ->
    subset s t = true -> Subset s t.
  Proof. intros W T. apply (proj2 (subset_iff s t W T)). Qed.
  Lemma is_empty_1 s : WF s -> Empty s -> is_empty s = true.
  Proof. intros W; apply (proj1 (is_empty_iff s W)). Qed.
  Lemma is_empty_2 s : is_empty s = true -> Empty s.
  Proof.
    destruct s as [[m]]. destruct m; intros H x K;
      [discriminate H|discriminate H|discriminate K].
  Qed.
  Lemma add_1 s x y : WF s -> E.eq x y -> In y (add x s).
  Proof. intros W H. rewrite -> add_iff by exact W. auto. Qed.
  Lemma add_2 s x y : WF s -> In y s -> In y (add x s).
  Proof. intros W H. rewrite -> add_iff by exact W. auto. Qed.
  Lemma add_3 s x y : WF s -> ~ E.eq x y -> In y (add x s) -> In y s.
  Proof. intros W H. rewrite -> add_iff by exact W. tauto. Qed.
  Lemma remove_1 s x y : WF s -> E.eq x y -> ~ In y (remove x s).
  Proof. intros W H. rewrite -> remove_iff by exact W. tauto. Qed.
  Lemma remove_2 s x y : WF s -> ~ E.eq x y -> In y s -> In y (remove x s).
  Proof. intros W H. rewrite -> remove_iff by exact W. tauto. Qed.
  Lemma remove_3 s x y : WF s -> In y (remove x s) -> In y s.
  Proof. intros W. rewrite -> remove_iff by exact W. tauto. Qed.
  Lemma singleton_1 x y : In y (singleton x) -> E.eq x y.
  Proof. apply (proj1 (singleton_iff x y)). Qed.
  Lemma singleton_2 x y : E.eq x y -> In y (singleton x).
  Proof. apply (proj2 (singleton_iff x y)). Qed.
  Lemma union_1 s t x : WF s -> WF t -> In x (union s t) -> In x s \/ In x t.
  Proof. intros W T; apply (proj1 (union_iff s t x W T)). Qed.
  Lemma union_2 s t x : WF s -> WF t -> In x s -> In x (union s t).
  Proof. intros W T H; apply (proj2 (union_iff s t x W T)); auto. Qed.
  Lemma union_3 s t x : WF s -> WF t -> In x t -> In x (union s t).
  Proof. intros W T H; apply (proj2 (union_iff s t x W T)); auto. Qed.
  Lemma diff_1 s t x : WF s -> WF t -> In x (diff s t) -> In x s.
  Proof. intros W T. rewrite -> diff_iff by assumption. tauto. Qed.
  Lemma diff_2 s t x : WF s -> WF t -> In x (diff s t) -> ~ In x t.
  Proof. intros W T. rewrite -> diff_iff by assumption. tauto. Qed.
  Lemma diff_3 s t x : WF s -> WF t -> In x s -> ~ In x t -> In x (diff s t).
  Proof. intros W T. rewrite -> diff_iff by assumption. tauto. Qed.
  Lemma filter_1 s x f : WF s ->
    In x (filter f s) -> In x s.
  Proof.
    intro W. unfold In, filter.
    rewrite -> (elemVarSet_lookup _ _ (filterVarSet_WF f s W)),
      (lookupVarSet_filter f s x W), (elemVarSet_lookup s x W).
    destruct (lookupVarSet s x) as [v|]; [destruct (f v)|];
      simpl; intuition discriminate.
  Qed.
  Lemma filter_2 s x f : WF s -> ValidVarSet s -> RespectsVar f ->
    In x (filter f s) -> f x = true.
  Proof. intros W V R. rewrite -> filter_iff by assumption. tauto. Qed.
  Lemma filter_3 s x f : WF s -> ValidVarSet s -> RespectsVar f ->
    In x s -> f x = true -> In x (filter f s).
  Proof. intros W V R. rewrite -> filter_iff by assumption. tauto. Qed.
  Lemma inter_1 s t x : WF s -> WF t -> In x (inter s t) -> In x s.
  Proof. intros W T. rewrite -> inter_iff by assumption. tauto. Qed.
  Lemma inter_2 s t x : WF s -> WF t -> In x (inter s t) -> In x t.
  Proof. intros W T. rewrite -> inter_iff by assumption. tauto. Qed.
  Lemma inter_3 s t x : WF s -> WF t -> In x s -> In x t -> In x (inter s t).
  Proof. intros W T. rewrite -> inter_iff by assumption. tauto. Qed.
  Lemma for_all_1 s f : WF s -> ValidVarSet s -> RespectsVar f ->
    For_all (fun x => f x = true) s -> for_all f s = true.
  Proof. intros W V R. apply (proj1 (for_all_iff s f W V R)). Qed.
  Lemma for_all_2 s f : WF s -> ValidVarSet s -> RespectsVar f ->
    for_all f s = true -> For_all (fun x => f x = true) s.
  Proof. intros W V R. apply (proj2 (for_all_iff s f W V R)). Qed.
  Lemma exists_1 s f : WF s -> ValidVarSet s -> RespectsVar f ->
    Exists (fun x => f x = true) s -> exists_ f s = true.
  Proof. intros W V R. apply (proj1 (exists_iff s f W V R)). Qed.
  Lemma exists_2 s f : WF s -> ValidVarSet s -> RespectsVar f ->
    exists_ f s = true -> Exists (fun x => f x = true) s.
  Proof. intros W V R. apply (proj2 (exists_iff s f W V R)). Qed.
End VarSetBasicFacts.
Export VarSetBasicFacts.
Module F := VarSetFacts.
Module MP := VarSetProperties.
Module Notin.
  Ltac destruct_notin := set_iff.
  Ltac solve_notin := fsetdec.
End Notin.
