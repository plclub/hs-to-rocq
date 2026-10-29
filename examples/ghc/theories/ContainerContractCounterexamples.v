(* The WF premises in ContainerProofs exclude these malformed raw trees.
   Each counterexample follows by computation, without a blanket WF axiom. *)
From Coq Require Import NArith List.
Require Import GHC.Base Data.IntMap.Internal.
Require Proofs.ContainerProofs.

Local Open Scope N_scope.

Lemma lookup_insert_neq_malformed :
  Data.IntMap.Internal.lookup 4
    (insert 5 tt (Bin 0 1 (Tip 4 tt) Nil)) <>
  Data.IntMap.Internal.lookup 4 (Bin 0 1 (Tip 4 tt) Nil).
Proof. vm_compute. discriminate. Qed.

Lemma member_insert_malformed :
  Data.IntMap.Internal.member 4
    (insert 2 tt (Bin 0 3 (Tip 4 tt) Nil)) <>
  orb (N.eqb 4 2) (Data.IntMap.Internal.member 4 (Bin 0 3 (Tip 4 tt) Nil)).
Proof. vm_compute. discriminate. Qed.

Lemma non_member_lookup_malformed :
  ~ (Data.IntMap.Internal.member 4 (Bin 0 1 (Tip 4 tt) Nil) = false <->
     Data.IntMap.Internal.lookup 4 (Bin 0 1 (Tip 4 tt) Nil) = None).
Proof. vm_compute. intros [H _]. discriminate (H eq_refl). Qed.

Lemma member_lookup_malformed :
  ~ (Data.IntMap.Internal.member 4 (Bin 0 1 (Tip 4 tt) Nil) = true <->
     exists v, Data.IntMap.Internal.lookup 4 (Bin 0 1 (Tip 4 tt) Nil) = Some v).
Proof.
  vm_compute. intros [_ H].
  assert (E : false = true) by (apply H; exists tt; reflexivity).
  discriminate.
Qed.

Lemma null_member_malformed :
  ~ (Data.IntMap.Internal.null (Bin 0 1 (@Nil unit) Nil) = true <->
     forall k, Data.IntMap.Internal.member k (Bin 0 1 (@Nil unit) Nil) = false).
Proof.
  intros [_ H].
  assert (E : false = true).
  { apply H. intro k. simpl.
    destruct (nomatch k 0 1); [reflexivity |].
    destruct (Data.IntSet.Internal.zero k 1); reflexivity. }
  discriminate.
Qed.

Lemma tree_elem_kv_lookup_malformed :
  ~ (ContainerProofs.tree_elem_kv 4 tt (Bin 0 1 Nil (Tip 4 tt)) ->
     Data.IntMap.Internal.lookup 4 (Bin 0 1 Nil (Tip 4 tt)) = Some tt).
Proof.
  intro H.
  assert (Hin : ContainerProofs.tree_elem_kv 4 tt (Bin 0 1 Nil (Tip 4 tt))).
  { right. split; reflexivity. }
  specialize (H Hin). vm_compute in H. discriminate.
Qed.

(* The rejected universal invariant is refutable without any axiom. *)
Lemma all_IntMaps_WF_false :
  ~ (forall A (m : Data.IntMap.Internal.IntMap A), IntMapProofs.WF m).
Proof.
  intro Hwf. apply non_member_lookup_malformed.
  apply ContainerProofs.non_member_lookup. exact (Hwf _ _).
Qed.

(* An unguarded equation for every functional admits the negation diagonal.
   IntMapRecursion proves equations only after establishing termination. *)
Lemma unguarded_deferredFix2_eq_false :
  ~ (forall a b r (d : HsToRocq.Err.Default r)
       (f : (a -> b -> r) -> a -> b -> r),
       @HsToRocq.DeferredFix.deferredFix2 a b r d f =
       f (@HsToRocq.DeferredFix.deferredFix2 a b r d f)).
Proof.
  intro Heq.
  pose (f := fun (g : unit -> unit -> bool) x y => negb (g x y)).
  pose proof (Heq unit unit bool HsToRocq.Err.default_bool f) as H.
  apply (f_equal (fun g => g tt tt)) in H.
  change (HsToRocq.DeferredFix.deferredFix2 f tt tt =
    negb (HsToRocq.DeferredFix.deferredFix2 f tt tt)) in H.
  destruct (HsToRocq.DeferredFix.deferredFix2 f tt tt); discriminate.
Qed.

Require Proofs.Axioms.

(* A structurally valid singleton can still violate the value/key invariant.
   Reusing one Var's fields avoids assumptions about particular payloads. *)
Lemma all_VarSets_valid_false :
  ~ (forall s, Axioms.ValidVarSet s).
Proof.
  intro Hvalid.
  destruct (HsToRocq.Err.default : Core.Var) as [n u ty mult sc d i].
  pose (v0 := Core.Mk_Id n (Unique.MkUnique 0) ty mult sc d i).
  pose (v1 := Core.Mk_Id n (Unique.MkUnique 1) ty mult sc d i).
  pose (bad := UniqSet.Mk_UniqSet (UniqFM.UFM (Tip 0 v1))).
  pose proof (Hvalid bad v0 v1 eq_refl) as H.
  change (false = true) in H. discriminate.
Qed.

Print Assumptions all_IntMaps_WF_false.
Print Assumptions unguarded_deferredFix2_eq_false.
Print Assumptions all_VarSets_valid_false.
