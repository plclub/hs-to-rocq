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
