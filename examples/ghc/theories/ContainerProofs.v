(* Properties of IntMap operations.
   All properties are proved as Lemmas using two foundational Axioms
   imported from IntMapProofs:
   - deferredFix2_eq: one-step unfolding of the deferred fixpoint combinator
   - All_IntMaps_WF: all IntMaps are well-formed patricia tries

   Stated in terms of Data.IntMap.Internal operations directly,
   since VarSet/UniqFM unfolds to Internal operations. *)

From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Coq.NArith.BinNat.
Require Import Coq.Arith.Wf_nat.
Require Import Lia.
Require Import Coq.Program.Equality.

Require Import GHC.Base.

Require Import Proofs.Prelude.
Require Import Data.IntMap.Internal.
Require IntMap.

(* Require (without Import) to access IntMapProofs.Sem etc. for WF-based proofs.
   NOTE: This transitively loads mathcomp which sets Asymmetric Patterns globally.
   Downstream files must handle this (Unset Asymmetric Patterns if needed). *)
Require IntMapProofs.

(* Import DyadicIntervals for range lemmas (isSubrange, halfRange, etc.) *)
Require Import DyadicIntervals.
(* Import MapProofs.Bounds for the 'oro' (option-or) combinator *)
Require Import MapProofs.Bounds.
(* Import IntSetProofs for zero_spec *)
Require Import IntSetProofs.

Set Bullet Behavior "Strict Subproofs".

(* ============================================================ *)
(* Eq_sym_Word: (x == y) = (y == x) for Word/N                 *)
(* ============================================================ *)

Local Lemma Eq_sym_Word : forall (x y : GHC.Num.Word), (x == y) = (y == x).
Proof.
  intros x y. unfold op_zeze__, Eq_Word___.
  apply N.eqb_sym.
Qed.

(* ============================================================ *)
(* Core infrastructure: Sem2 and lookup_Sem2                     *)
(* ============================================================ *)

(* Sem implies Sem2 agreement *)
Local Lemma WF_Bin_children : forall {a} p msk (l r : IntMap.IntMap a),
  IntMapProofs.WF (Bin p msk l r) ->
  IntMapProofs.WF l /\ IntMapProofs.WF r.
Proof.
  intros a p msk l r [f Hf].
  inversion Hf.
  apply Eqdep.EqdepTheory.inj_pair2 in H1.
  apply Eqdep.EqdepTheory.inj_pair2 in H2.
  subst.
  inversion HD.
  repeat match goal with
    | Heq : existT _ _ _ = existT _ _ _ |- _ =>
        apply Eqdep.EqdepTheory.inj_pair2 in Heq
  end.
  subst.
  split; eexists; eapply IntMapProofs.DescSem; eassumption.
Qed.

(* For WF maps, lookup equals the compositional Sem2.
   Proved directly by structural induction on the map, avoiding
   dependency on Sem induction with Asymmetric Patterns. *)
Local Lemma lookup_Sem2 : forall {a} (s : IntMap.IntMap a) k,
  IntMapProofs.WF s -> Data.IntMap.Internal.lookup k s = IntMapProofs.Sem2 s k.
Proof.
  intros a s.
  induction s as [p msk l IHl r IHr | kx vx | ]; intros k HWF.
  - (* Bin case: use zero_oro to convert the if/then/else to oro *)
    destruct (WF_Bin_children p msk l r HWF) as [HWFl HWFr].
    simpl Data.IntMap.Internal.lookup. simpl IntMapProofs.Sem2.
    (* Rewrite by IH *)
    rewrite (IHl k HWFl). rewrite (IHr k HWFr).
    (* Goal: if zero k msk then Sem2 l k else Sem2 r k = oro (Sem2 l k) (Sem2 r k) *)
    (* Extract Desc of Bin via WF to get range structure *)
    destruct HWF as [f Hf].
    (* Get the Desc for each subtree from the parent's Sem evidence. *)
    (* For the range info, use the fact that WF (Bin p msk l r) gives us Desc *)
    (* Specifically: from Desc (Bin p msk l r) rr f, we get:
       Desc l r1 ff1, Desc r r2 ff2,
       (0 < rBits rr), isSubrange r1 (halfRange rr false), isSubrange r2 (halfRange rr true)
       and zero_oro applies with rr, r1, r2 *)
    (* Approach: use lookup_Desc directly and zero_oro at the f level *)
    (* f is the sem function, and we need:
       if zero k msk then Sem2 l k else Sem2 r k = oro (Sem2 l k) (Sem2 r k) *)
    (* This holds iff one of them is None, which follows from the Desc structure *)
    (* Use IntMapProofs.lookup_Sem and zero_oro to get there *)
    (* But we need the range rr. Let's use the fact that Desc (Bin p msk l r) rr f
       where rr has p = rPrefix rr, msk = rMask rr *)
    (* Get Desc explicitly via a helper *)
    (* Get Desc of the Bin from Sem via inversion *)
    (* Use Sem_Bin_Desc to get subtree Descs and range info *)
    (* But Sem_Bin_Desc is defined after lookup_Sem2; use inline version *)
    assert (HDbin : exists rr, IntMapProofs.Desc (Bin p msk l r) rr f).
    { inversion Hf.
      apply Eqdep.EqdepTheory.inj_pair2 in H1.
      apply Eqdep.EqdepTheory.inj_pair2 in H2.
      subst. eauto. }
    destruct HDbin as [rr HDbin].
    (* Now invert the DescBin to get subtree Descs and range info *)
    inversion HDbin.
    repeat match goal with
      | Heq : existT _ _ _ = existT _ _ _ |- _ =>
          apply Eqdep.EqdepTheory.inj_pair2 in Heq
    end.
    subst.
    (* Now we have the Desc hypotheses for the subtrees. Identify which ones are
       for l and r. They are named by Coq automatically. *)
    rename H4 into HHD1. rename H5 into HHD2.
    rename H6 into Hbits. rename H8 into Hsub1. rename H10 into Hsub2.
    apply (IntMapProofs.zero_oro k rr (IntMapProofs.Sem2 l) (IntMapProofs.Sem2 r) r1 r2 Hbits Hsub1 Hsub2).
    + intro Hout.
      rewrite <- (IHl k HWFl).
      rewrite (IntMapProofs.lookup_Sem (IntMapProofs.DescSem _ _ _ HHD1)).
      exact (IntMapProofs.Desc_outside HHD1 Hout).
    + intro Hout.
      rewrite <- (IHr k HWFr).
      rewrite (IntMapProofs.lookup_Sem (IntMapProofs.DescSem _ _ _ HHD2)).
      exact (IntMapProofs.Desc_outside HHD2 Hout).
  - (* Tip case *)
    simpl. destruct (k == kx) eqn:Hkkx.
    + move: Hkkx => /Eq_eq_Word Hkkx. subst. rewrite Eq_refl. reflexivity.
    + destruct (kx == k) eqn:Hkxk.
      * move: Hkxk => /Eq_eq_Word Hkxk. subst. rewrite Eq_refl in Hkkx. discriminate.
      * reflexivity.
  - reflexivity.
Qed.

(* Derived: Sem agrees with Sem2 *)
Local Lemma Sem_Sem2 : forall {a} (s : IntMap.IntMap a) f,
  IntMapProofs.Sem s f -> forall k, f k = IntMapProofs.Sem2 s k.
Proof.
  intros a s f Hf k.
  pose proof (IntMapProofs.lookup_Sem Hf (i := k)) as Hlook.
  (* Hlook : lookup k s = f k *)
  pose proof (lookup_Sem2 s k (ex_intro _ f Hf)) as Hls2.
  (* Hls2 : lookup k s = Sem2 s k *)
  congruence.
Qed.

(* Sem2 of Bin decomposes compositionally *)
Local Lemma Sem2_Bin : forall {a} p msk (l r : IntMap.IntMap a) k,
  IntMapProofs.Sem2 (Bin p msk l r) k = oro (IntMapProofs.Sem2 l k) (IntMapProofs.Sem2 r k).
Proof. reflexivity. Qed.

(* For WF Bins, lookup decomposes compositionally (no routing dependency) *)
Local Lemma lookup_Bin_oro : forall {a} p msk (l r : IntMap.IntMap a) k,
  IntMapProofs.WF (Bin p msk l r) ->
  Data.IntMap.Internal.lookup k (Bin p msk l r) = oro (Data.IntMap.Internal.lookup k l) (Data.IntMap.Internal.lookup k r).
Proof.
  intros a p msk l r k HWF.
  rewrite (lookup_Sem2 _ k HWF). simpl.
  destruct (WF_Bin_children p msk l r HWF) as [HWFl HWFr].
  rewrite <- (lookup_Sem2 l k HWFl).
  rewrite <- (lookup_Sem2 r k HWFr).
  reflexivity.
Qed.

(* oro lemmas *)
Local Lemma oro_None_r {a} (x : option a) : oro x None = x.
Proof. destruct x; reflexivity. Qed.

Local Lemma oro_None_l {a} (x : option a) : oro None x = x.
Proof. reflexivity. Qed.

Local Lemma oro_assoc {a} (x y z : option a) : oro (oro x y) z = oro x (oro y z).
Proof. destruct x; reflexivity. Qed.

Local Lemma oro_Some {a} (v:a) x y : oro x y = Some v -> x = Some v \/ y = Some v.
Proof. destruct x; simpl; intros H; [left; exact H | right; exact H]. Qed.

Local Lemma oro_None_inv : forall {a} (x y : option a),
  oro x y = None -> x = None /\ y = None.
Proof. intros a [] []; simpl; intros H; try discriminate; auto. Qed.

(* ============================================================ *)
(* Proved lemmas: universally true (no WF needed)               *)
(* ============================================================ *)

Lemma null_empty : forall A,
    (@Data.IntMap.Internal.null A Data.IntMap.Internal.empty).
Proof. intros. reflexivity. Qed.

Lemma lookup_eq : forall A k k' (i : IntMap.IntMap A),
    k == k' ->
    Data.IntMap.Internal.lookup k i = Data.IntMap.Internal.lookup k' i.
Proof. intros A k k' i. move => /Eq_eq_Word ->. reflexivity. Qed.

Lemma member_eq : forall A k k' (i : IntMap.IntMap A),
    k == k' ->
    Data.IntMap.Internal.member k i = Data.IntMap.Internal.member k' i.
Proof. intros A k k' i. move => /Eq_eq_Word ->. reflexivity. Qed.

Lemma member_singleton : forall A k k' (v : A),
    Data.IntMap.Internal.member k (Data.IntMap.Internal.singleton k' v) = (k == k').
Proof. intros. simpl. reflexivity. Qed.

Lemma lookup_singleton_key : forall {A} x y (a b : A),
    Data.IntMap.Internal.lookup x (Data.IntMap.Internal.singleton y a) = Some b -> x == y.
Proof.
  intros A x y a b. simpl.
  destruct (x == y) eqn:Heq; [auto | intros H; discriminate].
Qed.

Lemma lookup_singleton_val : forall {A} x y (a b : A),
    Data.IntMap.Internal.lookup x (Data.IntMap.Internal.singleton y a) = Some b -> a = b.
Proof.
  intros A x y a b. simpl.
  destruct (x == y) eqn:Heq; [intros H; congruence | intros H; discriminate].
Qed.

(* Helper: lookup through link always finds the linked key. *)
Local Lemma lookup_link_self : forall A key (val : A) p2 t2,
  Data.IntMap.Internal.lookup key (link key (Tip key val) p2 t2) = Some val.
Proof.
  intros. unfold link, linkWithMask.
  destruct (Data.IntSet.Internal.zero key (branchMask key p2)) eqn:Hz;
  simpl; rewrite Hz; rewrite Eq_refl; reflexivity.
Qed.

Lemma lookup_insert : forall A key (val:A) i,
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.insert key val i) = Some val.
Proof.
  intros A key val.
  induction i as [p m l IHl r IHr | ky vy | ].
  - simpl. destruct (nomatch key p m) eqn:Hnm.
    + apply lookup_link_self.
    + destruct (Data.IntSet.Internal.zero key m) eqn:Hz; simpl; rewrite Hz; auto.
  - simpl. destruct (key == ky) eqn:Heq.
    + simpl. rewrite Eq_refl. reflexivity.
    + apply lookup_link_self.
  - simpl. rewrite Eq_refl. reflexivity.
Qed.

(* deferredFix2-based lemmas with Nil arguments *)

Lemma difference_nil_l : forall B A (i : IntMap.IntMap A),
    Data.IntMap.Internal.difference (@Data.IntMap.Internal.empty B) i =
    (@Data.IntMap.Internal.empty B).
Proof.
  intros. unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.empty.
  unfold mergeWithKey. unfold mergeWithKey'.
  rewrite IntMapProofs.deferredFix2_eq. reflexivity.
Qed.

Lemma difference_nil_r : forall A B (i : IntMap.IntMap A),
    Data.IntMap.Internal.difference i (@Data.IntMap.Internal.empty B) = i.
Proof.
  intros. unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.empty.
  unfold mergeWithKey. unfold mergeWithKey'.
  rewrite IntMapProofs.deferredFix2_eq.
  destruct i; reflexivity.
Qed.

Lemma disjoint_empty_l : forall A B (j : IntMap.IntMap B),
  Data.IntMap.Internal.disjoint (@Data.IntMap.Internal.empty A) j = true.
Proof.
  intros. unfold Data.IntMap.Internal.disjoint, Data.IntMap.Internal.empty.
  rewrite IntMapProofs.deferredFix2_eq. reflexivity.
Qed.

Lemma disjoint_empty_r : forall A B (i : IntMap.IntMap A),
  Data.IntMap.Internal.disjoint i (@Data.IntMap.Internal.empty B) = true.
Proof.
  intros. unfold Data.IntMap.Internal.disjoint, Data.IntMap.Internal.empty.
  rewrite IntMapProofs.deferredFix2_eq. destruct i; reflexivity.
Qed.

Lemma intersection_empty :
  forall A B (i : IntMap.IntMap A) (j : IntMap.IntMap B),
    (j = Data.IntMap.Internal.empty) ->
    Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i j).
Proof.
  intros A B i j Hj. subst.
  unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.empty.
  unfold mergeWithKey'.
  rewrite IntMapProofs.deferredFix2_eq.
  destruct i; reflexivity.
Qed.

(* ============================================================ *)
(* Proved lemmas: via IntMapProofs.Sem (WF-dependent)            *)
(* Uses IntMapProofs.All_IntMaps_WF axiom to obtain Sem witnesses.           *)
(* ============================================================ *)

Lemma non_member_lookup :
   forall (A : Type) (key : Internal.Key) (i : IntMap.IntMap A),
   (Data.IntMap.Internal.member key i = false) <-> (Data.IntMap.Internal.lookup key i = None).
Proof.
  intros A key i.
  destruct (IntMapProofs.All_IntMaps_WF _ i) as [f Hf].
  rewrite (IntMapProofs.lookup_Sem Hf) (IntMapProofs.member_Sem Hf).
  destruct (f key); split; intro H; try discriminate; reflexivity.
Qed.

Lemma member_lookup :
   forall (A : Type) (key : Internal.Key) (i : IntMap.IntMap A),
   (is_true (Data.IntMap.Internal.member key i)) <-> (exists val, Data.IntMap.Internal.lookup key i = Some val).
Proof.
  intros A key i.
  destruct (IntMapProofs.All_IntMaps_WF _ i) as [f Hf].
  rewrite (IntMapProofs.lookup_Sem Hf) (IntMapProofs.member_Sem Hf).
  destruct (f key) as [v|].
  - split; [intro; exists v; reflexivity | auto].
  - split; [intro H; discriminate | intros [v Hv]; discriminate].
Qed.

(* The forward direction needs no well-formedness: member follows lookup's
   routing after its additional prefix check succeeds. *)
Lemma member_lookup_some : forall A k (m : IntMap.IntMap A),
  Data.IntMap.Internal.member k m = true ->
  exists v, Data.IntMap.Internal.lookup k m = Some v.
Proof.
  intros A k m.
  induction m as [p msk l IHl r IHr | k' v' | ]; simpl.
  - destruct (Data.IntMap.Internal.nomatch k p msk); [discriminate |].
    destruct (Data.IntSet.Internal.zero k msk).
    + exact IHl.
    + exact IHr.
  - intro H. rewrite H. exists v'. reflexivity.
  - discriminate.
Qed.

Lemma null_member : forall A (m : IntMap.IntMap A),
    Data.IntMap.Internal.null m = true <-> (forall k, Data.IntMap.Internal.member k m = false).
Proof.
  intros A m.
  destruct (IntMapProofs.All_IntMaps_WF _ m) as [f Hf].
  rewrite (IntMapProofs.null_Sem Hf).
  split.
  - intros Hnil k. rewrite (IntMapProofs.member_Sem Hf). rewrite Hnil. reflexivity.
  - intros Hmem i. specialize (Hmem i).
    rewrite (IntMapProofs.member_Sem Hf) in Hmem.
    destruct (f i); [discriminate | reflexivity].
Qed.

Lemma lookup_insert_neq :
  forall b key1 key2 (val:b) m,
    key1 <> key2 ->
    Data.IntMap.Internal.lookup key1 (Data.IntMap.Internal.insert key2 val m) = Data.IntMap.Internal.lookup key1 m.
Proof.
  intros b key1 key2 val m Hneq.
  destruct (IntMapProofs.All_IntMaps_WF _ m) as [f Hf].
  set (f' := fun i => if (i =? key2)%N then Some val else f i).
  assert (Hins : IntMapProofs.Sem (insert key2 val m) f').
  { exact (IntMapProofs.insert_Sem _ key2 val m f f' Hf (fun i => Logic.eq_refl)). }
  rewrite (IntMapProofs.lookup_Sem Hins) (IntMapProofs.lookup_Sem Hf). unfold f'.
  destruct (N.eqb_spec key1 key2); [congruence | reflexivity].
Qed.

Lemma member_insert : forall A k k' v (i : IntMap.IntMap A),
  Data.IntMap.Internal.member k (Data.IntMap.Internal.insert k' v i) =
  (k == k') || Data.IntMap.Internal.member k i.
Proof.
  intros A k k' v i.
  destruct (IntMapProofs.All_IntMaps_WF _ i) as [f Hf].
  set (f' := fun j => if (j =? k')%N then Some v else f j).
  assert (Hins : IntMapProofs.Sem (insert k' v i) f').
  { exact (IntMapProofs.insert_Sem _ k' v i f f' Hf (fun j => Logic.eq_refl)). }
  rewrite (IntMapProofs.member_Sem Hins) (IntMapProofs.member_Sem Hf). unfold f'.
  change (k == k') with ((k =? k')%N).
  destruct (N.eqb_spec k k') as [->|ne]; simpl; reflexivity.
Qed.

(* ============================================================ *)
(* Delete: proved via Sem2 + structural induction                *)
(* ============================================================ *)

(* Helper to get Desc of a Bin from its Sem *)
Local Lemma Sem_Bin_Desc : forall {a} p msk (l r : IntMap.IntMap a) f,
  IntMapProofs.Sem (Bin p msk l r) f ->
  exists rr r1 ff1 r2 ff2,
    IntMapProofs.Desc l r1 ff1 /\
    IntMapProofs.Desc r r2 ff2 /\
    (0 < rBits rr)%N /\
    isSubrange r1 (halfRange rr false) = true /\
    isSubrange r2 (halfRange rr true) = true /\
    (forall i, f i = oro (ff1 i) (ff2 i)) /\
    p = rPrefix rr /\
    msk = rMask rr.
Proof.
  intros a p msk l r f Hf.
  (* Step 1: inversion on Sem gives us a Desc of the whole Bin *)
  inversion Hf.
  apply Eqdep.EqdepTheory.inj_pair2 in H1.
  apply Eqdep.EqdepTheory.inj_pair2 in H2.
  subst.
  (* Now HD : Desc (Bin p msk l r) r0 f *)
  (* Step 2: inversion on DescBin gives subtree Descs *)
  inversion HD.
  (* Apply inj_pair2 to all existT equalities *)
  repeat match goal with
    | Heq : existT _ _ _ = existT _ _ _ |- _ =>
        apply Eqdep.EqdepTheory.inj_pair2 in Heq
  end.
  subst.
  (* Now we have: H4 : Desc l r1 f1, H5 : Desc r r2 f2, H6 : 0 < rBits r0, etc. *)
  eauto 14.
Qed.

(* Helper: for a WF Bin, a key routing left (zero key msk = true) has Sem2 = None in right subtree *)
(* Show inRange key (halfRange rr h) = false from the testbit value, without
   requiring inRange key rr = true (works for key both in and out of rr). *)
Local Lemma inRange_halfRange_false_of_testbit :
  forall rr key h,
  (0 < rBits rr)%N ->
  N.testbit key (rBits rr - 1) = negb h ->
  inRange key (halfRange rr h) = false.
Proof.
  intros rr key h Hbits Hbit.
  destruct (inRange key rr) eqn:HinR.
  - (* key is in rr: use testbit_halfRange_false *)
    rewrite (testbit_halfRange_false rr key h Hbits HinR).
    exact Hbit.
  - (* key is not in rr: halfRange rr h ⊆ rr, so key not in halfRange *)
    eapply inRange_isSubrange_false.
    + exact (isSubrange_halfRange rr h Hbits).
    + exact HinR.
Qed.

Local Lemma WF_Bin_left_key_not_right : forall {a} p msk (l r : IntMap.IntMap a) key,
  IntMapProofs.WF (Bin p msk l r) ->
  Data.IntSet.Internal.zero key msk = true ->
  IntMapProofs.Sem2 r key = None.
Proof.
  intros a p msk l r key HWF Hz.
  destruct HWF as [f Hf].
  destruct (Sem_Bin_Desc p msk l r f Hf) as (rr & r1 & ff1 & r2 & ff2 & HHD1 & HHD2 & Hbits & Hsub1 & Hsub2 & Hff0 & Hpp & Hmsk).
  (* zero key (rMask rr) = true -> N.testbit key (rBits rr - 1) = false *)
  pose proof (zero_spec key rr Hbits) as Hzero_spec.
  (* Hz : zero key msk = true. Hmsk : msk = rMask rr. *)
  rewrite Hmsk in Hz. rewrite Hz in Hzero_spec.
  (* Hzero_spec : true = negb (N.testbit key (rBits rr - 1))
     So N.testbit key (rBits rr - 1) = false *)
  assert (Hbit : N.testbit key (rBits rr - 1) = false).
  { apply Bool.negb_true_iff. exact (eq_sym Hzero_spec). }
  (* inRange key (halfRange rr true) = false *)
  assert (Hnot_right : inRange key (halfRange rr true) = false).
  { apply inRange_halfRange_false_of_testbit. exact Hbits. simpl. exact Hbit. }
  (* inRange key r2 = false *)
  assert (Hout2 : inRange key r2 = false).
  { eapply inRange_isSubrange_false. exact Hsub2. exact Hnot_right. }
  (* ff2 key = None *)
  assert (Hff2_none : ff2 key = None).
  { exact (IntMapProofs.Desc_outside HHD2 Hout2). }
  rewrite <- (Sem_Sem2 _ _ (IntMapProofs.DescSem _ _ _ HHD2) key).
  exact Hff2_none.
Qed.

Local Lemma WF_Bin_right_key_not_left : forall {a} p msk (l r : IntMap.IntMap a) key,
  IntMapProofs.WF (Bin p msk l r) ->
  Data.IntSet.Internal.zero key msk = false ->
  IntMapProofs.Sem2 l key = None.
Proof.
  intros a p msk l r key HWF Hz.
  destruct HWF as [f Hf].
  destruct (Sem_Bin_Desc p msk l r f Hf) as (rr & r1 & ff1 & r2 & ff2 & HHD1 & HHD2 & Hbits & Hsub1 & Hsub2 & Hff0 & Hpp & Hmsk).
  pose proof (zero_spec key rr Hbits) as Hzero_spec.
  rewrite Hmsk in Hz. rewrite Hz in Hzero_spec.
  (* Hzero_spec : false = negb (N.testbit key (rBits rr - 1))
     So N.testbit key (rBits rr - 1) = true *)
  assert (Hbit : N.testbit key (rBits rr - 1) = true).
  { apply Bool.negb_false_iff. exact (eq_sym Hzero_spec). }
  (* inRange key (halfRange rr false) = false *)
  assert (Hnot_left : inRange key (halfRange rr false) = false).
  { apply inRange_halfRange_false_of_testbit. exact Hbits. simpl. exact Hbit. }
  (* inRange key r1 = false *)
  assert (Hout1 : inRange key r1 = false).
  { eapply inRange_isSubrange_false. exact Hsub1. exact Hnot_left. }
  assert (Hff1_none : ff1 key = None).
  { exact (IntMapProofs.Desc_outside HHD1 Hout1). }
  rewrite <- (Sem_Sem2 _ _ (IntMapProofs.DescSem _ _ _ HHD1) key).
  exact Hff1_none.
Qed.

(* Key lemma: delete removes exactly one key from the Sem2 semantics *)
Local Lemma Sem2_delete : forall {a} key (m : IntMap.IntMap a) k,
  IntMapProofs.WF m ->
  IntMapProofs.Sem2 (Data.IntMap.Internal.delete key m) k =
  (if (k =? key)%N then None else IntMapProofs.Sem2 m k).
Proof.
  intros a key m.
  induction m as [p msk l IHl r IHr | ky vy | ]; intros k HWF.
  - (* Bin case *)
    simpl Data.IntMap.Internal.delete.
    destruct (nomatch key p msk) eqn:Hnm.
    + (* nomatch: delete returns Bin p msk l r unchanged *)
      simpl IntMapProofs.Sem2.
      destruct (k =? key)%N eqn:Hkkey; [|reflexivity].
      apply N.eqb_eq in Hkkey. subst k.
      (* nomatch means key is not in range of Bin, so Sem2 key = None *)
      assert (Hlook_sem2 : IntMapProofs.Sem2 (Bin p msk l r) key = None).
      { destruct HWF as [f Hf].
        rewrite <- (Sem_Sem2 _ _ Hf key).
        (* Goal: f key = None. Use Desc_outside. *)
        assert (HDB : exists rr, IntMapProofs.Desc (Bin p msk l r) rr f).
        { inversion Hf.
          apply Eqdep.EqdepTheory.inj_pair2 in H1.
          apply Eqdep.EqdepTheory.inj_pair2 in H2.
          subst. eauto. }
        destruct HDB as [rr HDB].
        (* Invert HDB to get rr_bits and the p=rPrefix/msk=rMask equalities *)
        assert (Hrr_bits : (0 < rBits rr)%N).
        { inversion HDB.
          repeat match goal with
            | Heq : existT _ _ _ = existT _ _ _ |- _ =>
                apply Eqdep.EqdepTheory.inj_pair2 in Heq
          end.
          subst. assumption. }
        assert (Hnm_rr : nomatch key (rPrefix rr) (rMask rr) = true).
        { inversion HDB.
          repeat match goal with
            | Heq : existT _ _ _ = existT _ _ _ |- _ =>
                apply Eqdep.EqdepTheory.inj_pair2 in Heq
          end.
          subst. exact Hnm. }
        eapply IntMapProofs.Desc_outside. exact HDB.
        rewrite <- Bool.negb_true_iff.
        rewrite <- IntMapProofs.nomatch_spec; [exact Hnm_rr | exact Hrr_bits]. }
      simpl in Hlook_sem2. exact Hlook_sem2.
    + (* match: route via zero *)
      destruct (Data.IntSet.Internal.zero key msk) eqn:Hz.
      * (* zero = true: delete from left *)
        unfold binCheckLeft.
        destruct (Data.IntMap.Internal.delete key l) as [p' msk' l' r' | ky' vy' | ] eqn:Hdel.
        -- (* delete key l = Bin p' msk' l' r': result is Bin p msk (Bin p' msk' l' r') r *)
           (* IHl k WFl : Sem2 (Bin p' msk' l' r') k = if k=?key then None else Sem2 l k
              Goal: Sem2 (Bin p msk (Bin p' msk' l' r') r) k = if k=?key then None else Sem2 (Bin p msk l r) k *)
           (* Both sides = if k=?key then None else Sem2 l k ||| Sem2 r k *)
           (* Use congruence-like reasoning *)
           destruct (k =? key)%N eqn:Hkkey.
           ** (* k = key *)
              apply N.eqb_eq in Hkkey. subst k.
              assert (H_delL : IntMapProofs.Sem2 (Bin p' msk' l' r') key = None).
              { pose proof (IHl key (IntMapProofs.All_IntMaps_WF _ l)) as H.
                rewrite N.eqb_refl in H. exact H. }
              assert (H_r : IntMapProofs.Sem2 r key = None).
              { exact (WF_Bin_left_key_not_right p msk l r key HWF Hz). }
              (* Rewrite Sem2 of Bin using Sem2_Bin BEFORE simpl *)
              rewrite (Sem2_Bin p msk (Bin p' msk' l' r') r key).
              rewrite H_delL. rewrite H_r. simpl. reflexivity.
           ** (* k ≠ key *)
              assert (H_delL : IntMapProofs.Sem2 (Bin p' msk' l' r') k = IntMapProofs.Sem2 l k).
              { pose proof (IHl k (IntMapProofs.All_IntMaps_WF _ l)) as H.
                rewrite Hkkey in H. exact H. }
              rewrite (Sem2_Bin p msk (Bin p' msk' l' r') r k).
              rewrite H_delL.
              rewrite (Sem2_Bin p msk l r k). reflexivity.
        -- (* delete key l = Tip ky' vy': result is Bin p msk (Tip ky' vy') r *)
           destruct (k =? key)%N eqn:Hkkey.
           ** apply N.eqb_eq in Hkkey. subst k.
              assert (H_delL : IntMapProofs.Sem2 (Tip ky' vy') key = None).
              { pose proof (IHl key (IntMapProofs.All_IntMaps_WF _ l)) as H.
                rewrite N.eqb_refl in H. exact H. }
              assert (H_r : IntMapProofs.Sem2 r key = None).
              { exact (WF_Bin_left_key_not_right p msk l r key HWF Hz). }
              rewrite (Sem2_Bin p msk (Tip ky' vy') r key).
              rewrite H_delL. rewrite H_r. simpl. reflexivity.
           ** assert (H_delL : IntMapProofs.Sem2 (Tip ky' vy') k = IntMapProofs.Sem2 l k).
              { pose proof (IHl k (IntMapProofs.All_IntMaps_WF _ l)) as H.
                rewrite Hkkey in H. exact H. }
              rewrite (Sem2_Bin p msk (Tip ky' vy') r k).
              rewrite H_delL.
              rewrite (Sem2_Bin p msk l r k). reflexivity.
        -- (* delete key l = Nil: result is r *)
           (* Goal: Sem2 r k = if k=?key then None else Sem2 (Bin p msk l r) k *)
           (* IHl : Sem2 Nil k = if k=?key then None else Sem2 l k  [i.e., None = ...] *)
           destruct (k =? key)%N eqn:Hkkey.
           ++ (* k = key: Sem2 r key = None *)
              apply N.eqb_eq in Hkkey. subst k.
              apply (WF_Bin_left_key_not_right p msk l r key HWF Hz).
           ++ (* k ≠ key: Sem2 r k = Sem2 (Bin p msk l r) k = oro (Sem2 l k) (Sem2 r k) *)
              (* From IHl: None = Sem2 l k (since Sem2 Nil k = None = Sem2 l k for k≠key) *)
              assert (Hl_k_none : IntMapProofs.Sem2 l k = None).
              { pose proof (IHl k (IntMapProofs.All_IntMaps_WF _ l)) as H.
                rewrite Hkkey in H.
                (* H : None = Sem2 l k *)
                exact (eq_sym H). }
              rewrite (Sem2_Bin p msk l r k).
              rewrite Hl_k_none. reflexivity.
      * (* zero = false: delete from right *)
        unfold binCheckRight.
        destruct (Data.IntMap.Internal.delete key r) as [p' msk' l' r' | ky' vy' | ] eqn:Hdel.
        -- (* delete key r = Bin p' msk' l' r': result is Bin p msk l (Bin p' msk' l' r') *)
           destruct (k =? key)%N eqn:Hkkey.
           ** apply N.eqb_eq in Hkkey. subst k.
              assert (H_delR : IntMapProofs.Sem2 (Bin p' msk' l' r') key = None).
              { pose proof (IHr key (IntMapProofs.All_IntMaps_WF _ r)) as H.
                rewrite N.eqb_refl in H. exact H. }
              assert (H_l : IntMapProofs.Sem2 l key = None).
              { exact (WF_Bin_right_key_not_left p msk l r key HWF Hz). }
              rewrite (Sem2_Bin p msk l (Bin p' msk' l' r') key).
              rewrite H_delR. rewrite H_l. simpl. reflexivity.
           ** assert (H_delR : IntMapProofs.Sem2 (Bin p' msk' l' r') k = IntMapProofs.Sem2 r k).
              { pose proof (IHr k (IntMapProofs.All_IntMaps_WF _ r)) as H.
                rewrite Hkkey in H. exact H. }
              rewrite (Sem2_Bin p msk l (Bin p' msk' l' r') k).
              rewrite H_delR.
              rewrite (Sem2_Bin p msk l r k). reflexivity.
        -- (* delete key r = Tip ky' vy': result is Bin p msk l (Tip ky' vy') *)
           destruct (k =? key)%N eqn:Hkkey.
           ** apply N.eqb_eq in Hkkey. subst k.
              assert (H_delR : IntMapProofs.Sem2 (Tip ky' vy') key = None).
              { pose proof (IHr key (IntMapProofs.All_IntMaps_WF _ r)) as H.
                rewrite N.eqb_refl in H. exact H. }
              assert (H_l : IntMapProofs.Sem2 l key = None).
              { exact (WF_Bin_right_key_not_left p msk l r key HWF Hz). }
              rewrite (Sem2_Bin p msk l (Tip ky' vy') key).
              rewrite H_delR. rewrite H_l. simpl. reflexivity.
           ** assert (H_delR : IntMapProofs.Sem2 (Tip ky' vy') k = IntMapProofs.Sem2 r k).
              { pose proof (IHr k (IntMapProofs.All_IntMaps_WF _ r)) as H.
                rewrite Hkkey in H. exact H. }
              rewrite (Sem2_Bin p msk l (Tip ky' vy') k).
              rewrite H_delR.
              rewrite (Sem2_Bin p msk l r k). reflexivity.
        -- (* delete key r = Nil: result is l *)
           destruct (k =? key)%N eqn:Hkkey.
           ++ (* k = key: Sem2 l key = None *)
              apply N.eqb_eq in Hkkey. subst k.
              apply (WF_Bin_right_key_not_left p msk l r key HWF Hz).
           ++ (* k ≠ key: Sem2 r k = None, so Sem2 l k = Sem2 (Bin p msk l r) k *)
              assert (Hr_k_none : IntMapProofs.Sem2 r k = None).
              { pose proof (IHr k (IntMapProofs.All_IntMaps_WF _ r)) as H.
                rewrite Hkkey in H.
                exact (eq_sym H). }
              rewrite (Sem2_Bin p msk l r k).
              rewrite Hr_k_none. rewrite oro_None_r. reflexivity.
  - (* Tip case *)
    simpl.
    destruct (key == ky) eqn:Heq.
    + simpl.
      destruct (k =? key)%N eqn:Hkkey.
      * reflexivity.
      * (* k ≠ key but key == ky. Sem2 (Tip ky vy) k *)
        move: Heq => /Eq_eq_Word Heq. subst ky.
        simpl. destruct (key == k) eqn:Hkk.
        -- move: Hkk => /Eq_eq_Word Hkk. subst. rewrite N.eqb_refl in Hkkey. discriminate.
        -- reflexivity.
    + simpl.
      destruct (k =? key)%N eqn:Hkkey.
      * apply N.eqb_eq in Hkkey. subst k.
        simpl. rewrite Eq_sym_Word. rewrite Heq. reflexivity.
      * reflexivity.
  - (* Nil case *)
    simpl. destruct (k =? key)%N; reflexivity.
Qed.

(* ============================================================ *)
(* Helper infrastructure for union/difference/intersection       *)
(* ============================================================ *)

(* lookup on bin (smart constructor) distributes over oro, using WF *)
Local Lemma lookup_bin_oro : forall {a} p m (l r : IntMap.IntMap a) k,
  Data.IntMap.Internal.lookup k (bin p m l r) =
  oro (Data.IntMap.Internal.lookup k l) (Data.IntMap.Internal.lookup k r).
Proof.
  intros a p m l r k.
  unfold bin.
  destruct l as [pl ml ll rl | kl vl | ], r as [pr mr lr rr | kr vr | ].
  - apply lookup_Bin_oro. exact (IntMapProofs.All_IntMaps_WF _ _).
  - apply lookup_Bin_oro. exact (IntMapProofs.All_IntMaps_WF _ _).
  - rewrite oro_None_r. reflexivity.
  - apply lookup_Bin_oro. exact (IntMapProofs.All_IntMaps_WF _ _).
  - apply lookup_Bin_oro. exact (IntMapProofs.All_IntMaps_WF _ _).
  - rewrite oro_None_r. reflexivity.
  - rewrite oro_None_l. reflexivity.
  - rewrite oro_None_l. reflexivity.
  - reflexivity.
Qed.

(* Helper: oro commutes when we know which side routes to None *)
Local Lemma oro_comm_left_None : forall {a} (x y : option a),
  x = None -> oro x y = oro y x.
Proof. intros. subst. simpl. destruct y; reflexivity. Qed.

Local Lemma oro_comm_right_None : forall {a} (x y : option a),
  y = None -> oro x y = oro y x.
Proof. intros. subst. rewrite oro_None_r. destruct x; reflexivity. Qed.

(* lookup on link distributes over oro (left, then right preference) *)
Local Lemma lookup_link_oro : forall {a} p1 (t1 : IntMap.IntMap a) p2 t2 k,
  Data.IntMap.Internal.lookup k (link p1 t1 p2 t2) =
  oro (Data.IntMap.Internal.lookup k t1) (Data.IntMap.Internal.lookup k t2).
Proof.
  intros a p1 t1 p2 t2 k.
  unfold link, linkWithMask.
  set (m := branchMask p1 p2).
  set (p := Data.IntSet.Internal.mask p1 m).
  destruct (Data.IntSet.Internal.zero p1 m) eqn:Hz.
  - (* Bin p m t1 t2 *)
    simpl Data.IntMap.Internal.lookup.
    destruct (Data.IntSet.Internal.zero k m) eqn:Hzk.
    + (* k routes to t1 (left); t2 gives None *)
      pose proof (WF_Bin_left_key_not_right p m t1 t2 k
        (IntMapProofs.All_IntMaps_WF _ (Bin p m t1 t2)) Hzk) as H.
      rewrite <- (lookup_Sem2 t2 k (IntMapProofs.All_IntMaps_WF _ t2)) in H.
      rewrite H. rewrite oro_None_r. reflexivity.
    + (* k routes to t2 (right); t1 gives None *)
      pose proof (WF_Bin_right_key_not_left p m t1 t2 k
        (IntMapProofs.All_IntMaps_WF _ (Bin p m t1 t2)) Hzk) as H.
      rewrite <- (lookup_Sem2 t1 k (IntMapProofs.All_IntMaps_WF _ t1)) in H.
      rewrite H. simpl. reflexivity.
  - (* Bin p m t2 t1 *)
    simpl Data.IntMap.Internal.lookup.
    destruct (Data.IntSet.Internal.zero k m) eqn:Hzk.
    + (* k routes to t2 (left); t1 gives None *)
      pose proof (WF_Bin_left_key_not_right p m t2 t1 k
        (IntMapProofs.All_IntMaps_WF _ (Bin p m t2 t1)) Hzk) as H.
      rewrite <- (lookup_Sem2 t1 k (IntMapProofs.All_IntMaps_WF _ t1)) in H.
      rewrite H. rewrite oro_None_l. reflexivity.
    + (* k routes to t1 (right); t2 gives None *)
      pose proof (WF_Bin_right_key_not_left p m t2 t1 k
        (IntMapProofs.All_IntMaps_WF _ (Bin p m t2 t1)) Hzk) as H.
      rewrite <- (lookup_Sem2 t2 k (IntMapProofs.All_IntMaps_WF _ t2)) in H.
      rewrite H. rewrite oro_None_r. reflexivity.
Qed.

(* ============================================================ *)
(* Delete-derived public lemmas                                  *)
(* ============================================================ *)

(* Helper: isSome of oro *)
Local Lemma isSome_oro : forall {a} (x y : option a),
  ssrbool.isSome (oro x y) = ssrbool.isSome x || ssrbool.isSome y.
Proof. intros. destruct x; reflexivity. Qed.

Lemma delete_eq : forall key b (i : IntMap.IntMap b),
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.delete key i) = None.
Proof.
  intros key b i.
  rewrite (lookup_Sem2 _ key (IntMapProofs.All_IntMaps_WF _ _)).
  rewrite (Sem2_delete key i key (IntMapProofs.All_IntMaps_WF _ i)).
  rewrite N.eqb_refl. reflexivity.
Qed.

Lemma delete_neq : forall key1 key2 b (i : IntMap.IntMap b),
    key1 <> key2 ->
    Data.IntMap.Internal.lookup key1 (Data.IntMap.Internal.delete key2 i) =
    Data.IntMap.Internal.lookup key1 i.
Proof.
  intros key1 key2 b i Hne.
  rewrite (lookup_Sem2 _ key1 (IntMapProofs.All_IntMaps_WF _ _)).
  rewrite (Sem2_delete key2 i key1 (IntMapProofs.All_IntMaps_WF _ i)).
  destruct (N.eqb_spec key1 key2) as [Heq | Hne'].
  - congruence.
  - rewrite <- (lookup_Sem2 i key1 (IntMapProofs.All_IntMaps_WF _ i)). reflexivity.
Qed.

Lemma member_delete_neq : forall k1 k2 b (i: IntMap.IntMap b), k1 <> k2 ->
  Data.IntMap.Internal.member k2 (Data.IntMap.Internal.delete k1 i) =
  Data.IntMap.Internal.member k2 i.
Proof.
  intros k1 k2 b i Hne.
  destruct (IntMapProofs.All_IntMaps_WF _ i) as [f Hf].
  destruct (IntMapProofs.All_IntMaps_WF _ (delete k1 i)) as [fd Hfd].
  rewrite (IntMapProofs.member_Sem Hfd).
  rewrite (IntMapProofs.member_Sem Hf).
  assert (Heq : fd k2 = f k2).
  { rewrite <- (IntMapProofs.lookup_Sem Hfd). rewrite <- (IntMapProofs.lookup_Sem Hf).
    exact (delete_neq k2 k1 b i (fun H => Hne (eq_sym H))). }
  rewrite Heq. reflexivity.
Qed.

Lemma member_delete : forall A k k' (m : IntMap.IntMap A),
    Data.IntMap.Internal.member k (Data.IntMap.Internal.delete k' m) =
    negb (k == k') && Data.IntMap.Internal.member k m.
Proof.
  intros A k k' m.
  destruct (IntMapProofs.All_IntMaps_WF _ m) as [f Hf].
  destruct (IntMapProofs.All_IntMaps_WF _ (delete k' m)) as [fd Hfd].
  rewrite (IntMapProofs.member_Sem Hfd) (IntMapProofs.member_Sem Hf).
  (* goal: isSome (fd k) = negb (k == k') && isSome (f k) *)
  (* Use Sem2_delete to characterize fd k *)
  assert (Hfd_k : fd k = IntMapProofs.Sem2 (delete k' m) k).
  { rewrite <- (IntMapProofs.lookup_Sem Hfd).
    exact (lookup_Sem2 (delete k' m) k (ex_intro _ fd Hfd)). }
  assert (Hf_k : f k = IntMapProofs.Sem2 m k).
  { rewrite <- (IntMapProofs.lookup_Sem Hf).
    exact (lookup_Sem2 m k (ex_intro _ f Hf)). }
  rewrite Hfd_k.
  rewrite (Sem2_delete k' m k (ex_intro _ f Hf)).
  rewrite Hf_k.
  (* Goal: isSome (if (k=?k')%N then None else Sem2 m k) = negb (k == k') && isSome (Sem2 m k) *)
  (* k == k' = (k =? k')%N via Eq_N *)
  assert (Hkk_eq : (k == k') = (k =? k')%N) by reflexivity.
  rewrite Hkk_eq.
  destruct ((k =? k')%N) eqn:Hkk.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* ============================================================ *)
(* Filter-related lemmas                                         *)
(* ============================================================ *)

(* Looking up in a filtered map implies the predicate holds *)
Lemma lookup_filter_Some : forall A (p : A -> bool) key val (m : IntMap.IntMap A),
  Data.IntMap.Internal.lookup key (Data.IntMap.Internal.filter p m) = Some val ->
  p val = true /\ Data.IntMap.Internal.lookup key m = Some val.
Proof.
  intros A p key val m Hlook.
  destruct (IntMapProofs.All_IntMaps_WF _ m) as [f Hf].
  set (f' := fun i => match f i with
                       | None => None
                       | Some v => if p v then Some v else None
                       end).
  assert (Hfilt : IntMapProofs.Sem (Data.IntMap.Internal.filter p m) f').
  { exact (IntMapProofs.filter_Sem p m f f' Hf (fun i => Logic.eq_refl)). }
  rewrite (IntMapProofs.lookup_Sem Hfilt) in Hlook.
  rewrite (IntMapProofs.lookup_Sem Hf).
  unfold f' in Hlook. destruct (f key) as [v|] eqn:Hfk.
  - destruct (p v) eqn:Hpv.
    + inversion Hlook; subst. auto.
    + discriminate.
  - discriminate.
Qed.

(* If lookup finds val in m and p val = true, then member in filter *)
Lemma member_filter : forall A (p : A -> bool) key val (m : IntMap.IntMap A),
  Data.IntMap.Internal.lookup key m = Some val ->
  p val = true ->
  Data.IntMap.Internal.member key (Data.IntMap.Internal.filter p m) = true.
Proof.
  intros A p key val m Hlook Hpval.
  destruct (IntMapProofs.All_IntMaps_WF _ m) as [f Hf].
  set (f' := fun i => match f i with
                       | None => None
                       | Some v => if p v then Some v else None
                       end).
  assert (Hfilt : IntMapProofs.Sem (Data.IntMap.Internal.filter p m) f').
  { exact (IntMapProofs.filter_Sem p m f f' Hf (fun i => Logic.eq_refl)). }
  rewrite (IntMapProofs.member_Sem Hfilt).
  rewrite (IntMapProofs.lookup_Sem Hf) in Hlook.
  unfold f'. rewrite Hlook Hpval. reflexivity.
Qed.

(* filterWithKey: looking up in filtered map gives a value from the original map *)
Lemma lookup_filterWithKey :
  forall b key (val:b) m f,
  Data.IntMap.Internal.lookup key (Data.IntMap.Internal.filterWithKey f m) = Some val ->
  Data.IntMap.Internal.lookup key m = Some val.
Proof.
  intros b key val m.
  revert val.
  induction m as [p mask l IHl r IHr | k v | ]; intros val f.
  - (* Bin: filterWithKey f (Bin p mask l r) = bin p mask (filterWithKey f l) (filterWithKey f r) *)
    intro H.
    change (Data.IntMap.Internal.filterWithKey f (Bin p mask l r))
      with (bin p mask (Data.IntMap.Internal.filterWithKey f l)
                       (Data.IntMap.Internal.filterWithKey f r)) in H.
    rewrite lookup_bin_oro in H.
    apply oro_Some in H.
    rewrite (lookup_Bin_oro p mask l r key (IntMapProofs.All_IntMaps_WF _ _)).
    (* Route by zero key mask to determine which subtree is relevant *)
    destruct (Data.IntSet.Internal.zero key mask) eqn:Hzk.
    + (* key routes left: r gives None *)
      pose proof (WF_Bin_left_key_not_right p mask l r key (IntMapProofs.All_IntMaps_WF _ _) Hzk) as Hr_none.
      rewrite <- (lookup_Sem2 r key (IntMapProofs.All_IntMaps_WF _ r)) in Hr_none.
      destruct H as [Hl1 | Hr1].
      * rewrite (IHl _ f Hl1) Hr_none. reflexivity.
      * (* fwk r gave Some val, but by IHr lookup key r = Some val, contradicts Hr_none *)
        apply (IHr _ f) in Hr1. congruence.
    + (* key routes right: l gives None *)
      pose proof (WF_Bin_right_key_not_left p mask l r key (IntMapProofs.All_IntMaps_WF _ _) Hzk) as Hl_none.
      rewrite <- (lookup_Sem2 l key (IntMapProofs.All_IntMaps_WF _ l)) in Hl_none.
      destruct H as [Hl1 | Hr1].
      * (* fwk l gave Some val, but by IHl lookup key l = Some val, contradicts Hl_none *)
        apply (IHl _ f) in Hl1. congruence.
      * rewrite Hl_none (IHr _ f Hr1). rewrite oro_None_l. reflexivity.
  - (* Tip: filterWithKey f (Tip k v) = if f k v then Tip k v else Nil *)
    simpl. destruct (f k v) eqn:Hfv.
    + exact id.
    + intro H. discriminate.
  - (* Nil *)
    simpl. intro H. discriminate.
Qed.

(* fst (partition P m) = filter P m *)
Local Lemma partition_fst_eq_filter : forall {A} (P : A -> bool) (m : IntMap.IntMap A),
  fst (Data.IntMap.Internal.partition P m) =
  Data.IntMap.Internal.filter P m.
Proof.
  intros A P m.
  induction m as [p mask l IHl r IHr | k v | ]; simpl.
  - unfold Data.IntMap.Internal.partition, Data.IntMap.Internal.partitionWithKey.
    simpl.
    unfold Data.IntMap.Internal.filter, Data.IntMap.Internal.filterWithKey. simpl.
    destruct (let fix go p0 t := match t with
      | Bin pp m0 ll rr => let 'pair r1 r2 := go p0 rr in
                           let 'pair l1 l2 := go p0 ll in pair (bin pp m0 l1 r1) (bin pp m0 l2 r2)
      | Tip k x => if p0 k x then pair t Nil else pair Nil t
      | Nil => pair Nil Nil end in go (fun _ x => P x) r) as [rl rr] eqn:Hr.
    destruct (let fix go p0 t := match t with
      | Bin pp m0 ll rr => let 'pair r1 r2 := go p0 rr in
                           let 'pair l1 l2 := go p0 ll in pair (bin pp m0 l1 r1) (bin pp m0 l2 r2)
      | Tip k x => if p0 k x then pair t Nil else pair Nil t
      | Nil => pair Nil Nil end in go (fun _ x => P x) l) as [ll lr] eqn:Hl.
    simpl fst.
    (* After simpl, IHl has (partition P l).1 = filter P l with SSReflect .1 notation.
       The assert goal after rewrite<-IHl; unfold; simpl has ((fix go...) pred l).1 in it.
       But Hl has (let fix go... in go pred l) form.
       Convert Hl to the fix-applied form by definitional equality, then rewrite. *)
    assert (Hll : ll = Data.IntMap.Internal.filter P l).
    { rewrite <- IHl.
      unfold Data.IntMap.Internal.partition, Data.IntMap.Internal.partitionWithKey.
      simpl.
      (* Goal: ll = ((fix go...) pred l).1 *)
      (* Hl : (let fix go... in go pred l) = (ll, lr) *)
      (* These are definitionally equal, so we can cast Hl *)
      have Hl' : ((fix go (p0 : Data.IntSet.Internal.Key -> A -> bool)
                      (t : IntMap.IntMap A) {struct t} :
                      IntMap.IntMap A * IntMap.IntMap A :=
                    match t with
                    | Bin pp m0 ll rr =>
                        let '(r1, r2) := go p0 rr in
                        let '(l1, l2) := go p0 ll in
                        (bin pp m0 l1 r1, bin pp m0 l2 r2)
                    | Tip k x => if p0 k x then (t, Nil) else (Nil, t)
                    | Nil => (Nil, Nil)
                    end) (fun=> [eta P]) l) = (ll, lr) := Hl.
      rewrite Hl'. reflexivity. }
    assert (Hrl : rl = Data.IntMap.Internal.filter P r).
    { rewrite <- IHr.
      unfold Data.IntMap.Internal.partition, Data.IntMap.Internal.partitionWithKey.
      simpl.
      have Hr' : ((fix go (p0 : Data.IntSet.Internal.Key -> A -> bool)
                      (t : IntMap.IntMap A) {struct t} :
                      IntMap.IntMap A * IntMap.IntMap A :=
                    match t with
                    | Bin pp m0 ll rr =>
                        let '(r1, r2) := go p0 rr in
                        let '(l1, l2) := go p0 ll in
                        (bin pp m0 l1 r1, bin pp m0 l2 r2)
                    | Tip k x => if p0 k x then (t, Nil) else (Nil, t)
                    | Nil => (Nil, Nil)
                    end) (fun=> [eta P]) r) = (rl, rr) := Hr.
      rewrite Hr'. reflexivity. }
    rewrite Hll Hrl. reflexivity.
  - (* Tip case *)
    unfold Data.IntMap.Internal.partition, Data.IntMap.Internal.partitionWithKey.
    unfold Data.IntMap.Internal.filter, Data.IntMap.Internal.filterWithKey. simpl.
    destruct (P v) eqn:HP; simpl; reflexivity.
  - (* Nil case *)
    reflexivity.
Qed.

(* Helper: lookup in fst or snd of partition gives lookup in original *)
Local Lemma lookup_partition_fst : forall {A} key val (m : IntMap.IntMap A) P,
  Data.IntMap.Internal.lookup key (fst (Data.IntMap.Internal.partition P m)) = Some val ->
  Data.IntMap.Internal.lookup key m = Some val.
Proof.
  intros A key val m P H.
  rewrite partition_fst_eq_filter in H.
  exact (proj2 (lookup_filter_Some A P key val m H)).
Qed.

(* snd (partition P m) = filter (negb . P) m *)
Local Lemma partition_snd_eq_filter : forall {A} (P : A -> bool) (m : IntMap.IntMap A),
  snd (Data.IntMap.Internal.partition P m) =
  Data.IntMap.Internal.filter (fun v => negb (P v)) m.
Proof.
  intros A P m.
  induction m as [p mask l IHl r IHr | k v | ]; simpl.
  - unfold Data.IntMap.Internal.partition, Data.IntMap.Internal.partitionWithKey.
    simpl.
    unfold Data.IntMap.Internal.filter, Data.IntMap.Internal.filterWithKey. simpl.
    destruct (let fix go p0 t := match t with
      | Bin pp m0 ll rr => let 'pair r1 r2 := go p0 rr in
                           let 'pair l1 l2 := go p0 ll in pair (bin pp m0 l1 r1) (bin pp m0 l2 r2)
      | Tip k x => if p0 k x then pair t Nil else pair Nil t
      | Nil => pair Nil Nil end in go (fun _ x => P x) r) as [rl rr] eqn:Hr.
    destruct (let fix go p0 t := match t with
      | Bin pp m0 ll rr => let 'pair r1 r2 := go p0 rr in
                           let 'pair l1 l2 := go p0 ll in pair (bin pp m0 l1 r1) (bin pp m0 l2 r2)
      | Tip k x => if p0 k x then pair t Nil else pair Nil t
      | Nil => pair Nil Nil end in go (fun _ x => P x) l) as [ll lr] eqn:Hl.
    simpl snd.
    assert (Hlr : lr = Data.IntMap.Internal.filter (fun v => negb (P v)) l).
    { rewrite <- IHl.
      unfold Data.IntMap.Internal.partition, Data.IntMap.Internal.partitionWithKey.
      simpl.
      have Hl' : ((fix go (p0 : Data.IntSet.Internal.Key -> A -> bool)
                      (t : IntMap.IntMap A) {struct t} :
                      IntMap.IntMap A * IntMap.IntMap A :=
                    match t with
                    | Bin pp m0 ll rr =>
                        let '(r1, r2) := go p0 rr in
                        let '(l1, l2) := go p0 ll in
                        (bin pp m0 l1 r1, bin pp m0 l2 r2)
                    | Tip k x => if p0 k x then (t, Nil) else (Nil, t)
                    | Nil => (Nil, Nil)
                    end) (fun=> [eta P]) l) = (ll, lr) := Hl.
      rewrite Hl'. reflexivity. }
    assert (Hrr : rr = Data.IntMap.Internal.filter (fun v => negb (P v)) r).
    { rewrite <- IHr.
      unfold Data.IntMap.Internal.partition, Data.IntMap.Internal.partitionWithKey.
      simpl.
      have Hr' : ((fix go (p0 : Data.IntSet.Internal.Key -> A -> bool)
                      (t : IntMap.IntMap A) {struct t} :
                      IntMap.IntMap A * IntMap.IntMap A :=
                    match t with
                    | Bin pp m0 ll rr =>
                        let '(r1, r2) := go p0 rr in
                        let '(l1, l2) := go p0 ll in
                        (bin pp m0 l1 r1, bin pp m0 l2 r2)
                    | Tip k x => if p0 k x then (t, Nil) else (Nil, t)
                    | Nil => (Nil, Nil)
                    end) (fun=> [eta P]) r) = (rl, rr) := Hr.
      rewrite Hr'. reflexivity. }
    rewrite Hlr Hrr. reflexivity.
  - (* Tip case *)
    unfold Data.IntMap.Internal.partition, Data.IntMap.Internal.partitionWithKey.
    unfold Data.IntMap.Internal.filter, Data.IntMap.Internal.filterWithKey. simpl.
    destruct (P v) eqn:HP; simpl; reflexivity.
  - (* Nil case *)
    reflexivity.
Qed.

Local Lemma lookup_partition_snd : forall {A} key val (m : IntMap.IntMap A) P,
  Data.IntMap.Internal.lookup key (snd (Data.IntMap.Internal.partition P m)) = Some val ->
  Data.IntMap.Internal.lookup key m = Some val.
Proof.
  intros A key val m P H.
  rewrite partition_snd_eq_filter in H.
  exact (proj2 (lookup_filter_Some A (fun v => negb (P v)) key val m H)).
Qed.

(* partition: lookup in either partition yields lookup in the original map *)
Lemma lookup_partition :
  forall (A:Type) key (val:A) (m m': IntMap.IntMap A) (P: A -> bool),
    ((m' = fst (Data.IntMap.Internal.partition P m) \/
      m' = snd (Data.IntMap.Internal.partition P m)) /\
     Data.IntMap.Internal.lookup key m' = Some val) ->
    Data.IntMap.Internal.lookup key m  = Some val.
Proof.
  intros A key val m m' P [[Hm'l | Hm'r] Hlook]; subst m'.
  - exact (lookup_partition_fst key val m P Hlook).
  - exact (lookup_partition_snd key val m P Hlook).
Qed.

(* ============================================================ *)
(* Phase 1: Infrastructure helpers                               *)
(* ============================================================ *)

(* member = isSome . lookup *)
Local Lemma member_isSome : forall A k (m : IntMap.IntMap A),
  Data.IntMap.Internal.member k m = ssrbool.isSome (Data.IntMap.Internal.lookup k m).
Proof.
  intros A k m.
  destruct (IntMapProofs.All_IntMaps_WF _ m) as [f Hf].
  rewrite (IntMapProofs.member_Sem Hf) (IntMapProofs.lookup_Sem Hf).
  reflexivity.
Qed.

(* oro reordering when at most one of y,z is Some *)
Local Lemma oro_swap_if_None : forall {a} (x y z : option a),
  y = None \/ z = None ->
  oro (oro x y) z = oro (oro x z) y.
Proof.
  intros a x y z [Hy | Hz]; subst.
  - rewrite oro_None_r. destruct x, z; reflexivity.
  - rewrite oro_None_r. destruct x, y; reflexivity.
Qed.

(* WF Bins have disjoint subtrees wrt lookup *)
Local Lemma WF_Bin_lookup_disjoint : forall {a} p msk (l r : IntMap.IntMap a) k,
  IntMapProofs.WF (Bin p msk l r) ->
  Data.IntMap.Internal.lookup k l = None \/ Data.IntMap.Internal.lookup k r = None.
Proof.
  intros a p msk l r k HWF.
  destruct (Data.IntSet.Internal.zero k msk) eqn:Hz.
  - right.
    rewrite (lookup_Sem2 r k (IntMapProofs.All_IntMaps_WF _ r)).
    exact (WF_Bin_left_key_not_right p msk l r k HWF Hz).
  - left.
    rewrite (lookup_Sem2 l k (IntMapProofs.All_IntMaps_WF _ l)).
    exact (WF_Bin_right_key_not_left p msk l r k HWF Hz).
Qed.

(* Word Eq_refl via change *)
Local Lemma Eq_refl_Word : forall (x : GHC.Num.Word), (x == x) = true.
Proof.
  intro x. change ((x == x) = true) with ((x =? x)%N = true).
  apply N.eqb_refl.
Qed.

(* IntMap Eq_refl: m == m = true when elements have EqLaws *)
Local Lemma IntMap_Eq_refl : forall A `{EqLaws A} (m : IntMap.IntMap A),
  (m == m) = true.
Proof.
  intros A HeqA HlawsA m. induction m as [p mask l IHl r IHr | k v | ].
  - (* Bin: (Bin p mask l r) == (Bin p mask l r) unfolds through CPS/equal to the conjunction *)
    change ((Bin p mask l r == Bin p mask l r) = true)
      with ((mask == mask) && ((p == p) && ((l == l) && (r == r))) = true).
    rewrite !Eq_refl_Word IHl IHr. reflexivity.
  - change ((Tip k v == Tip k v) = true)
      with ((k == k) && (v == v) = true).
    rewrite Eq_refl_Word Eq_refl. reflexivity.
  - reflexivity.
Qed.

(* ============================================================ *)
(* Phase 2: EqLaws-based lemmas (no core characterizations)      *)
(* ============================================================ *)

(* Helper: two maps with same lookup are Leibniz equal *)
Local Lemma maps_eq_of_lookup_eq : forall A (m1 m2 : IntMap.IntMap A),
  (forall k, Data.IntMap.Internal.lookup k m1 = Data.IntMap.Internal.lookup k m2) ->
  m1 = m2.
Proof.
  intros A m1 m2 Hlookup.
  destruct (IntMapProofs.All_IntMaps_WF _ m1) as [f1 Hf1].
  destruct (IntMapProofs.All_IntMaps_WF _ m2) as [f2 Hf2].
  apply (IntMapProofs.Sem_unique _ _ f1 _ f2 Hf1 Hf2).
  intro k.
  rewrite -(IntMapProofs.lookup_Sem Hf1) -(IntMapProofs.lookup_Sem Hf2).
  exact (Hlookup k).
Qed.

(* delete_commute: uses delete_eq/delete_neq + maps_eq_of_lookup_eq *)
Lemma delete_commute :
  forall (A : Type) `{EqLaws A}
    (kx ky : Internal.Key)
    (i : IntMap.IntMap A),
  Data.IntMap.Internal.delete ky (Data.IntMap.Internal.delete kx i) ==
  Data.IntMap.Internal.delete kx (Data.IntMap.Internal.delete ky i).
Proof.
  intros A HeqA HlawsA kx ky i.
  assert (H : Data.IntMap.Internal.delete ky (Data.IntMap.Internal.delete kx i) =
              Data.IntMap.Internal.delete kx (Data.IntMap.Internal.delete ky i)).
  { apply maps_eq_of_lookup_eq. intro k.
    destruct (N.eq_dec k kx) as [-> | Hnkx].
    - destruct (N.eq_dec kx ky) as [-> | Hnky].
      + rewrite !delete_eq. reflexivity.
      + rewrite (delete_neq _ _ _ _ Hnky) !delete_eq. reflexivity.
    - destruct (N.eq_dec k ky) as [-> | Hnky].
      + rewrite delete_eq (delete_neq _ _ _ _ Hnkx) delete_eq. reflexivity.
      + rewrite (delete_neq _ _ _ _ Hnky) !(delete_neq _ _ _ _ Hnkx)
                (delete_neq _ _ _ _ Hnky). reflexivity. }
  rewrite H. exact (@IntMap_Eq_refl A HeqA HlawsA _).
Qed.

(* filter_comp: filter f (filter f' m) == filter (fun v => f v && f' v) m *)
Lemma filter_comp : forall A `{EqLaws A} f f' (i : IntMap.IntMap A),
    Data.IntMap.Internal.filter f (Data.IntMap.Internal.filter f' i) ==
    Data.IntMap.Internal.filter (fun v => f v && f' v) i.
Proof.
  intros A HeqA HlawsA f f' i.
  assert (Heq : Data.IntMap.Internal.filter f (Data.IntMap.Internal.filter f' i) =
                Data.IntMap.Internal.filter (fun v => f v && f' v) i).
  { destruct (IntMapProofs.All_IntMaps_WF _ i) as [fi Hfi].
    set (fi' := fun k => match fi k with None => None | Some v => if f' v then Some v else None end).
    assert (Hfilt' : IntMapProofs.Sem (Data.IntMap.Internal.filter f' i) fi').
    { exact (IntMapProofs.filter_Sem f' i fi fi' Hfi (fun k => Logic.eq_refl)). }
    set (fcomp := fun k => match fi' k with None => None | Some v => if f v then Some v else None end).
    assert (Hfcomp : IntMapProofs.Sem (Data.IntMap.Internal.filter f (Data.IntMap.Internal.filter f' i)) fcomp).
    { exact (IntMapProofs.filter_Sem f _ fi' fcomp Hfilt' (fun k => Logic.eq_refl)). }
    set (fand := fun k => match fi k with None => None | Some v => if f v && f' v then Some v else None end).
    assert (Hfand : IntMapProofs.Sem (Data.IntMap.Internal.filter (fun v => f v && f' v) i) fand).
    { exact (IntMapProofs.filter_Sem (fun v => f v && f' v) i fi fand Hfi (fun k => Logic.eq_refl)). }
    apply (IntMapProofs.Sem_unique _ _ fcomp _ fand Hfcomp Hfand).
    intro k. unfold fcomp, fi', fand.
    destruct (fi k) as [v|]; [| reflexivity].
    destruct (f' v), (f v); reflexivity. }
  rewrite Heq. exact (@IntMap_Eq_refl A HeqA HlawsA _).
Qed.

(* filter_true: filter (const true) m == m *)
Lemma filter_true : forall (A:Type) `{EqLaws A} (m:IntMap.IntMap A),
    Data.IntMap.Internal.filter (const true) m == m.
Proof.
  intros A HeqA HlawsA m.
  assert (Heq : Data.IntMap.Internal.filter (const true) m = m).
  { destruct (IntMapProofs.All_IntMaps_WF _ m) as [fm Hfm].
    set (ff := fun k => match fm k with None => None | Some v => if (const true) v then Some v else None end).
    assert (Hff : IntMapProofs.Sem (Data.IntMap.Internal.filter (const true) m) ff).
    { exact (IntMapProofs.filter_Sem (const true) m fm ff Hfm (fun k => Logic.eq_refl)). }
    apply (IntMapProofs.Sem_unique _ _ ff _ fm Hff Hfm).
    intro k. unfold ff, const. destruct (fm k); reflexivity. }
  rewrite Heq. exact (@IntMap_Eq_refl A HeqA HlawsA _).
Qed.

(* ============================================================ *)
(* Core lookup characterizations (proved Lemmas)                 *)
(* These characterize lookup through union/difference/intersection *)
(* in terms of lookups on the component maps.                    *)
(* ============================================================ *)

(* Helper: one-step unfolding of union for the Bin/Bin case *)
Local Lemma union_unfold_BinBin : forall A p1 msk1 (l1 r1 : IntMap.IntMap A) p2 msk2 l2 r2,
  Data.IntMap.Internal.union (Bin p1 msk1 l1 r1) (Bin p2 msk2 l2 r2) =
  (let t1 := Bin p1 msk1 l1 r1 in
   let t2 := Bin p2 msk2 l2 r2 in
   if shorter msk1 msk2 then
    if nomatch p2 p1 msk1 then link p1 t1 p2 t2
    else if Data.IntSet.Internal.zero p2 msk1 then Bin p1 msk1 (Data.IntMap.Internal.union l1 t2) r1
    else Bin p1 msk1 l1 (Data.IntMap.Internal.union r1 t2)
  else if shorter msk2 msk1 then
    if nomatch p1 p2 msk2 then link p1 t1 p2 t2
    else if Data.IntSet.Internal.zero p1 msk2 then Bin p2 msk2 (Data.IntMap.Internal.union t1 l2) r2
    else Bin p2 msk2 l2 (Data.IntMap.Internal.union t1 r2)
  else if p1 == p2 then Bin p1 msk1 (Data.IntMap.Internal.union l1 l2) (Data.IntMap.Internal.union r1 r2)
  else link p1 t1 p2 t2).
Proof.
  intros. unfold Data.IntMap.Internal.union, Data.IntMap.Internal.mergeWithKey'.
  rewrite {1}IntMapProofs.deferredFix2_eq. reflexivity.
Qed.

(* Helper tactic: rewrite lookup on a Bin using WF *)
Local Ltac rw_lookup_Bin :=
  erewrite lookup_Bin_oro; [| exact (IntMapProofs.All_IntMaps_WF _ _)].

(* Helper tactic: derive disjointness for oro_swap_if_None from WF + IH (for merge0 proofs) *)
Local Ltac derive_disj_merge IH lchild rchild p m k :=
  destruct (@WF_Bin_lookup_disjoint _ p m lchild rchild k (IntMapProofs.All_IntMaps_WF _ _)) as [?Hu | ?Hr];
  [ left; rewrite IH in Hu; exact (proj2 (oro_None_inv _ _ Hu))
  | right; exact Hr ].

Local Lemma lookup_union_eq : forall A (m1 m2 : IntMap.IntMap A) k,
  Data.IntMap.Internal.lookup k (Data.IntMap.Internal.union m1 m2) =
  oro (Data.IntMap.Internal.lookup k m1) (Data.IntMap.Internal.lookup k m2).
Proof.
  intros A.
  enough (Hstrong : forall n (m1 m2 : IntMap.IntMap A) k,
    (size_nat m1 + size_nat m2 <= n)%nat ->
    Data.IntMap.Internal.lookup k (Data.IntMap.Internal.union m1 m2) =
    oro (Data.IntMap.Internal.lookup k m1) (Data.IntMap.Internal.lookup k m2)).
  { intros m1 m2 k. exact (Hstrong _ m1 m2 k (Nat.le_refl _)). }
  intro n. induction n as [n IHn] using lt_wf_ind.
  intros m1 m2 k Hle.
  destruct m1 as [p1 msk1 l1 r1 | k1 v1 | ];
  destruct m2 as [p2 msk2 l2 r2 | k2 v2 | ].
  - (* Bin/Bin *)
    rewrite union_unfold_BinBin. cbv beta zeta.
    destruct (shorter msk1 msk2) eqn:Hsh1.
    + (* merge1: shorter msk1 msk2 *)
      destruct (nomatch p2 p1 msk1) eqn:Hnm.
      * apply lookup_link_oro.
      * destruct (Data.IntSet.Internal.zero p2 msk1) eqn:Hz.
        -- (* merge1/zero: Bin p1 msk1 (union l1 t2) r1 *)
           rewrite (lookup_Bin_oro p1 msk1 _ r1 k (IntMapProofs.All_IntMaps_WF _ _)).
           rewrite (IHn (size_nat l1 + size_nat (Bin p2 msk2 l2 r2))%nat
             ltac:(simpl size_nat in Hle |- *; lia) l1 (Bin p2 msk2 l2 r2) k ltac:(lia)).
           rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
           apply oro_swap_if_None.
           destruct (WF_Bin_lookup_disjoint p1 msk1
             (Data.IntMap.Internal.union l1 (Bin p2 msk2 l2 r2)) r1 k (IntMapProofs.All_IntMaps_WF _ _)) as [Hu | Hr].
           ++ left.
              rewrite (IHn (size_nat l1 + size_nat (Bin p2 msk2 l2 r2))%nat
                ltac:(simpl size_nat in Hle |- *; lia) l1 (Bin p2 msk2 l2 r2) k ltac:(lia)) in Hu.
              exact (proj2 (oro_None_inv _ _ Hu)).
           ++ right. exact Hr.
        -- (* merge1/not-zero: Bin p1 msk1 l1 (union r1 t2) *)
           rewrite (lookup_Bin_oro p1 msk1 l1 _ k (IntMapProofs.All_IntMaps_WF _ _)).
           rewrite (IHn (size_nat r1 + size_nat (Bin p2 msk2 l2 r2))%nat
             ltac:(simpl size_nat in Hle |- *; lia) r1 (Bin p2 msk2 l2 r2) k ltac:(lia)).
           rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
           rewrite oro_assoc. reflexivity.
    + destruct (shorter msk2 msk1) eqn:Hsh2.
      * (* merge2: shorter msk2 msk1 *)
        destruct (nomatch p1 p2 msk2) eqn:Hnm.
        -- apply lookup_link_oro.
        -- destruct (Data.IntSet.Internal.zero p1 msk2) eqn:Hz.
           ++ (* merge2/zero: Bin p2 msk2 (union t1 l2) r2 *)
              rewrite (lookup_Bin_oro p2 msk2 _ r2 k (IntMapProofs.All_IntMaps_WF _ _)).
              rewrite (IHn (size_nat (Bin p1 msk1 l1 r1) + size_nat l2)%nat
                ltac:(simpl size_nat in Hle |- *; lia) (Bin p1 msk1 l1 r1) l2 k ltac:(lia)).
              rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
              rewrite oro_assoc. reflexivity.
           ++ (* merge2/not-zero: Bin p2 msk2 l2 (union t1 r2) *)
              rewrite (lookup_Bin_oro p2 msk2 l2 _ k (IntMapProofs.All_IntMaps_WF _ _)).
              rewrite (IHn (size_nat (Bin p1 msk1 l1 r1) + size_nat r2)%nat
                ltac:(simpl size_nat in Hle |- *; lia) (Bin p1 msk1 l1 r1) r2 k ltac:(lia)).
              rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
              (* goal: oro l2 (oro t1 r2) = oro t1 (oro l2 r2) *)
              rewrite <- !oro_assoc. f_equal.
              destruct (WF_Bin_lookup_disjoint p2 msk2 l2
                (Data.IntMap.Internal.union (Bin p1 msk1 l1 r1) r2) k (IntMapProofs.All_IntMaps_WF _ _)) as [Hl | Hu].
              ** apply oro_comm_left_None. exact Hl.
              ** apply oro_comm_right_None.
                 rewrite (IHn (size_nat (Bin p1 msk1 l1 r1) + size_nat r2)%nat
                   ltac:(simpl size_nat in Hle |- *; lia) (Bin p1 msk1 l1 r1) r2 k ltac:(lia)) in Hu.
                 exact (proj1 (oro_None_inv _ _ Hu)).
      * (* same length, different prefix or same prefix *)
        destruct (p1 == p2) eqn:Hpp.
        -- (* same prefix: Bin p1 msk1 (union l1 l2) (union r1 r2) *)
           rewrite (lookup_Bin_oro p1 msk1 _ _ k (IntMapProofs.All_IntMaps_WF _ _)).
           rewrite (IHn (size_nat l1 + size_nat l2)%nat
             ltac:(simpl size_nat in Hle |- *; lia) l1 l2 k ltac:(lia)).
           rewrite (IHn (size_nat r1 + size_nat r2)%nat
             ltac:(simpl size_nat in Hle |- *; lia) r1 r2 k ltac:(lia)).
           rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
           rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
           rewrite !oro_assoc. f_equal. rewrite <- !oro_assoc. f_equal.
           destruct (WF_Bin_lookup_disjoint p1 msk1
             (Data.IntMap.Internal.union l1 l2) (Data.IntMap.Internal.union r1 r2) k
             (IntMapProofs.All_IntMaps_WF _ _)) as [Hu1 | Hu2].
           ++ apply oro_comm_left_None.
              rewrite (IHn (size_nat l1 + size_nat l2)%nat
                ltac:(simpl size_nat in Hle |- *; lia) l1 l2 k ltac:(lia)) in Hu1.
              exact (proj2 (oro_None_inv _ _ Hu1)).
           ++ apply oro_comm_right_None.
              rewrite (IHn (size_nat r1 + size_nat r2)%nat
                ltac:(simpl size_nat in Hle |- *; lia) r1 r2 k ltac:(lia)) in Hu2.
              exact (proj1 (oro_None_inv _ _ Hu2)).
        -- (* different prefix *)
           apply lookup_link_oro.
  - (* Bin/Tip *)
    unfold Data.IntMap.Internal.union, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    match goal with
    | |- context [?f (Tip k2 v2) k2 l1] => set (merge0_fn := f)
    end.
    assert (Hmerge : forall t1 kk,
      Data.IntMap.Internal.lookup kk (merge0_fn (Tip k2 v2) k2 t1) =
      oro (Data.IntMap.Internal.lookup kk t1) (Data.IntMap.Internal.lookup kk (Tip k2 v2))).
    { intro t1. induction t1 as [p' m' l' IHl r' IHr | k' v' | ]; intro kk;
      unfold merge0_fn; cbv beta iota zeta; fold merge0_fn.
      - destruct (Data.IntMap.Internal.nomatch k2 p' m') eqn:Hnm'.
        + apply lookup_link_oro.
        + destruct (Data.IntSet.Internal.zero k2 m') eqn:Hz'.
          * rw_lookup_Bin. rewrite IHl. rw_lookup_Bin.
            apply oro_swap_if_None.
            derive_disj_merge IHl (merge0_fn (Tip k2 v2) k2 l') r' p' m' kk.
          * rw_lookup_Bin. rewrite IHr. rw_lookup_Bin.
            rewrite oro_assoc. reflexivity.
      - destruct (k' == k2) eqn:Hkk.
        + simpl Data.IntMap.Internal.lookup.
          move: Hkk => /Eq_eq_Word Hkk. subst k'.
          destruct (kk == k2); simpl; reflexivity.
        + apply lookup_link_oro.
      - simpl. reflexivity.
    }
    destruct (Data.IntMap.Internal.nomatch k2 p1 msk1) eqn:Hnm.
    + apply lookup_link_oro.
    + destruct (Data.IntSet.Internal.zero k2 msk1) eqn:Hz.
      * rw_lookup_Bin. rewrite Hmerge. rw_lookup_Bin.
        apply oro_swap_if_None.
        derive_disj_merge Hmerge (merge0_fn (Tip k2 v2) k2 l1) r1 p1 msk1 k.
      * rw_lookup_Bin. rewrite Hmerge. rw_lookup_Bin.
        rewrite oro_assoc. reflexivity.
  - (* Bin/Nil *)
    unfold Data.IntMap.Internal.union, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    rewrite oro_None_r. reflexivity.
  - (* Tip/Bin *)
    unfold Data.IntMap.Internal.union, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    match goal with
    | |- context [?f (Tip k1 v1) k1 l2] => set (merge0_fn := f)
    end.
    assert (Hmerge : forall t2 kk,
      Data.IntMap.Internal.lookup kk (merge0_fn (Tip k1 v1) k1 t2) =
      oro (Data.IntMap.Internal.lookup kk (Tip k1 v1)) (Data.IntMap.Internal.lookup kk t2)).
    { intro t2. induction t2 as [p' m' l' IHl r' IHr | k' v' | ]; intro kk;
      unfold merge0_fn; cbv beta iota zeta; fold merge0_fn.
      - destruct (Data.IntMap.Internal.nomatch k1 p' m') eqn:Hnm'.
        + apply lookup_link_oro.
        + destruct (Data.IntSet.Internal.zero k1 m') eqn:Hz'.
          * rw_lookup_Bin. rewrite IHl. rw_lookup_Bin.
            rewrite oro_assoc. reflexivity.
          * rw_lookup_Bin. rewrite IHr. rw_lookup_Bin.
            (* goal: oro l' (oro t1 r') = oro t1 (oro l' r') *)
            rewrite <- !oro_assoc. f_equal.
            destruct (@WF_Bin_lookup_disjoint _ p' m' l' (merge0_fn (Tip k1 v1) k1 r') kk
              (IntMapProofs.All_IntMaps_WF _ _)) as [Hl | Hu].
            ** apply oro_comm_left_None. exact Hl.
            ** apply oro_comm_right_None.
               rewrite IHr in Hu. exact (proj1 (oro_None_inv _ _ Hu)).
      - destruct (k1 == k') eqn:Hkk.
        + simpl Data.IntMap.Internal.lookup.
          move: Hkk => /Eq_eq_Word Hkk. subst k1.
          destruct (kk == k'); simpl; reflexivity.
        + apply lookup_link_oro.
      - simpl. rewrite oro_None_r. reflexivity.
    }
    destruct (Data.IntMap.Internal.nomatch k1 p2 msk2) eqn:Hnm.
    + apply lookup_link_oro.
    + destruct (Data.IntSet.Internal.zero k1 msk2) eqn:Hz.
      * rw_lookup_Bin. rewrite Hmerge. rw_lookup_Bin.
        rewrite oro_assoc. reflexivity.
      * rw_lookup_Bin. rewrite Hmerge. rw_lookup_Bin.
        (* goal: oro l2 (oro t1 r2) = oro t1 (oro l2 r2) *)
        rewrite <- !oro_assoc. f_equal.
        destruct (@WF_Bin_lookup_disjoint _ p2 msk2 l2 (merge0_fn (Tip k1 v1) k1 r2) k
          (IntMapProofs.All_IntMaps_WF _ _)) as [Hl | Hu].
        -- apply oro_comm_left_None. exact Hl.
        -- apply oro_comm_right_None.
           rewrite Hmerge in Hu. exact (proj1 (oro_None_inv _ _ Hu)).
  - (* Tip/Tip *)
    unfold Data.IntMap.Internal.union, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    destruct (k1 == k2) eqn:Hkk.
    + simpl Data.IntMap.Internal.lookup.
      move: Hkk => /Eq_eq_Word Hkk. subst k1.
      destruct (k == k2); simpl; reflexivity.
    + apply lookup_link_oro.
  - (* Tip/Nil *)
    unfold Data.IntMap.Internal.union, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    rewrite oro_None_r. reflexivity.
  - (* Nil/Bin *)
    unfold Data.IntMap.Internal.union, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    reflexivity.
  - (* Nil/Tip *)
    unfold Data.IntMap.Internal.union, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    reflexivity.
  - (* Nil/Nil *)
    unfold Data.IntMap.Internal.union, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    reflexivity.
Qed.

(* Helper: nomatch implies lookup on Bin returns None *)
Local Lemma lookup_nomatch_None : forall {a} p msk (l r : IntMap.IntMap a) key,
  Data.IntMap.Internal.nomatch key p msk = true ->
  Data.IntMap.Internal.lookup key (Bin p msk l r) = None.
Proof.
  intros a p msk l r key Hnm.
  rewrite (lookup_Sem2 _ key (IntMapProofs.All_IntMaps_WF _ _)).
  destruct (IntMapProofs.All_IntMaps_WF _ (Bin p msk l r)) as [f Hf].
  rewrite <- (Sem_Sem2 _ _ Hf key).
  assert (HDB : exists rr, IntMapProofs.Desc (Bin p msk l r) rr f).
  { inversion Hf.
    apply Eqdep.EqdepTheory.inj_pair2 in H1.
    apply Eqdep.EqdepTheory.inj_pair2 in H2.
    subst. eauto. }
  destruct HDB as [rr HDB].
  assert (Hrr_bits : (0 < rBits rr)%N).
  { inversion HDB.
    repeat match goal with
      | Heq : existT _ _ _ = existT _ _ _ |- _ =>
          apply Eqdep.EqdepTheory.inj_pair2 in Heq
    end.
    subst. assumption. }
  assert (Hnm_rr : nomatch key (rPrefix rr) (rMask rr) = true).
  { inversion HDB.
    repeat match goal with
      | Heq : existT _ _ _ = existT _ _ _ |- _ =>
          apply Eqdep.EqdepTheory.inj_pair2 in Heq
    end.
    subst. exact Hnm. }
  eapply IntMapProofs.Desc_outside. exact HDB.
  rewrite <- Bool.negb_true_iff.
  rewrite <- IntMapProofs.nomatch_spec; [exact Hnm_rr | exact Hrr_bits].
Qed.

(* Helper: lookup on a map is None when it's the left child and key routes right *)
(* The dummy argument allows cross-type calls (IntMap A / IntMap B) *)
Local Lemma lookup_left_None : forall {a b} (p msk : N) (l : IntMap.IntMap a) (dummy : IntMap.IntMap b) k,
  Data.IntSet.Internal.zero k msk = false ->
  Data.IntMap.Internal.lookup k l = None.
Proof.
  intros a b p msk l dummy k Hz.
  rewrite (lookup_Sem2 l k (IntMapProofs.All_IntMaps_WF _ l)).
  exact (WF_Bin_right_key_not_left p msk l Nil k (IntMapProofs.All_IntMaps_WF _ (Bin p msk l Nil)) Hz).
Qed.

(* Helper: lookup on a map is None when it's the right child and key routes left *)
(* The dummy argument allows cross-type calls (IntMap A / IntMap B) *)
Local Lemma lookup_right_None : forall {a b} (p msk : N) (dummy : IntMap.IntMap b) (r : IntMap.IntMap a) k,
  Data.IntSet.Internal.zero k msk = true ->
  Data.IntMap.Internal.lookup k r = None.
Proof.
  intros a b p msk dummy r k Hz.
  rewrite (lookup_Sem2 r k (IntMapProofs.All_IntMaps_WF _ r)).
  exact (WF_Bin_left_key_not_right p msk Nil r k (IntMapProofs.All_IntMaps_WF _ (Bin p msk Nil r)) Hz).
Qed.

(* Helper: for Desc inversion, extract range components *)
Local Ltac get_Desc_info t :=
  let f := fresh "f" in let Hf := fresh "Hf" in
  let rr := fresh "rr" in let HD := fresh "HD" in
  destruct (IntMapProofs.All_IntMaps_WF _ t) as [f Hf];
  assert (HD : exists rr, IntMapProofs.Desc t rr f) by
    (inversion Hf;
     repeat match goal with
       | Heq : existT _ _ _ = existT _ _ _ |- _ =>
           apply Eqdep.EqdepTheory.inj_pair2 in Heq
     end;
     subst; eauto);
  destruct HD as [rr HD].

(* Helper: Bins with disjoint ranges have disjoint lookups (nomatch cases) *)
Local Lemma nomatch_disjoint_lookup :
  forall {a b} (p1 msk1 : N) (l1 r1 : IntMap.IntMap a) (p2 msk2 : N) (l2 r2 : IntMap.IntMap b) k,
  shorter msk1 msk2 = true ->
  Data.IntMap.Internal.nomatch p2 p1 msk1 = true ->
  Data.IntMap.Internal.lookup k (Bin p1 msk1 l1 r1) = None \/
  Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2) = None.
Proof.
  intros a b p1 msk1 l1 r1 p2 msk2 l2 r2 k Hsh Hnm.
  get_Desc_info (Bin p1 msk1 l1 r1).
  get_Desc_info (Bin p2 msk2 l2 r2).
  assert (Hp1 : p1 = rPrefix rr) by
    (inversion HD; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; reflexivity).
  assert (Hmsk1 : msk1 = rMask rr) by
    (inversion HD; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; reflexivity).
  assert (Hbits1 : (0 < rBits rr)%N) by
    (inversion HD; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; assumption).
  assert (Hp2 : p2 = rPrefix rr0) by
    (inversion HD0; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; reflexivity).
  assert (Hmsk2 : msk2 = rMask rr0) by
    (inversion HD0; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; reflexivity).
  assert (Hbits2 : (0 < rBits rr0)%N) by
    (inversion HD0; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; assumption).
  subst p1 msk1 p2 msk2.
  (* nomatch → inRange (rPrefix rr0) rr = false *)
  pose proof (IntMapProofs.nomatch_spec (rPrefix rr0) rr Hbits1) as Hnm_spec.
  rewrite Hnm in Hnm_spec.
  assert (HnotInR : inRange (rPrefix rr0) rr = false).
  { destruct (inRange (rPrefix rr0) rr); [discriminate | reflexivity]. }
  (* shorter → rBits rr0 < rBits rr *)
  change Data.IntMap.Internal.shorter with Data.IntSet.Internal.shorter in Hsh.
  pose proof (IntSetProofs.shorter_spec rr rr0 Hbits1 Hbits2) as Hsh_spec.
  rewrite Hsh in Hsh_spec.
  assert (Hbits_lt : (rBits rr0 < rBits rr)%N).
  { apply N.ltb_lt. exact (eq_sym Hsh_spec). }
  (* Derive rangeDisjoint rr0 rr = true *)
  assert (Hdisj : rangeDisjoint rr0 rr = true).
  { unfold rangeDisjoint, isSubrange.
    rewrite HnotInR. simpl.
    assert (Hle : (rBits rr <=? rBits rr0)%N = false).
    { apply N.leb_gt. lia. }
    rewrite Hle. rewrite Bool.andb_false_r. reflexivity. }
  (* Case-split on inRange k rr0 *)
  destruct (inRange k rr0) eqn:HinR0.
  - (* k in rr0: k not in rr → lookup k t1 = None *)
    left.
    rewrite (lookup_Sem2 _ k (IntMapProofs.All_IntMaps_WF _ _)).
    rewrite <- (Sem_Sem2 _ _ Hf k).
    eapply IntMapProofs.Desc_outside. exact HD.
    exact (rangeDisjoint_inRange_false k rr0 rr Hdisj HinR0).
  - (* k not in rr0: lookup k t2 = None *)
    right.
    rewrite (lookup_Sem2 _ k (IntMapProofs.All_IntMaps_WF _ _)).
    rewrite <- (Sem_Sem2 _ _ Hf0 k).
    eapply IntMapProofs.Desc_outside. exact HD0.
    exact HinR0.
Qed.

(* Same-length different-prefix gives disjoint lookups *)
Local Lemma diff_prefix_disjoint_lookup :
  forall {a b} (p1 msk1 : N) (l1 r1 : IntMap.IntMap a) (p2 msk2 : N) (l2 r2 : IntMap.IntMap b) k,
  shorter msk1 msk2 = false ->
  shorter msk2 msk1 = false ->
  (p1 == p2) = false ->
  Data.IntMap.Internal.lookup k (Bin p1 msk1 l1 r1) = None \/
  Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2) = None.
Proof.
  intros a b p1 msk1 l1 r1 p2 msk2 l2 r2 k Hsh1 Hsh2 Hpp.
  get_Desc_info (Bin p1 msk1 l1 r1).
  get_Desc_info (Bin p2 msk2 l2 r2).
  assert (Hp1 : p1 = rPrefix rr) by
    (inversion HD; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; reflexivity).
  assert (Hmsk1 : msk1 = rMask rr) by
    (inversion HD; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; reflexivity).
  assert (Hbits1 : (0 < rBits rr)%N) by
    (inversion HD; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; assumption).
  assert (Hp2 : p2 = rPrefix rr0) by
    (inversion HD0; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; reflexivity).
  assert (Hmsk2 : msk2 = rMask rr0) by
    (inversion HD0; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; reflexivity).
  assert (Hbits2 : (0 < rBits rr0)%N) by
    (inversion HD0; repeat match goal with Heq : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in Heq end; subst; assumption).
  subst p1 msk1 p2 msk2.
  (* shorter both false → rBits rr = rBits rr0 *)
  change Data.IntMap.Internal.shorter with Data.IntSet.Internal.shorter in Hsh1, Hsh2.
  pose proof (IntSetProofs.shorter_spec rr rr0 Hbits1 Hbits2) as Hs1.
  pose proof (IntSetProofs.shorter_spec rr0 rr Hbits2 Hbits1) as Hs2.
  rewrite Hsh1 in Hs1. rewrite Hsh2 in Hs2.
  symmetry in Hs1, Hs2.
  assert (Hbits_eq : rBits rr = rBits rr0).
  { apply N.ltb_ge in Hs1. apply N.ltb_ge in Hs2. lia. }
  (* p1 ≠ p2 → rPrefix rr ≠ rPrefix rr0 *)
  assert (Hpne : rPrefix rr <> rPrefix rr0).
  { intro Heq.
    change ((rPrefix rr == rPrefix rr0) = false) in Hpp.
    change ((rPrefix rr == rPrefix rr0) = false) with ((rPrefix rr =? rPrefix rr0)%N = false) in Hpp.
    apply N.eqb_neq in Hpp. contradiction. }
  (* Different prefix, same bits → disjoint *)
  assert (Hdisj : rangeDisjoint rr rr0 = true).
  { exact (different_prefix_same_bits_disjoint rr rr0 Hpne Hbits_eq). }
  destruct (inRange k rr) eqn:HinR.
  - right.
    rewrite (lookup_Sem2 _ k (IntMapProofs.All_IntMaps_WF _ _)).
    rewrite <- (Sem_Sem2 _ _ Hf0 k).
    eapply IntMapProofs.Desc_outside. exact HD0.
    exact (rangeDisjoint_inRange_false k rr rr0 Hdisj HinR).
  - left.
    rewrite (lookup_Sem2 _ k (IntMapProofs.All_IntMaps_WF _ _)).
    rewrite <- (Sem_Sem2 _ _ Hf k).
    eapply IntMapProofs.Desc_outside. exact HD. exact HinR.
Qed.

(* Helper: one-step unfolding of difference for the Bin/Bin case *)
Local Lemma difference_unfold_BinBin : forall A B p1 msk1 (l1 r1 : IntMap.IntMap A) p2 msk2 (l2 r2 : IntMap.IntMap B),
  Data.IntMap.Internal.difference (Bin p1 msk1 l1 r1) (Bin p2 msk2 l2 r2) =
  (let t1 := Bin p1 msk1 l1 r1 in
   let t2 := Bin p2 msk2 l2 r2 in
   if shorter msk1 msk2 then
    if nomatch p2 p1 msk1 then t1
    else if Data.IntSet.Internal.zero p2 msk1 then bin p1 msk1 (Data.IntMap.Internal.difference l1 t2) r1
    else bin p1 msk1 l1 (Data.IntMap.Internal.difference r1 t2)
  else if shorter msk2 msk1 then
    if nomatch p1 p2 msk2 then t1
    else if Data.IntSet.Internal.zero p1 msk2 then bin p2 msk2 (Data.IntMap.Internal.difference t1 l2) Nil
    else bin p2 msk2 Nil (Data.IntMap.Internal.difference t1 r2)
  else if p1 == p2 then bin p1 msk1 (Data.IntMap.Internal.difference l1 l2) (Data.IntMap.Internal.difference r1 r2)
  else t1).
Proof.
  intros. unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.mergeWithKey, Data.IntMap.Internal.mergeWithKey'.
  rewrite {1}IntMapProofs.deferredFix2_eq. reflexivity.
Qed.

(* Helper tactic: derive routing-based None for diff proofs *)
Local Ltac diff_route_None :=
  match goal with
  | Hz : Data.IntSet.Internal.zero ?k ?msk = true |- Data.IntMap.Internal.lookup ?k ?r = None =>
    exact (lookup_right_None _ msk _ r k Hz)
  | Hz : Data.IntSet.Internal.zero ?k ?msk = false |- Data.IntMap.Internal.lookup ?k ?l = None =>
    exact (lookup_left_None _ msk l _ k Hz)
  end.

Local Lemma lookup_difference_eq : forall A B (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B) k,
  Data.IntMap.Internal.lookup k (Data.IntMap.Internal.difference m1 m2) =
  match Data.IntMap.Internal.lookup k m2 with Some _ => None | None => Data.IntMap.Internal.lookup k m1 end.
Proof.
  intros A B.
  enough (Hstrong : forall n (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B) k,
    (size_nat m1 + size_nat m2 <= n)%nat ->
    Data.IntMap.Internal.lookup k (Data.IntMap.Internal.difference m1 m2) =
    match Data.IntMap.Internal.lookup k m2 with Some _ => None | None => Data.IntMap.Internal.lookup k m1 end).
  { intros m1 m2 k. exact (Hstrong _ m1 m2 k (Nat.le_refl _)). }
  intro n. induction n as [n IHn] using lt_wf_ind.
  intros m1 m2 k Hle.
  destruct m1 as [p1 msk1 l1 r1 | k1 v1 | ];
  destruct m2 as [p2 msk2 l2 r2 | k2 v2 | ].
  - (* Bin/Bin *)
    rewrite difference_unfold_BinBin. cbv beta zeta.
    destruct (shorter msk1 msk2) eqn:Hsh1.
    + (* merge1: shorter msk1 msk2 *)
      destruct (nomatch p2 p1 msk1) eqn:Hnm.
      * (* nomatch: result = t1 *)
        destruct (Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2)) eqn:Ht2.
        -- (* lookup k t2 = Some: need lookup k t1 = None *)
           (* t1 and t2 are disjoint (use constructed Bin) *)
           destruct (nomatch_disjoint_lookup p1 msk1 l1 r1 p2 msk2 l2 r2 k Hsh1 Hnm) as [Ht1_none | Ht2_none].
           ++ exact Ht1_none.
           ++ rewrite Ht2_none in Ht2. discriminate.
        -- (* lookup k t2 = None *) reflexivity.
      * destruct (Data.IntSet.Internal.zero p2 msk1) eqn:Hz.
        -- (* merge1/zero: bin p1 msk1 (diff l1 t2) r1 *)
           rewrite lookup_bin_oro.
           rewrite (IHn (size_nat l1 + size_nat (Bin p2 msk2 l2 r2))%nat
             ltac:(simpl size_nat in Hle |- *; lia) l1 (Bin p2 msk2 l2 r2) k ltac:(lia)).
           rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
           (* Goal: match t2_lk with Some _ => None | None => oro l1_lk r1_lk end
              vs   oro (match t2_lk with Some _ => None | None => l1_lk end) r1_lk *)
           destruct (Data.IntSet.Internal.zero k msk1) eqn:Hzk.
           ++ (* zero k msk1 = true: r1_lk = None *)
              rewrite (lookup_right_None p1 msk1 l1 r1 k Hzk).
              rewrite !oro_None_r.
              reflexivity.
           ++ (* zero k msk1 = false: l1_lk = None AND t2_lk = None *)
              rewrite (lookup_left_None p1 msk1 l1 r1 k Hzk).
              rewrite (lookup_left_None p1 msk1 (Bin p2 msk2 l2 r2) r1 k Hzk).
              simpl. reflexivity.
        -- (* merge1/not-zero: bin p1 msk1 l1 (diff r1 t2) *)
           rewrite lookup_bin_oro.
           rewrite (IHn (size_nat r1 + size_nat (Bin p2 msk2 l2 r2))%nat
             ltac:(simpl size_nat in Hle |- *; lia) r1 (Bin p2 msk2 l2 r2) k ltac:(lia)).
           rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
           destruct (Data.IntSet.Internal.zero k msk1) eqn:Hzk.
           ++ (* zero k msk1 = true: r1_lk = None AND t2_lk = None *)
              rewrite (lookup_right_None p1 msk1 l1 r1 k Hzk).
              rewrite (lookup_right_None p1 msk1 l1 (Bin p2 msk2 l2 r2) k Hzk).
              simpl. rewrite !oro_None_r. reflexivity.
           ++ (* zero k msk1 = false: l1_lk = None *)
              rewrite (lookup_left_None p1 msk1 l1 r1 k Hzk). simpl. reflexivity.
    + destruct (shorter msk2 msk1) eqn:Hsh2.
      * (* merge2: shorter msk2 msk1 *)
        destruct (nomatch p1 p2 msk2) eqn:Hnm.
        -- (* nomatch: result = t1 *)
           destruct (Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2)) eqn:Ht2.
           ++ destruct (nomatch_disjoint_lookup p2 msk2 l2 r2 p1 msk1 l1 r1 k Hsh2 Hnm) as [Ht2_none | Ht1_none].
              ** rewrite Ht2_none in Ht2. discriminate.
              ** exact Ht1_none.
           ++ reflexivity.
        -- destruct (Data.IntSet.Internal.zero p1 msk2) eqn:Hz.
           ++ (* merge2/zero: bin p2 msk2 (diff t1 l2) Nil *)
              rewrite lookup_bin_oro. rewrite oro_None_r.
              rewrite (IHn (size_nat (Bin p1 msk1 l1 r1) + size_nat l2)%nat
                ltac:(simpl size_nat in Hle |- *; lia) (Bin p1 msk1 l1 r1) l2 k ltac:(lia)).
              rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
              destruct (Data.IntSet.Internal.zero k msk2) eqn:Hzk.
              ** (* zero k msk2 = true: r2_lk = None *)
                 rewrite (lookup_right_None p2 msk2 l2 r2 k Hzk).
                 rewrite oro_None_r. reflexivity.
              ** (* zero k msk2 = false: l2_lk = None, t1_lk = None *)
                 rewrite (lookup_left_None p2 msk2 l2 r2 k Hzk).
                 rewrite (lookup_left_None p2 msk2 (Bin p1 msk1 l1 r1) r2 k Hzk).
                 destruct (Data.IntMap.Internal.lookup k r2); reflexivity.
           ++ (* merge2/not-zero: bin p2 msk2 Nil (diff t1 r2) *)
              rewrite lookup_bin_oro. rewrite oro_None_l.
              rewrite (IHn (size_nat (Bin p1 msk1 l1 r1) + size_nat r2)%nat
                ltac:(simpl size_nat in Hle |- *; lia) (Bin p1 msk1 l1 r1) r2 k ltac:(lia)).
              rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
              destruct (Data.IntSet.Internal.zero k msk2) eqn:Hzk.
              ** (* zero k msk2 = true: r2_lk = None, t1_lk = None *)
                 rewrite (lookup_right_None p2 msk2 l2 r2 k Hzk).
                 rewrite (lookup_right_None p2 msk2 l2 (Bin p1 msk1 l1 r1) k Hzk).
                 destruct (Data.IntMap.Internal.lookup k l2); reflexivity.
              ** (* zero k msk2 = false: l2_lk = None *)
                 rewrite (lookup_left_None p2 msk2 l2 r2 k Hzk). simpl. reflexivity.
      * (* same length *)
        destruct (p1 == p2) eqn:Hpp.
        -- (* same prefix: bin p1 msk1 (diff l1 l2) (diff r1 r2) *)
           rewrite lookup_bin_oro.
           rewrite (IHn (size_nat l1 + size_nat l2)%nat
             ltac:(simpl size_nat in Hle |- *; lia) l1 l2 k ltac:(lia)).
           rewrite (IHn (size_nat r1 + size_nat r2)%nat
             ltac:(simpl size_nat in Hle |- *; lia) r1 r2 k ltac:(lia)).
           rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
           rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
           destruct (Data.IntSet.Internal.zero k msk1) eqn:Hzk.
           ++ (* zero k msk1 = true: r1 = None, r2 = None *)
              rewrite (lookup_right_None p1 msk1 l1 r1 k Hzk).
              rewrite (lookup_right_None p1 msk1 l2 r2 k Hzk).
              rewrite !oro_None_r. reflexivity.
           ++ (* zero k msk1 = false: l1 = None, l2 = None *)
              rewrite (lookup_left_None p1 msk1 l1 r1 k Hzk).
              rewrite (lookup_left_None p1 msk1 l2 r2 k Hzk).
              simpl. reflexivity.
        -- (* different prefix: result = t1 *)
           destruct (Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2)) eqn:Ht2.
           ++ destruct (diff_prefix_disjoint_lookup p1 msk1 l1 r1 p2 msk2 l2 r2 k Hsh1 Hsh2 Hpp) as [Ht1_none | Ht2_none].
              ** exact Ht1_none.
              ** rewrite Ht2_none in Ht2. discriminate.
           ++ reflexivity.
  - (* Bin/Tip *)
    unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.mergeWithKey, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    match goal with
    | |- context [?f (Tip k2 v2) k2 l1] => set (merge0_fn := f)
    end.
    assert (Hmerge : forall t1 kk,
      Data.IntMap.Internal.lookup kk (merge0_fn (Tip k2 v2) k2 t1) =
      match Data.IntMap.Internal.lookup kk (Tip k2 v2) with Some _ => None | None => Data.IntMap.Internal.lookup kk t1 end).
    { intro t1. induction t1 as [p' m' l' IHl r' IHr | k' v' | ]; intro kk;
      unfold merge0_fn; cbv beta iota zeta; fold merge0_fn.
      - destruct (Data.IntMap.Internal.nomatch k2 p' m') eqn:Hnm'.
        + (* nomatch: result = Bin p' m' l' r' *)
          simpl Data.IntMap.Internal.lookup at 2.
          destruct (kk == k2) eqn:Hkk.
          * move: Hkk => /Eq_eq_Word Hkk. subst kk.
            rewrite (lookup_nomatch_None p' m' l' r' k2 Hnm'). reflexivity.
          * reflexivity.
        + destruct (Data.IntSet.Internal.zero k2 m') eqn:Hz'.
          * (* zero: bin p' m' (merge0 l') r' *)
            rewrite lookup_bin_oro. rewrite IHl.
            rewrite (lookup_Bin_oro p' m' l' r' kk (IntMapProofs.All_IntMaps_WF _ _)).
            destruct (Data.IntSet.Internal.zero kk m') eqn:Hzk.
            ** rewrite (lookup_right_None p' m' l' r' kk Hzk). rewrite !oro_None_r. reflexivity.
            ** rewrite (lookup_left_None p' m' l' r' kk Hzk).
               rewrite (lookup_left_None p' m' (Tip k2 v2) r' kk Hzk).
               simpl. reflexivity.
          * (* not-zero: bin p' m' l' (merge0 r') *)
            rewrite lookup_bin_oro. rewrite IHr.
            rewrite (lookup_Bin_oro p' m' l' r' kk (IntMapProofs.All_IntMaps_WF _ _)).
            destruct (Data.IntSet.Internal.zero kk m') eqn:Hzk.
            ** rewrite (lookup_right_None p' m' l' r' kk Hzk).
               rewrite (lookup_right_None p' m' l' (Tip k2 v2) kk Hzk).
               simpl. rewrite !oro_None_r. reflexivity.
            ** rewrite (lookup_left_None p' m' l' r' kk Hzk). simpl. reflexivity.
      - (* Tip/Tip in merge0 *)
        destruct (k' == k2) eqn:Hkk.
        + (* k' == k2: result = Nil *)
          simpl.
          move: Hkk => /Eq_eq_Word Hkk. subst k'.
          destruct (kk == k2) eqn:Hkk2; reflexivity.
        + (* k' /= k2: result = Tip k' v' *)
          simpl Data.IntMap.Internal.lookup.
          destruct (kk == k2) eqn:Hkk2.
          * move: Hkk2 => /Eq_eq_Word Hkk2. subst kk.
            destruct (k2 == k') eqn:Hk2k; [|reflexivity].
            move: Hk2k => /Eq_eq_Word Hk2k. subst k'.
            rewrite Eq_refl_Word in Hkk. discriminate.
          * reflexivity.
      - (* Nil in merge0: result = Nil *)
        simpl. destruct (kk == k2); reflexivity.
    }
    destruct (Data.IntMap.Internal.nomatch k2 p1 msk1) eqn:Hnm.
    + (* nomatch: result = Bin p1 msk1 l1 r1 *)
      simpl Data.IntMap.Internal.lookup at 2.
      destruct (k == k2) eqn:Hkk.
      * move: Hkk => /Eq_eq_Word Hkk. subst k.
        rewrite (lookup_nomatch_None p1 msk1 l1 r1 k2 Hnm). reflexivity.
      * reflexivity.
    + destruct (Data.IntSet.Internal.zero k2 msk1) eqn:Hz.
      * rewrite lookup_bin_oro. rewrite Hmerge.
        rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
        destruct (Data.IntSet.Internal.zero k msk1) eqn:Hzk.
        ** rewrite (lookup_right_None p1 msk1 l1 r1 k Hzk). rewrite !oro_None_r. reflexivity.
        ** rewrite (lookup_left_None p1 msk1 l1 r1 k Hzk).
           rewrite (lookup_left_None p1 msk1 (Tip k2 v2) r1 k Hzk).
           simpl. reflexivity.
      * rewrite lookup_bin_oro. rewrite Hmerge.
        rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
        destruct (Data.IntSet.Internal.zero k msk1) eqn:Hzk.
        ** rewrite (lookup_right_None p1 msk1 l1 r1 k Hzk).
           rewrite (lookup_right_None p1 msk1 l1 (Tip k2 v2) k Hzk).
           simpl. rewrite !oro_None_r. reflexivity.
        ** rewrite (lookup_left_None p1 msk1 l1 r1 k Hzk). simpl. reflexivity.
  - (* Bin/Nil *)
    unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.mergeWithKey, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    reflexivity.
  - (* Tip/Bin *)
    unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.mergeWithKey, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    match goal with
    | |- context [?f (Tip k1 v1) k1 l2] => set (merge0_fn := f)
    end.
    assert (Hmerge : forall t2 kk,
      Data.IntMap.Internal.lookup kk (merge0_fn (Tip k1 v1) k1 t2) =
      match Data.IntMap.Internal.lookup kk t2 with Some _ => None | None => Data.IntMap.Internal.lookup kk (Tip k1 v1) end).
    { intro t2. induction t2 as [p' m' l' IHl r' IHr | k' v' | ]; intro kk;
      unfold merge0_fn; cbv beta iota zeta; fold merge0_fn.
      - destruct (Data.IntMap.Internal.nomatch k1 p' m') eqn:Hnm'.
        + (* nomatch: result = Tip k1 v1 *)
          destruct (kk == k1) eqn:Hkk1.
          * move: Hkk1 => /Eq_eq_Word Hkk1. subst kk.
            rewrite (lookup_nomatch_None p' m' l' r' k1 Hnm'). simpl. reflexivity.
          * destruct (Data.IntMap.Internal.lookup kk (Bin p' m' l' r'));
            simpl Data.IntMap.Internal.lookup; rewrite Hkk1; reflexivity.
        + destruct (Data.IntSet.Internal.zero k1 m') eqn:Hz'.
          * (* zero: bin p' m' (merge0 l') Nil *)
            rewrite lookup_bin_oro. rewrite oro_None_r. rewrite IHl.
            rewrite (lookup_Bin_oro p' m' l' r' kk (IntMapProofs.All_IntMaps_WF _ _)).
            destruct (Data.IntSet.Internal.zero kk m') eqn:Hzk.
            ** rewrite (lookup_right_None p' m' l' r' kk Hzk). rewrite oro_None_r. reflexivity.
            ** rewrite (lookup_left_None p' m' l' r' kk Hzk).
               rewrite (lookup_left_None p' m' (Tip k1 v1) r' kk Hzk).
               destruct (Data.IntMap.Internal.lookup kk r'); reflexivity.
          * (* not-zero: bin p' m' Nil (merge0 r') *)
            rewrite lookup_bin_oro. rewrite oro_None_l. rewrite IHr.
            rewrite (lookup_Bin_oro p' m' l' r' kk (IntMapProofs.All_IntMaps_WF _ _)).
            destruct (Data.IntSet.Internal.zero kk m') eqn:Hzk.
            ** rewrite (lookup_right_None p' m' l' r' kk Hzk).
               rewrite (lookup_right_None p' m' l' (Tip k1 v1) kk Hzk).
               destruct (Data.IntMap.Internal.lookup kk l'); reflexivity.
            ** rewrite (lookup_left_None p' m' l' r' kk Hzk). simpl. reflexivity.
      - (* Tip/Tip in merge0 *)
        destruct (k1 == k') eqn:Hkk.
        + (* k1 == k': combine returns Nil *)
          simpl.
          move: Hkk => /Eq_eq_Word Hkk. subst k1.
          destruct (kk == k'); reflexivity.
        + (* k1 /= k': result = Tip k1 v1 *)
          simpl Data.IntMap.Internal.lookup.
          destruct (kk == k') eqn:Hkkk.
          * move: Hkkk => /Eq_eq_Word Hkkk. subst kk.
            destruct (k' == k1) eqn:Hk1k; [|reflexivity].
            move: Hk1k => /Eq_eq_Word Hk1k. subst k'.
            rewrite Eq_refl_Word in Hkk. discriminate.
          * reflexivity.
      - (* Nil in merge0: result = Tip k1 v1 *)
        simpl. reflexivity.
    }
    destruct (Data.IntMap.Internal.nomatch k1 p2 msk2) eqn:Hnm.
    + (* nomatch: result = Tip k1 v1 *)
      destruct (k == k1) eqn:Hkk1.
      * move: Hkk1 => /Eq_eq_Word Hkk1. subst k.
        rewrite (lookup_nomatch_None p2 msk2 l2 r2 k1 Hnm). simpl. reflexivity.
      * destruct (Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2));
        simpl Data.IntMap.Internal.lookup; rewrite Hkk1; reflexivity.
    + destruct (Data.IntSet.Internal.zero k1 msk2) eqn:Hz.
      * rewrite lookup_bin_oro. rewrite oro_None_r. rewrite Hmerge.
        rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
        destruct (Data.IntSet.Internal.zero k msk2) eqn:Hzk.
        ** rewrite (lookup_right_None p2 msk2 l2 r2 k Hzk). rewrite oro_None_r. reflexivity.
        ** rewrite (lookup_left_None p2 msk2 l2 r2 k Hzk).
           rewrite (lookup_left_None p2 msk2 (Tip k1 v1) r2 k Hzk).
           destruct (Data.IntMap.Internal.lookup k r2); reflexivity.
      * rewrite lookup_bin_oro. rewrite oro_None_l. rewrite Hmerge.
        rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
        destruct (Data.IntSet.Internal.zero k msk2) eqn:Hzk.
        ** rewrite (lookup_right_None p2 msk2 l2 r2 k Hzk).
           rewrite (lookup_right_None p2 msk2 l2 (Tip k1 v1) k Hzk).
           destruct (Data.IntMap.Internal.lookup k l2); reflexivity.
        ** rewrite (lookup_left_None p2 msk2 l2 r2 k Hzk). simpl. reflexivity.
  - (* Tip/Tip *)
    unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.mergeWithKey, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    destruct (k1 == k2) eqn:Hkk.
    + simpl.
      move: Hkk => /Eq_eq_Word Hkk. subst k1.
      destruct (k == k2); reflexivity.
    + simpl Data.IntMap.Internal.lookup.
      destruct (k == k1) eqn:Hkk1, (k == k2) eqn:Hkk2; try reflexivity.
      move: Hkk1 => /Eq_eq_Word Hkk1. move: Hkk2 => /Eq_eq_Word Hkk2. subst.
      rewrite Eq_refl_Word in Hkk. discriminate.
  - (* Tip/Nil *)
    unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.mergeWithKey, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    reflexivity.
  - (* Nil/Bin *)
    unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.mergeWithKey, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    destruct (Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2)); reflexivity.
  - (* Nil/Tip *)
    unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.mergeWithKey, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    destruct (Data.IntMap.Internal.lookup k (Tip k2 v2)); simpl; reflexivity.
  - (* Nil/Nil *)
    unfold Data.IntMap.Internal.difference, Data.IntMap.Internal.mergeWithKey, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    reflexivity.
Qed.

(* Helper: one-step unfolding of intersection for the Bin/Bin case *)
Local Lemma intersection_unfold_BinBin : forall A B p1 msk1 (l1 r1 : IntMap.IntMap A) p2 msk2 (l2 r2 : IntMap.IntMap B),
  Data.IntMap.Internal.intersection (Bin p1 msk1 l1 r1) (Bin p2 msk2 l2 r2) =
  (let t1 := Bin p1 msk1 l1 r1 in
   let t2 := Bin p2 msk2 l2 r2 in
   if shorter msk1 msk2 then
    if nomatch p2 p1 msk1 then Nil
    else if Data.IntSet.Internal.zero p2 msk1 then bin p1 msk1 (Data.IntMap.Internal.intersection l1 t2) Nil
    else bin p1 msk1 Nil (Data.IntMap.Internal.intersection r1 t2)
  else if shorter msk2 msk1 then
    if nomatch p1 p2 msk2 then Nil
    else if Data.IntSet.Internal.zero p1 msk2 then bin p2 msk2 (Data.IntMap.Internal.intersection t1 l2) Nil
    else bin p2 msk2 Nil (Data.IntMap.Internal.intersection t1 r2)
  else if p1 == p2 then bin p1 msk1 (Data.IntMap.Internal.intersection l1 l2) (Data.IntMap.Internal.intersection r1 r2)
  else Nil).
Proof.
  intros. unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
  rewrite {1}IntMapProofs.deferredFix2_eq.
  cbv beta iota zeta delta [GHC.Base.const GHC.Base.id].
  reflexivity.
Qed.

Local Lemma lookup_intersection_eq : forall A B (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B) k,
  Data.IntMap.Internal.lookup k (Data.IntMap.Internal.intersection m1 m2) =
  match Data.IntMap.Internal.lookup k m2 with Some _ => Data.IntMap.Internal.lookup k m1 | None => None end.
Proof.
  intros A B.
  enough (Hstrong : forall n (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B) k,
    (size_nat m1 + size_nat m2 <= n)%nat ->
    Data.IntMap.Internal.lookup k (Data.IntMap.Internal.intersection m1 m2) =
    match Data.IntMap.Internal.lookup k m2 with Some _ => Data.IntMap.Internal.lookup k m1 | None => None end).
  { intros m1 m2 k. exact (Hstrong _ m1 m2 k (Nat.le_refl _)). }
  intro n. induction n as [n IHn] using lt_wf_ind.
  intros m1 m2 k Hle.
  destruct m1 as [p1 msk1 l1 r1 | k1 v1 | ];
  destruct m2 as [p2 msk2 l2 r2 | k2 v2 | ].
  - (* Bin/Bin *)
    rewrite intersection_unfold_BinBin. cbv beta zeta.
    destruct (shorter msk1 msk2) eqn:Hsh1.
    + (* merge1: shorter msk1 msk2 *)
      destruct (nomatch p2 p1 msk1) eqn:Hnm.
      * (* nomatch: result = Nil *)
        change (Data.IntMap.Internal.lookup k (@Nil A)) with (@None A).
        destruct (nomatch_disjoint_lookup p1 msk1 l1 r1 p2 msk2 l2 r2 k Hsh1 Hnm) as [Ht1 | Ht2].
        -- rewrite Ht1. destruct (Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2)); reflexivity.
        -- rewrite Ht2. reflexivity.
      * destruct (Data.IntSet.Internal.zero p2 msk1) eqn:Hz.
        -- (* merge1/zero: bin p1 msk1 (inter l1 t2) Nil *)
           rewrite lookup_bin_oro. rewrite oro_None_r.
           rewrite (IHn (size_nat l1 + size_nat (Bin p2 msk2 l2 r2))%nat
             ltac:(simpl size_nat in Hle |- *; lia) l1 (Bin p2 msk2 l2 r2) k ltac:(lia)).
           rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
           destruct (Data.IntSet.Internal.zero k msk1) eqn:Hzk.
           ++ rewrite (lookup_right_None p1 msk1 l1 r1 k Hzk).
              rewrite oro_None_r. reflexivity.
           ++ rewrite (lookup_left_None p1 msk1 l1 r1 k Hzk).
              rewrite (lookup_left_None p1 msk1 (Bin p2 msk2 l2 r2) r1 k Hzk).
              reflexivity.
        -- (* merge1/not-zero: bin p1 msk1 Nil (inter r1 t2) *)
           rewrite lookup_bin_oro. rewrite oro_None_l.
           rewrite (IHn (size_nat r1 + size_nat (Bin p2 msk2 l2 r2))%nat
             ltac:(simpl size_nat in Hle |- *; lia) r1 (Bin p2 msk2 l2 r2) k ltac:(lia)).
           rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
           destruct (Data.IntSet.Internal.zero k msk1) eqn:Hzk.
           ++ rewrite (lookup_right_None p1 msk1 l1 r1 k Hzk).
              rewrite (lookup_right_None p1 msk1 l1 (Bin p2 msk2 l2 r2) k Hzk).
              reflexivity.
           ++ rewrite (lookup_left_None p1 msk1 l1 r1 k Hzk). simpl. reflexivity.
    + destruct (shorter msk2 msk1) eqn:Hsh2.
      * (* merge2: shorter msk2 msk1 *)
        destruct (nomatch p1 p2 msk2) eqn:Hnm.
        -- (* nomatch: result = Nil *)
           change (Data.IntMap.Internal.lookup k (@Nil A)) with (@None A).
           destruct (nomatch_disjoint_lookup p2 msk2 l2 r2 p1 msk1 l1 r1 k Hsh2 Hnm) as [Ht2 | Ht1].
           ++ rewrite Ht2. reflexivity.
           ++ rewrite Ht1. destruct (Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2)); reflexivity.
        -- destruct (Data.IntSet.Internal.zero p1 msk2) eqn:Hz.
           ++ (* merge2/zero: bin p2 msk2 (inter t1 l2) Nil *)
              rewrite lookup_bin_oro. rewrite oro_None_r.
              rewrite (IHn (size_nat (Bin p1 msk1 l1 r1) + size_nat l2)%nat
                ltac:(simpl size_nat in Hle |- *; lia) (Bin p1 msk1 l1 r1) l2 k ltac:(lia)).
              rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
              destruct (Data.IntSet.Internal.zero k msk2) eqn:Hzk.
              ** rewrite (lookup_right_None p2 msk2 l2 r2 k Hzk).
                 rewrite oro_None_r. reflexivity.
              ** rewrite (lookup_left_None p2 msk2 l2 r2 k Hzk).
                 rewrite (lookup_left_None p2 msk2 (Bin p1 msk1 l1 r1) r2 k Hzk).
                 rewrite oro_None_l.
                 destruct (Data.IntMap.Internal.lookup k r2); reflexivity.
           ++ (* merge2/not-zero: bin p2 msk2 Nil (inter t1 r2) *)
              rewrite lookup_bin_oro. rewrite oro_None_l.
              rewrite (IHn (size_nat (Bin p1 msk1 l1 r1) + size_nat r2)%nat
                ltac:(simpl size_nat in Hle |- *; lia) (Bin p1 msk1 l1 r1) r2 k ltac:(lia)).
              rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
              destruct (Data.IntSet.Internal.zero k msk2) eqn:Hzk.
              ** rewrite (lookup_right_None p2 msk2 l2 r2 k Hzk).
                 rewrite (lookup_right_None p2 msk2 l2 (Bin p1 msk1 l1 r1) k Hzk).
                 rewrite oro_None_r.
                 destruct (Data.IntMap.Internal.lookup k l2); reflexivity.
              ** rewrite (lookup_left_None p2 msk2 l2 r2 k Hzk).
                 rewrite (lookup_left_None p2 msk2 (Bin p1 msk1 l1 r1) r2 k Hzk).
                 rewrite oro_None_l.
                 destruct (Data.IntMap.Internal.lookup k r2); reflexivity.
      * (* same length *)
        destruct (p1 == p2) eqn:Hpp.
        -- (* same prefix *)
           rewrite lookup_bin_oro.
           rewrite (IHn (size_nat l1 + size_nat l2)%nat
             ltac:(simpl size_nat in Hle |- *; lia) l1 l2 k ltac:(lia)).
           rewrite (IHn (size_nat r1 + size_nat r2)%nat
             ltac:(simpl size_nat in Hle |- *; lia) r1 r2 k ltac:(lia)).
           rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
           rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
           destruct (Data.IntSet.Internal.zero k msk1) eqn:Hzk.
           ++ rewrite (lookup_right_None p1 msk1 l1 r1 k Hzk).
              rewrite (lookup_right_None p1 msk1 l2 r2 k Hzk).
              rewrite !oro_None_r. reflexivity.
           ++ rewrite (lookup_left_None p1 msk1 l1 r1 k Hzk).
              rewrite (lookup_left_None p1 msk1 l2 r2 k Hzk).
              simpl. reflexivity.
        -- (* different prefix: result = Nil *)
           change (Data.IntMap.Internal.lookup k (@Nil A)) with (@None A).
           destruct (diff_prefix_disjoint_lookup p1 msk1 l1 r1 p2 msk2 l2 r2 k Hsh1 Hsh2 Hpp) as [Ht1 | Ht2].
           ++ rewrite Ht1. destruct (Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2)); reflexivity.
           ++ rewrite Ht2. reflexivity.
  - (* Bin/Tip *)
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    match goal with
    | |- context [?f (Tip k2 v2) k2 l1] => set (merge0_fn := f)
    end.
    assert (Hmerge : forall t1 kk,
      Data.IntMap.Internal.lookup kk (merge0_fn (Tip k2 v2) k2 t1) =
      match Data.IntMap.Internal.lookup kk (Tip k2 v2) with Some _ => Data.IntMap.Internal.lookup kk t1 | None => None end).
    { intro t1. induction t1 as [p' m' l' IHl r' IHr | k' v' | ]; intro kk;
      unfold merge0_fn; cbv beta iota zeta; fold merge0_fn.
      - destruct (Data.IntMap.Internal.nomatch k2 p' m') eqn:Hnm'.
        + (* nomatch: result = Nil *)
          change (Data.IntMap.Internal.lookup kk (@Nil A)) with (@None A).
          destruct (kk == k2) eqn:Hkk1.
          * move: Hkk1 => /Eq_eq_Word Hkk1. subst kk.
            rewrite (lookup_nomatch_None p' m' l' r' k2 Hnm').
            simpl Data.IntMap.Internal.lookup. rewrite Eq_refl_Word. reflexivity.
          * simpl Data.IntMap.Internal.lookup. rewrite Hkk1. reflexivity.
        + destruct (Data.IntSet.Internal.zero k2 m') eqn:Hz'.
          * (* zero: bin p' m' (merge0 l') Nil *)
            rewrite lookup_bin_oro. rewrite oro_None_r. rewrite IHl.
            rewrite (lookup_Bin_oro p' m' l' r' kk (IntMapProofs.All_IntMaps_WF _ _)).
            destruct (Data.IntSet.Internal.zero kk m') eqn:Hzk.
            ** rewrite (lookup_right_None p' m' l' r' kk Hzk). rewrite oro_None_r. reflexivity.
            ** rewrite (lookup_left_None p' m' l' r' kk Hzk).
               rewrite (lookup_left_None p' m' (Tip k2 v2) r' kk Hzk).
               destruct (Data.IntMap.Internal.lookup kk r'); reflexivity.
          * (* not-zero: bin p' m' Nil (merge0 r') *)
            rewrite lookup_bin_oro. rewrite oro_None_l. rewrite IHr.
            rewrite (lookup_Bin_oro p' m' l' r' kk (IntMapProofs.All_IntMaps_WF _ _)).
            destruct (Data.IntSet.Internal.zero kk m') eqn:Hzk.
            ** rewrite (lookup_right_None p' m' l' r' kk Hzk).
               rewrite (lookup_right_None p' m' l' (Tip k2 v2) kk Hzk).
               destruct (Data.IntMap.Internal.lookup kk l'); reflexivity.
            ** rewrite (lookup_left_None p' m' l' r' kk Hzk).
               change (Data.IntMap.Internal.lookup kk (@Nil A)) with (@None A).
               simpl Data.IntMap.Internal.lookup. destruct (kk == k2); reflexivity.
      - (* Tip/Tip in merge0 *)
        destruct (k' == k2) eqn:Hkk.
        + (* k' == k2: result = Tip k' v' (kept by const) *)
          simpl Data.IntMap.Internal.lookup.
          move: Hkk => /Eq_eq_Word Hkk. subst k'.
          destruct (kk == k2); reflexivity.
        + (* k' /= k2: result = Nil *)
          change (Data.IntMap.Internal.lookup kk (@Nil A)) with (@None A).
          simpl Data.IntMap.Internal.lookup.
          destruct (kk == k2) eqn:Hkk2.
          * move: Hkk2 => /Eq_eq_Word Hkk2. subst kk.
            destruct (k2 == k') eqn:Hk2k; [|reflexivity].
            move: Hk2k => /Eq_eq_Word Hk2k. subst k'.
            rewrite Eq_refl_Word in Hkk. discriminate.
          * reflexivity.
      - (* Nil in merge0: result = Nil *)
        change (Data.IntMap.Internal.lookup kk (@Nil A)) with (@None A).
        simpl Data.IntMap.Internal.lookup. destruct (kk == k2); reflexivity.
    }
    destruct (Data.IntMap.Internal.nomatch k2 p1 msk1) eqn:Hnm.
    + (* nomatch: result = Nil *)
      change (Data.IntMap.Internal.lookup k (@Nil A)) with (@None A).
      destruct (k == k2) eqn:Hkk.
      * move: Hkk => /Eq_eq_Word Hkk. subst k.
        rewrite (lookup_nomatch_None p1 msk1 l1 r1 k2 Hnm).
        simpl Data.IntMap.Internal.lookup. rewrite Eq_refl_Word. reflexivity.
      * simpl Data.IntMap.Internal.lookup. rewrite Hkk. reflexivity.
    + destruct (Data.IntSet.Internal.zero k2 msk1) eqn:Hz.
      * rewrite lookup_bin_oro. rewrite oro_None_r. rewrite Hmerge.
        rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
        destruct (Data.IntSet.Internal.zero k msk1) eqn:Hzk.
        ** rewrite (lookup_right_None p1 msk1 l1 r1 k Hzk). rewrite oro_None_r. reflexivity.
        ** rewrite (lookup_left_None p1 msk1 l1 r1 k Hzk).
           rewrite (lookup_left_None p1 msk1 (Tip k2 v2) r1 k Hzk).
           reflexivity.
      * rewrite lookup_bin_oro. rewrite oro_None_l. rewrite Hmerge.
        rewrite (lookup_Bin_oro p1 msk1 l1 r1 k (IntMapProofs.All_IntMaps_WF _ _)).
        destruct (Data.IntSet.Internal.zero k msk1) eqn:Hzk.
        ** rewrite (lookup_right_None p1 msk1 l1 r1 k Hzk).
           rewrite (lookup_right_None p1 msk1 l1 (Tip k2 v2) k Hzk).
           reflexivity.
        ** rewrite (lookup_left_None p1 msk1 l1 r1 k Hzk).
           change (Data.IntMap.Internal.lookup k (@Nil A)) with (@None A).
           reflexivity.
  - (* Bin/Nil *)
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    reflexivity.
  - (* Tip/Bin *)
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    match goal with
    | |- context [?f (Tip k1 v1) k1 l2] => set (merge0_fn := f)
    end.
    assert (Hmerge : forall t2 kk,
      Data.IntMap.Internal.lookup kk (merge0_fn (Tip k1 v1) k1 t2) =
      match Data.IntMap.Internal.lookup kk t2 with Some _ => Data.IntMap.Internal.lookup kk (Tip k1 v1) | None => None end).
    { intro t2. induction t2 as [p' m' l' IHl r' IHr | k' v' | ]; intro kk;
      unfold merge0_fn; cbv beta iota zeta; fold merge0_fn.
      - destruct (Data.IntMap.Internal.nomatch k1 p' m') eqn:Hnm'.
        + (* nomatch: result = Nil *)
          change (Data.IntMap.Internal.lookup kk (@Nil A)) with (@None A).
          destruct (kk == k1) eqn:Hkk1.
          * move: Hkk1 => /Eq_eq_Word Hkk1. subst kk.
            rewrite (lookup_nomatch_None p' m' l' r' k1 Hnm'). reflexivity.
          * destruct (Data.IntMap.Internal.lookup kk (Bin p' m' l' r')); [|reflexivity].
            simpl Data.IntMap.Internal.lookup. rewrite Hkk1. reflexivity.
        + destruct (Data.IntSet.Internal.zero k1 m') eqn:Hz'.
          * (* zero: bin p' m' (merge0 l') Nil *)
            rewrite lookup_bin_oro. rewrite oro_None_r. rewrite IHl.
            rewrite (lookup_Bin_oro p' m' l' r' kk (IntMapProofs.All_IntMaps_WF _ _)).
            destruct (Data.IntSet.Internal.zero kk m') eqn:Hzk.
            ** rewrite (lookup_right_None p' m' l' r' kk Hzk). rewrite oro_None_r. reflexivity.
            ** rewrite (lookup_left_None p' m' l' r' kk Hzk).
               rewrite (lookup_left_None p' m' (Tip k1 v1) r' kk Hzk).
               destruct (Data.IntMap.Internal.lookup kk r'); reflexivity.
          * (* not-zero: bin p' m' Nil (merge0 r') *)
            rewrite lookup_bin_oro. rewrite oro_None_l. rewrite IHr.
            rewrite (lookup_Bin_oro p' m' l' r' kk (IntMapProofs.All_IntMaps_WF _ _)).
            destruct (Data.IntSet.Internal.zero kk m') eqn:Hzk.
            ** rewrite (lookup_right_None p' m' l' r' kk Hzk).
               rewrite (lookup_right_None p' m' l' (Tip k1 v1) kk Hzk).
               destruct (Data.IntMap.Internal.lookup kk l'); reflexivity.
            ** rewrite (lookup_left_None p' m' l' r' kk Hzk).
               change (Data.IntMap.Internal.lookup kk (@Nil A)) with (@None A).
               simpl Data.IntMap.Internal.lookup. destruct (kk == k1); reflexivity.
      - (* Tip/Tip in merge0 *)
        destruct (k1 == k') eqn:Hkk.
        + (* k1 == k': combine keeps Tip k1 v1 *)
          simpl Data.IntMap.Internal.lookup.
          move: Hkk => /Eq_eq_Word Hkk. subst k1.
          destruct (kk == k'); reflexivity.
        + (* k1 /= k': result = Nil *)
          change (Data.IntMap.Internal.lookup kk (@Nil A)) with (@None A).
          simpl Data.IntMap.Internal.lookup.
          destruct (kk == k') eqn:Hkkk.
          * move: Hkkk => /Eq_eq_Word Hkkk. subst kk.
            destruct (k' == k1) eqn:Hk1k; [|reflexivity].
            move: Hk1k => /Eq_eq_Word Hk1k. subst k'.
            rewrite Eq_refl_Word in Hkk. discriminate.
          * reflexivity.
      - (* Nil in merge0: result = Nil *)
        change (Data.IntMap.Internal.lookup kk (@Nil A)) with (@None A).
        reflexivity.
    }
    destruct (Data.IntMap.Internal.nomatch k1 p2 msk2) eqn:Hnm.
    + (* nomatch: result = Nil *)
      change (Data.IntMap.Internal.lookup k (@Nil A)) with (@None A).
      destruct (k == k1) eqn:Hkk1.
      * move: Hkk1 => /Eq_eq_Word Hkk1. subst k.
        rewrite (lookup_nomatch_None p2 msk2 l2 r2 k1 Hnm). reflexivity.
      * destruct (Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2)); [|reflexivity].
        simpl Data.IntMap.Internal.lookup. rewrite Hkk1. reflexivity.
    + destruct (Data.IntSet.Internal.zero k1 msk2) eqn:Hz.
      * rewrite lookup_bin_oro. rewrite oro_None_r. rewrite Hmerge.
        rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
        destruct (Data.IntSet.Internal.zero k msk2) eqn:Hzk.
        ** rewrite (lookup_right_None p2 msk2 l2 r2 k Hzk). rewrite oro_None_r. reflexivity.
        ** rewrite (lookup_left_None p2 msk2 l2 r2 k Hzk).
           rewrite (lookup_left_None p2 msk2 (Tip k1 v1) r2 k Hzk).
           destruct (Data.IntMap.Internal.lookup k r2); reflexivity.
      * rewrite lookup_bin_oro. rewrite oro_None_l. rewrite Hmerge.
        rewrite (lookup_Bin_oro p2 msk2 l2 r2 k (IntMapProofs.All_IntMaps_WF _ _)).
        destruct (Data.IntSet.Internal.zero k msk2) eqn:Hzk.
        ** rewrite (lookup_right_None p2 msk2 l2 r2 k Hzk).
           rewrite (lookup_right_None p2 msk2 l2 (Tip k1 v1) k Hzk).
           destruct (Data.IntMap.Internal.lookup k l2); reflexivity.
        ** rewrite (lookup_left_None p2 msk2 l2 r2 k Hzk).
           rewrite (lookup_left_None p2 msk2 (Tip k1 v1) r2 k Hzk).
           destruct (Data.IntMap.Internal.lookup k r2); reflexivity.
  - (* Tip/Tip *)
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    destruct (k1 == k2) eqn:Hkk.
    + simpl Data.IntMap.Internal.lookup.
      move: Hkk => /Eq_eq_Word Hkk. subst k1.
      destruct (k == k2); reflexivity.
    + (* k1 /= k2: result = Nil *)
      change (Data.IntMap.Internal.lookup k (@Nil A)) with (@None A).
      simpl Data.IntMap.Internal.lookup.
      destruct (k == k2) eqn:Hkk2.
      * move: Hkk2 => /Eq_eq_Word Hkk2. subst k.
        destruct (k2 == k1) eqn:Hk21; [|reflexivity].
        move: Hk21 => /Eq_eq_Word Hk21. subst k2.
        rewrite Eq_refl_Word in Hkk. discriminate.
      * reflexivity.
  - (* Tip/Nil *)
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    reflexivity.
  - (* Nil/Bin *)
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    destruct (Data.IntMap.Internal.lookup k (Bin p2 msk2 l2 r2)); reflexivity.
  - (* Nil/Tip *)
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    destruct (Data.IntMap.Internal.lookup k (Tip k2 v2)); reflexivity.
  - (* Nil/Nil *)
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq.
    cbv beta iota zeta delta [GHC.Base.id GHC.Base.const].
    reflexivity.
Qed.

(* Boolean helper: b1 = true <-> b2 = true -> b1 = b2 *)
Local Lemma bool_eq_of_iff : forall b1 b2 : bool,
  (b1 = true <-> b2 = true) -> b1 = b2.
Proof.
  intros [] []; intuition discriminate.
Qed.

(* member k (inter m1 m2) = member k m1 && member k m2 — moved here for disjoint proof *)
Local Lemma member_intersection_local : forall A B k (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
    Data.IntMap.Internal.member k (Data.IntMap.Internal.intersection m1 m2) =
    Data.IntMap.Internal.member k m1 && Data.IntMap.Internal.member k m2.
Proof.
  intros A B k m1 m2.
  rewrite !member_isSome lookup_intersection_eq.
  destruct (Data.IntMap.Internal.lookup k m2) eqn:Hm2;
    destruct (Data.IntMap.Internal.lookup k m1) eqn:Hm1;
    simpl; reflexivity.
Qed.

(* null of bin smart constructor *)
Local Lemma null_bin : forall A p m (l r : IntMap.IntMap A),
  Data.IntMap.Internal.null (bin p m l r) = Data.IntMap.Internal.null l && Data.IntMap.Internal.null r.
Proof. intros A p m l r. destruct l; destruct r; reflexivity. Qed.

(* One-step unfolding of disjoint for Bin/Bin case *)
Local Lemma disjoint_unfold_BinBin : forall A B p1 msk1 (l1 r1 : IntMap.IntMap A) p2 msk2 (l2 r2 : IntMap.IntMap B),
  Data.IntMap.Internal.disjoint (Bin p1 msk1 l1 r1) (Bin p2 msk2 l2 r2) =
  (let t1 := Bin p1 msk1 l1 r1 in
   let t2 := Bin p2 msk2 l2 r2 in
   if shorter msk1 msk2 then
    if nomatch p2 p1 msk1 then true
    else if Data.IntSet.Internal.zero p2 msk1 then Data.IntMap.Internal.disjoint l1 t2
    else Data.IntMap.Internal.disjoint r1 t2
  else if shorter msk2 msk1 then
    if nomatch p1 p2 msk2 then true
    else if Data.IntSet.Internal.zero p1 msk2 then Data.IntMap.Internal.disjoint t1 l2
    else Data.IntMap.Internal.disjoint t1 r2
  else if p1 == p2 then Data.IntMap.Internal.disjoint l1 l2 && Data.IntMap.Internal.disjoint r1 r2
  else true).
Proof. intros. unfold Data.IntMap.Internal.disjoint. rewrite {1}IntMapProofs.deferredFix2_eq. reflexivity. Qed.

(* Helper: negb (member key m) = null (inter (Tip key val) m) *)
Local Lemma disjoint_tip_null_inter : forall A B key (val : A) (m : IntMap.IntMap B),
  negb (Data.IntMap.Internal.member key m) =
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection (Tip key val) m).
Proof.
  intros. apply bool_eq_of_iff. split.
  - intro H1. apply (proj2 (null_member _ _)). intros k.
    rewrite member_intersection_local. simpl Data.IntMap.Internal.member at 1.
    destruct (k == key) eqn:Hkeq; simpl.
    + move: Hkeq => /Eq_eq_Word Hkeq. subst k.
      destruct (Data.IntMap.Internal.member key m); [simpl in H1; discriminate | reflexivity].
    + reflexivity.
  - intro Hn. pose proof (proj1 (null_member _ _) Hn key) as Hk.
    rewrite member_intersection_local in Hk. simpl Data.IntMap.Internal.member at 1 in Hk.
    rewrite Eq_refl_Word in Hk. simpl in Hk.
    destruct (Data.IntMap.Internal.member key m); [discriminate | reflexivity].
Qed.

(* Symmetric helper: negb (member key m) = null (inter m (Tip key val)) *)
Local Lemma disjoint_tip_null_inter_r : forall A B key (val : B) (m : IntMap.IntMap A),
  negb (Data.IntMap.Internal.member key m) =
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection m (Tip key val)).
Proof.
  intros. apply bool_eq_of_iff. split.
  - intro H1. apply (proj2 (null_member _ _)). intros k.
    rewrite member_intersection_local. simpl Data.IntMap.Internal.member at 2.
    destruct (k == key) eqn:Hkeq.
    + move: Hkeq => /Eq_eq_Word Hkeq. subst k.
      rewrite Bool.andb_true_r.
      destruct (Data.IntMap.Internal.member key m); [simpl in H1; discriminate | reflexivity].
    + rewrite Bool.andb_false_r. reflexivity.
  - intro Hn. pose proof (proj1 (null_member _ _) Hn key) as Hk.
    rewrite member_intersection_local in Hk. simpl Data.IntMap.Internal.member at 2 in Hk.
    rewrite Eq_refl_Word Bool.andb_true_r in Hk.
    destruct (Data.IntMap.Internal.member key m); [discriminate | reflexivity].
Qed.

(* Key intermediate lemma: disjoint = null . intersection *)
Local Lemma disjoint_null_intersection : forall A B (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
  Data.IntMap.Internal.disjoint m1 m2 = Data.IntMap.Internal.null (Data.IntMap.Internal.intersection m1 m2).
Proof.
  intros A B.
  enough (Hstrong : forall n (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
    (size_nat m1 + size_nat m2 <= n)%nat ->
    Data.IntMap.Internal.disjoint m1 m2 = Data.IntMap.Internal.null (Data.IntMap.Internal.intersection m1 m2)).
  { intros m1 m2. exact (Hstrong _ m1 m2 (Nat.le_refl _)). }
  intro n. induction n as [n IHn] using lt_wf_ind.
  intros m1 m2 Hle.
  destruct m1 as [p1 msk1 l1 r1 | kx vx | ];
  destruct m2 as [p2 msk2 l2 r2 | ky vy | ].
  - (* Bin/Bin *)
    rewrite disjoint_unfold_BinBin intersection_unfold_BinBin. cbv beta zeta.
    set (t2 := Bin p2 msk2 l2 r2) in *.
    set (t1 := Bin p1 msk1 l1 r1) in Hle.
    destruct (shorter msk1 msk2) eqn:Hsh1.
    + destruct (nomatch p2 p1 msk1) eqn:Hnm.
      * reflexivity.
      * destruct (Data.IntSet.Internal.zero p2 msk1) eqn:Hz.
        -- rewrite null_bin Bool.andb_true_r.
           apply (IHn (size_nat l1 + size_nat t2)%nat
             ltac:(subst t1; simpl size_nat in Hle |- *; lia) l1 t2
             ltac:(lia)).
        -- rewrite null_bin.
           change (Data.IntMap.Internal.null (@Nil A)) with true. simpl.
           apply (IHn (size_nat r1 + size_nat t2)%nat
             ltac:(subst t1; simpl size_nat in Hle |- *; lia) r1 t2
             ltac:(lia)).
    + destruct (shorter msk2 msk1) eqn:Hsh2.
      * destruct (nomatch p1 p2 msk2) eqn:Hnm.
        -- reflexivity.
        -- destruct (Data.IntSet.Internal.zero p1 msk2) eqn:Hz.
           ++ rewrite null_bin Bool.andb_true_r.
              apply (IHn (size_nat t1 + size_nat l2)%nat
                ltac:(subst t1 t2; simpl size_nat in Hle |- *; lia) t1 l2
                ltac:(subst t1; simpl size_nat; lia)).
           ++ rewrite null_bin.
              change (Data.IntMap.Internal.null (@Nil B)) with true. simpl.
              apply (IHn (size_nat t1 + size_nat r2)%nat
                ltac:(subst t1 t2; simpl size_nat in Hle |- *; lia) t1 r2
                ltac:(subst t1; simpl size_nat; lia)).
      * destruct (p1 == p2) eqn:Hpp.
        -- rewrite null_bin. f_equal.
           ++ apply (IHn (size_nat l1 + size_nat l2)%nat
                ltac:(subst t1 t2; simpl size_nat in Hle |- *; lia) l1 l2
                ltac:(simpl size_nat; lia)).
           ++ apply (IHn (size_nat r1 + size_nat r2)%nat
                ltac:(subst t1 t2; simpl size_nat in Hle |- *; lia) r1 r2
                ltac:(simpl size_nat; lia)).
        -- reflexivity.
  - (* Bin/Tip *)
    unfold Data.IntMap.Internal.disjoint. rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta.
    unfold Data.IntMap.Internal.notMember.
    apply disjoint_tip_null_inter_r.
  - (* Bin/Nil *)
    unfold Data.IntMap.Internal.disjoint. rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta.
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta delta [GHC.Base.const GHC.Base.id].
    reflexivity.
  - (* Tip/Bin *)
    unfold Data.IntMap.Internal.disjoint. rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta.
    unfold Data.IntMap.Internal.notMember.
    apply disjoint_tip_null_inter.
  - (* Tip/Tip *)
    unfold Data.IntMap.Internal.disjoint. rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta.
    unfold Data.IntMap.Internal.notMember.
    apply disjoint_tip_null_inter.
  - (* Tip/Nil *)
    unfold Data.IntMap.Internal.disjoint. rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta.
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta delta [GHC.Base.const GHC.Base.id].
    reflexivity.
  - (* Nil/Bin *)
    unfold Data.IntMap.Internal.disjoint. rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta.
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta delta [GHC.Base.const GHC.Base.id].
    reflexivity.
  - (* Nil/Tip *)
    unfold Data.IntMap.Internal.disjoint. rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta.
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta delta [GHC.Base.const GHC.Base.id].
    reflexivity.
  - (* Nil/Nil *)
    unfold Data.IntMap.Internal.disjoint. rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta.
    unfold Data.IntMap.Internal.intersection, Data.IntMap.Internal.mergeWithKey'.
    rewrite IntMapProofs.deferredFix2_eq. cbv beta iota zeta delta [GHC.Base.const GHC.Base.id].
    reflexivity.
Qed.

(* Derive disjoint_spec from disjoint_null_intersection + null_member + member_intersection *)
Lemma disjoint_spec : forall A B (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
  Data.IntMap.Internal.disjoint m1 m2 = true <->
  (forall k, Data.IntMap.Internal.member k m1 = true -> Data.IntMap.Internal.member k m2 = false).
Proof.
  intros A B m1 m2.
  rewrite disjoint_null_intersection.
  rewrite (null_member _ _).
  split.
  - intros Hn k Hk.
    specialize (Hn k). rewrite member_intersection_local in Hn.
    destruct (Data.IntMap.Internal.member k m2) eqn:Hm2; [|reflexivity].
    rewrite Hk in Hn. simpl in Hn. discriminate.
  - intros Hdisj k. rewrite member_intersection_local.
    destruct (Data.IntMap.Internal.member k m1) eqn:Hm1; [|reflexivity].
    rewrite (Hdisj k Hm1). rewrite Bool.andb_false_r. reflexivity.
Qed.

(* ============================================================ *)
(* Eq_membership (restored from committed version)               *)
(* ============================================================ *)

Lemma Eq_membership : forall (A : Type) (HeqA : Eq_ A) (HlawsA : EqLaws A) (m1 m2 : IntMap.IntMap A),
  m1 == m2 ->
  forall k, Data.IntMap.Internal.member k m1 = Data.IntMap.Internal.member k m2.
Proof.
  intros A HeqA HlawsA.
  induction m1 as [p1 mask1 l1 IHl r1 IHr | kx vx | ]; destruct m2 as [p2 mask2 l2 r2 | ky vy | ];
    intros Heq k; simpl in Heq; try discriminate.
  - apply andb_true_iff in Heq. destruct Heq as [Hmask Hrest].
    apply andb_true_iff in Hrest. destruct Hrest as [Hprefix Hchildren].
    apply andb_true_iff in Hchildren. destruct Hchildren as [Heql Heqr].
    move: Hmask => /Eq_eq_Word Hmask. move: Hprefix => /Eq_eq_Word Hprefix.
    subst.
    unfold Data.IntMap.Internal.member. simpl.
    destruct (Data.IntMap.Internal.nomatch k p2 mask2); [reflexivity|].
    destruct (Data.IntSet.Internal.zero k mask2).
    + apply IHl. exact Heql.
    + apply IHr. exact Heqr.
  - apply andb_true_iff in Heq. destruct Heq as [Hkey Hval].
    move: Hkey => /Eq_eq_Word Hkey. subst.
    unfold Data.IntMap.Internal.member. simpl. reflexivity.
  - reflexivity.
Qed.

(* ============================================================ *)
(* Derived lookup/member lemmas                                  *)
(* ============================================================ *)

Lemma member_union :
   forall (A : Type)
     (key : Internal.Key)
     (i i0 : IntMap.IntMap A),
   (Data.IntMap.Internal.member key (Data.IntMap.Internal.union i i0)) =
   (Data.IntMap.Internal.member key i0 || Data.IntMap.Internal.member key i).
Proof.
  intros A key i i0.
  rewrite !member_isSome lookup_union_eq.
  destruct (Data.IntMap.Internal.lookup key i) eqn:Hi;
    destruct (Data.IntMap.Internal.lookup key i0) eqn:Hi0;
    simpl; reflexivity.
Qed.

Lemma lookup_union :
  forall (A:Type) key (val:A) (m1 m2: IntMap.IntMap A),
    (Data.IntMap.Internal.lookup key m1 = Some val \/ (Data.IntMap.Internal.lookup key m1 = None /\ Data.IntMap.Internal.lookup key m2 = Some val)) <->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.union m1 m2) = Some val.
Proof.
  intros A key val m1 m2.
  rewrite lookup_union_eq. split.
  - intros [H | [Hn H]].
    + rewrite H. reflexivity.
    + rewrite Hn. exact H.
  - intro H. destruct (Data.IntMap.Internal.lookup key m1) eqn:Hm1.
    + left. simpl in H. exact H.
    + right. simpl in H. split; [reflexivity | exact H].
Qed.

Lemma lookup_difference_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap.IntMap b) (y:b),
    Data.IntMap.Internal.lookup key i' = Some y ->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.difference i i') = None.
Proof.
  intros key b i i' y Hy.
  rewrite lookup_difference_eq Hy. reflexivity.
Qed.

Lemma lookup_difference_not_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap.IntMap b)(y:b),
    Data.IntMap.Internal.lookup key i' = None ->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.difference i i') = Data.IntMap.Internal.lookup key i.
Proof.
  intros key b i i' y Hn.
  rewrite lookup_difference_eq Hn. reflexivity.
Qed.

Lemma member_difference : forall A B k (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
    Data.IntMap.Internal.member k (Data.IntMap.Internal.difference m1 m2) =
    Data.IntMap.Internal.member k m1 && negb (Data.IntMap.Internal.member k m2).
Proof.
  intros A B k m1 m2.
  rewrite !member_isSome lookup_difference_eq.
  destruct (Data.IntMap.Internal.lookup k m2) eqn:Hm2;
    destruct (Data.IntMap.Internal.lookup k m1) eqn:Hm1;
    simpl; reflexivity.
Qed.

Lemma lookup_intersection :
  forall a b key (val1:a)
    (m1 : IntMap.IntMap a) (m2 : IntMap.IntMap b),
    Data.IntMap.Internal.lookup key m1 = Some val1 /\
    (exists (val2:b), Data.IntMap.Internal.lookup key m2 = Some val2) <->
    Data.IntMap.Internal.lookup key (Data.IntMap.Internal.intersection m1 m2) = Some val1.
Proof.
  intros a b key val1 m1 m2.
  rewrite lookup_intersection_eq. split.
  - intros [Hm1 [val2 Hm2]]. rewrite Hm2. exact Hm1.
  - intro H. destruct (Data.IntMap.Internal.lookup key m2) eqn:Hm2.
    + split; [exact H | exists b0; reflexivity].
    + discriminate.
Qed.

Lemma member_intersection : forall A B k (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
    Data.IntMap.Internal.member k (Data.IntMap.Internal.intersection m1 m2) =
    Data.IntMap.Internal.member k m1 && Data.IntMap.Internal.member k m2.
Proof.
  intros A B k m1 m2.
  rewrite !member_isSome lookup_intersection_eq.
  destruct (Data.IntMap.Internal.lookup k m2) eqn:Hm2;
    destruct (Data.IntMap.Internal.lookup k m1) eqn:Hm1;
    simpl; reflexivity.
Qed.

(* ============================================================ *)
(* Disjoint lemmas                                               *)
(* ============================================================ *)

Lemma disjoint_sym : forall A B (i : IntMap.IntMap A) (j : IntMap.IntMap B),
  Data.IntMap.Internal.disjoint i j = Data.IntMap.Internal.disjoint j i.
Proof.
  intros A B i j.
  apply bool_eq_of_iff. split.
  - intro H. apply (proj2 (disjoint_spec _ _ j i)). intros k Hk.
    destruct (Data.IntMap.Internal.member k i) eqn:Hi; [| reflexivity].
    pose proof (proj1 (disjoint_spec _ _ i j) H k Hi) as contra.
    rewrite Hk in contra. discriminate.
  - intro H. apply (proj2 (disjoint_spec _ _ i j)). intros k Hk.
    destruct (Data.IntMap.Internal.member k j) eqn:Hj; [| reflexivity].
    pose proof (proj1 (disjoint_spec _ _ j i) H k Hj) as contra.
    rewrite Hk in contra. discriminate.
Qed.

Lemma disjoint_insert : forall b k (v : b)(i1 i2 : IntMap.IntMap b),
  Data.IntMap.Internal.disjoint i1 (Data.IntMap.Internal.insert k v i2) =
  (negb (Data.IntMap.Internal.member k i1) && Data.IntMap.Internal.disjoint i1 i2).
Proof.
  intros b k v i1 i2.
  apply bool_eq_of_iff. split.
  - intro H.
    pose proof (proj1 (disjoint_spec _ _ i1 (Data.IntMap.Internal.insert k v i2)) H) as Hspec.
    clear H. apply andb_true_iff. split.
    + apply negb_true_iff.
      destruct (Data.IntMap.Internal.member k i1) eqn:Hk; [| reflexivity].
      exfalso. specialize (Hspec k Hk). rewrite member_insert Eq_refl_Word in Hspec. discriminate.
    + apply (proj2 (disjoint_spec _ _ i1 i2)). intros k' Hk'.
      specialize (Hspec k' Hk'). rewrite member_insert in Hspec.
      destruct (k' == k); simpl in Hspec; [discriminate | exact Hspec].
  - intro H. apply andb_true_iff in H. destruct H as [Hnk Hdisj].
    apply negb_true_iff in Hnk.
    pose proof (proj1 (disjoint_spec _ _ i1 i2) Hdisj) as Hspec. clear Hdisj.
    apply (proj2 (disjoint_spec _ _ i1 (Data.IntMap.Internal.insert k v i2))). intros k' Hk'.
    rewrite member_insert.
    destruct (N.eq_dec k' k) as [-> | Hneq].
    + rewrite Hnk in Hk'. discriminate.
    + change (k' == k) with ((k' =? k)%N).
      apply N.eqb_neq in Hneq. rewrite Hneq. simpl. exact (Hspec k' Hk').
Qed.

Lemma disjoint_non_member: forall b k (v : b)(i1 i2 : IntMap.IntMap b),
  Data.IntMap.Internal.disjoint i1 (Data.IntMap.Internal.insert k v i2) <->
  Data.IntMap.Internal.member k i1 = false /\
  Data.IntMap.Internal.disjoint i1 i2.
Proof.
  intros b k v i1 i2.
  rewrite disjoint_insert. split.
  - intro H. apply andb_true_iff in H. destruct H as [Hnk Hdisj].
    apply negb_true_iff in Hnk. auto.
  - intros [Hnk Hdisj]. apply andb_true_iff. split.
    + apply negb_true_iff. exact Hnk.
    + exact Hdisj.
Qed.

Lemma disjoint_eq : forall b (x1 x2 y1 y2 : IntMap.IntMap b),
  (forall a, Data.IntMap.Internal.member a x1 <-> Data.IntMap.Internal.member a y1) ->
  (forall a, Data.IntMap.Internal.member a x2 <-> Data.IntMap.Internal.member a y2) ->
  Data.IntMap.Internal.disjoint x1 x2 = Data.IntMap.Internal.disjoint y1 y2.
Proof.
  intros b x1 x2 y1 y2 H1 H2.
  apply bool_eq_of_iff. split.
  - intro H. apply (proj2 (disjoint_spec _ _ y1 y2)). intros k Hk.
    pose proof (proj1 (disjoint_spec _ _ x1 x2) H) as Hx.
    pose proof (bool_eq_of_iff _ _ (H1 k)) as E1.
    pose proof (bool_eq_of_iff _ _ (H2 k)) as E2.
    rewrite -E2. apply Hx. rewrite E1. exact Hk.
  - intro H. apply (proj2 (disjoint_spec _ _ x1 x2)). intros k Hk.
    pose proof (proj1 (disjoint_spec _ _ y1 y2) H) as Hy.
    pose proof (bool_eq_of_iff _ _ (H1 k)) as E1.
    pose proof (bool_eq_of_iff _ _ (H2 k)) as E2.
    rewrite E2. apply Hy. rewrite -E1. exact Hk.
Qed.

Lemma disjoint_difference: forall b (i1 i2 i3 : IntMap.IntMap b),
  Data.IntMap.Internal.disjoint i2 i3 = true ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.difference i1 i2) ->
  Data.IntMap.Internal.disjoint i1 i3 = true.
Proof.
  intros b i1 i2 i3 Hdisj Hnull.
  pose proof (proj1 (disjoint_spec _ _ i2 i3) Hdisj) as Hd. clear Hdisj.
  pose proof (proj1 (null_member _ _) Hnull) as Hn. clear Hnull.
  apply (proj2 (disjoint_spec _ _ i1 i3)). intros k Hk.
  specialize (Hn k). rewrite member_difference in Hn.
  rewrite Hk in Hn. simpl in Hn.
  apply negb_false_iff in Hn.
  exact (Hd k Hn).
Qed.

(* ============================================================ *)
(* Null-intersection lemmas                                      *)
(* ============================================================ *)

Lemma null_intersection_non_member: forall b k (v : b)(i1 i2 : IntMap.IntMap b),
  Data.IntMap.Internal.null
    (Data.IntMap.Internal.intersection i1 (Data.IntMap.Internal.insert k v i2)) <->
  Data.IntMap.Internal.member k i1 = false /\
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i1 i2).
Proof.
  intros b k v i1 i2. split.
  - intro H.
    pose proof (proj1 (null_member _ _) H) as Hn. clear H. split.
    + specialize (Hn k). rewrite member_intersection member_insert Eq_refl_Word in Hn.
      simpl in Hn. rewrite Bool.andb_true_r in Hn. exact Hn.
    + apply (proj2 (null_member _ _)). intros k'.
      specialize (Hn k'). rewrite !member_intersection member_insert in Hn.
      destruct (k' == k); simpl in Hn.
      * rewrite Bool.andb_true_r in Hn. rewrite member_intersection Hn. reflexivity.
      * rewrite member_intersection. exact Hn.
  - intros [Hnk Hnull].
    pose proof (proj1 (null_member _ _) Hnull) as Hn. clear Hnull.
    apply (proj2 (null_member _ _)). intros k'. rewrite member_intersection member_insert.
    destruct (N.eq_dec k' k) as [-> | Hneq].
    + rewrite Eq_refl_Word. simpl. rewrite Hnk. reflexivity.
    + change (k' == k) with ((k' =? k)%N).
      apply N.eqb_neq in Hneq. rewrite Hneq. simpl.
      specialize (Hn k'). rewrite member_intersection in Hn. exact Hn.
Qed.

Lemma null_intersection_difference: forall  b (i1 i2 i3 : IntMap.IntMap b),
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i2 i3) ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.difference i1 i2) ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection i1 i3).
Proof.
  intros b i1 i2 i3 Hint Hdiff.
  pose proof (proj1 (null_member _ _) Hint) as Hni. clear Hint.
  pose proof (proj1 (null_member _ _) Hdiff) as Hnd. clear Hdiff.
  apply (proj2 (null_member _ _)).
  intros k. rewrite member_intersection.
  specialize (Hnd k). rewrite member_difference in Hnd.
  specialize (Hni k). rewrite member_intersection in Hni.
  destruct (Data.IntMap.Internal.member k i1) eqn:H1;
    destruct (Data.IntMap.Internal.member k i2) eqn:H2;
    destruct (Data.IntMap.Internal.member k i3) eqn:H3;
    simpl in *; try reflexivity; discriminate.
Qed.

(* ============================================================ *)
(* IntMap tree structural predicates                             *)
(* ============================================================ *)

(* Key structural predicate: value appears somewhere in the tree *)
Fixpoint tree_elem_kv {a} (k : N) (v : a) (m : IntMap.IntMap a) : Prop :=
  match m with
  | Nil => False
  | Tip k' v' => k = k' /\ v = v'
  | Bin _ _ l r => tree_elem_kv k v l \/ tree_elem_kv k v r
  end.

(* Successful lookup always identifies a structural tree element, even
   when the tree is not well-formed. *)
Lemma lookup_tree_elem_kv : forall A k (v : A) m,
  Data.IntMap.Internal.lookup k m = Some v -> tree_elem_kv k v m.
Proof.
  intros A k v m.
  induction m as [p msk l IHl r IHr | k' v' | ]; simpl.
  - destruct (Data.IntSet.Internal.zero k msk).
    + intro H. left. exact (IHl H).
    + intro H. right. exact (IHr H).
  - destruct (k == k') eqn:Hk; [| discriminate].
    intro H. inversion H; subst.
    move: Hk => /Eq_eq_Word Hk.
    split; [exact Hk | reflexivity].
  - discriminate.
Qed.

(* tree_elem_kv k v m implies lookup k m = Some v (for WF maps) *)
Lemma tree_elem_kv_lookup :
  forall A k (v : A) (m : IntMap.IntMap A),
  tree_elem_kv k v m -> Data.IntMap.Internal.lookup k m = Some v.
Proof.
  intros A k v m.
  induction m as [p msk l IHl r IHr | k' v' | ]; intro H.
  - simpl in H. destruct H as [Hl | Hr].
    + apply IHl in Hl.
      rewrite (lookup_Bin_oro p msk l r k (IntMapProofs.All_IntMaps_WF _ _)).
      rewrite Hl. reflexivity.
    + apply IHr in Hr.
      rewrite (lookup_Bin_oro p msk l r k (IntMapProofs.All_IntMaps_WF _ _)).
      destruct (WF_Bin_lookup_disjoint p msk l r k (IntMapProofs.All_IntMaps_WF _ _)) as [Hlnone | Hrnone].
      * rewrite Hlnone. simpl. exact Hr.
      * rewrite Hrnone in Hr. discriminate.
  - simpl in H. destruct H as [Hk Hv]; subst.
    simpl. rewrite Eq_refl_Word. reflexivity.
  - simpl in H. contradiction.
Qed.

(* ============================================================ *)

Lemma null_intersection_eq : forall b (x1 x2 y1 y2 : IntMap.IntMap b),
  (forall a, Data.IntMap.Internal.member a x1 <-> Data.IntMap.Internal.member a y1) ->
  (forall a, Data.IntMap.Internal.member a x2 <-> Data.IntMap.Internal.member a y2) ->
  Data.IntMap.Internal.null (Data.IntMap.Internal.intersection x1 x2) = Data.IntMap.Internal.null (Data.IntMap.Internal.intersection y1 y2).
Proof.
  intros b x1 x2 y1 y2 H1 H2.
  apply bool_eq_of_iff. split.
  - intro H. pose proof (proj1 (null_member _ _) H) as Hn. clear H.
    apply (proj2 (null_member _ _)). intros k.
    specialize (Hn k). rewrite member_intersection in Hn.
    rewrite member_intersection.
    pose proof (bool_eq_of_iff _ _ (H1 k)) as E1.
    pose proof (bool_eq_of_iff _ _ (H2 k)) as E2.
    rewrite E1 E2 in Hn. exact Hn.
  - intro H. pose proof (proj1 (null_member _ _) H) as Hn. clear H.
    apply (proj2 (null_member _ _)). intros k.
    specialize (Hn k). rewrite member_intersection in Hn.
    rewrite member_intersection.
    pose proof (bool_eq_of_iff _ _ (H1 k)) as E1.
    pose proof (bool_eq_of_iff _ _ (H2 k)) as E2.
    rewrite -E1 -E2 in Hn. exact Hn.
Qed.
