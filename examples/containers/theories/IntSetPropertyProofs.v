(******************************************************************************)
(** Imports **)

(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

(* SSReflect *)
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype.
Set Bullet Behavior "Strict Subproofs".

(* Sortedness *)
Require Import Coq.Sorting.Sorted.

(* Arithmetic *)
From Coq Require Import NArith Lia.

(* Basic Haskell libraries *)
Require Import GHC.Base      Proofs.GHC.Base.
Require Import GHC.List      Proofs.GHC.List.
Require Import GHC.Enum      Proofs.GHC.Enum.
Require Import Data.Foldable Proofs.Data.Foldable.
Require Import Data.OldList  Proofs.Data.OldList.
Require Import Data.Bits     Proofs.Data.Bits.Popcount.

(* Quickcheck *)
Require Import Test.QuickCheck.Property.


(* IntSet library *)
Require Import Data.IntSet.Internal.

(* IntSet proofs *)
Require Import IntSetProperties.
Require Import DyadicIntervals.
Require Import IntSetProofs.

(* Bit manipulation *)
Require Import BitUtils.

(* Working with Haskell *)
Require Import OrdTactic.
Require Import HSUtil IntSetUtil SortedUtil.

(******************************************************************************)
(** Name dismabiguation -- copied from HSUtil **)

Notation list    := Coq.Init.Datatypes.list.
Notation seq     := Coq.Lists.List.seq.
Notation reflect := ssrbool.reflect.

(******************************************************************************)
(** Theorems **)
(** The quoted comments and the section headers are taken directly from
    `intset-properties.hs`. **)

(********************************************************************
  Valid IntMaps
********************************************************************)

Theorem thm_Valid : toProp prop_Valid.
Proof.
  rewrite /prop_Valid /forValidUnitTree /forValid /=; apply valid_correct.
Qed.

(********************************************************************
  Construction validity
********************************************************************)

Theorem thm_EmptyValid : toProp prop_EmptyValid.
Proof. done. Qed.

Theorem thm_SingletonValid : toProp prop_SingletonValid.
Proof.
  rewrite /prop_SingletonValid /= => x POS_x.
  by apply valid_correct, singleton_WF.
Qed.

Theorem thm_InsertIntoEmptyValid : toProp prop_InsertIntoEmptyValid.
Proof.
  rewrite /prop_InsertIntoEmptyValid /= => x POS.
  by apply valid_correct, insert_WF.
Qed.

(********************************************************************
  Single, Member, Insert, Delete, Member, FromList
********************************************************************)

Theorem thm_Single : toProp prop_Single.
Proof. by rewrite /prop_Single /= => x POS_x; apply/Eq_eq. Qed.

Theorem thm_Member : toProp prop_Member.
Proof.
  rewrite /prop_Member /= => xs POS_xs n POS_n.
  rewrite !Foldable_all_ssreflect; apply/allP => /= k.
  by rewrite fromList_member // Eq_refl.
Qed.

Theorem thm_NotMember : toProp prop_NotMember.
Proof.
  rewrite /prop_NotMember /= => xs POS_xs n POS_n.
  rewrite !Foldable_all_ssreflect; apply/allP => /= k.
  by rewrite /notMember /notElem /= fromList_member // Eq_refl.
Qed.

(* SKIPPED: test_LookupSomething, prop_LookupLT, prop_LookupGT, prop_LookupLE, prop_LookupGE *)

Theorem thm_InsertDelete : toProp prop_InsertDelete.
Proof.
  rewrite /prop_InsertDelete /= => x POS s WF_s.

  move: (insert_WF x _ WF_s  ) => WF_ins.
  move: (delete_WF x _ WF_ins) => WF_res.
  case x_nin_s: (~~ member x s) => //=; split=> /=; first by apply valid_correct.

  apply/eqIntSetMemberP => // k.
  rewrite delete_member // insert_member //.
  rewrite Eq_inv andb_orr andbN orFb.
  
  case: (EqExact_cases k x) => [[Beq Peq] | [Bneq Pneq]].
  - by rewrite Peq; move: x_nin_s => /negbTE->; rewrite andbF.
  - by rewrite Bneq andTb.
Qed.

(* Cheating: manually forgetting POS constraint *)
Theorem thm_MemberFromList : toProp prop_MemberFromList.
Proof.
  rewrite /prop_MemberFromList /= => xs _.
  unfold GHC.Prim.rightSection.
  set abs_xs := flat_map _ xs.
  apply/andP; split.
  all: rewrite Foldable_all_ssreflect; apply/allP => /= k; rewrite in_elem.
  - rewrite fromList_member //.
  - rewrite /GHC.Base.op_z2218U__ /= /notMember /notElem /= fromList_member //.
    + move=> k_abs; have k_pos: (0 <= k)%N. {
        Nomega.
      }
      clear k_abs; subst abs_xs; elim: xs => [|x xs IH] //=.
      rewrite elem_app negb_orb IH andbT.
      by case: k k_pos {IH}; case: x.
Qed.      

(********************************************************************
  Union, Difference and Intersection
********************************************************************)

Theorem thm_UnionInsert : toProp prop_UnionInsert.
Proof.
  rewrite /prop_UnionInsert /= => x POS_x s WF_s.

  move: (singleton_WF x)                => WF_sing.
  move: (union_WF     _ _ WF_s WF_sing) => WF_union.
  move: (insert_WF    x _ WF_s)         => WF_ins.

  split=> /=; first by apply valid_correct.
  
  apply/eqIntSetMemberP => // k.
  by rewrite union_member // singleton_member // insert_member // orbC.
Qed.

Theorem thm_UnionAssoc : toProp prop_UnionAssoc.
Proof.
  rewrite /prop_UnionAssoc /= => s1 WF1 s2 WF2 s3 WF3.
  
  move: (union_WF _ _ WF1  WF2)  => WF12.
  move: (union_WF _ _ WF2  WF3)  => WF23.
  move: (union_WF _ _ WF12 WF3)  => WF123.
  move: (union_WF _ _ WF1  WF23) => WF123'.
  
  apply/eqIntSetMemberP => // k.
  by rewrite !union_member // orbA.
Qed.

Theorem thm_UnionComm : toProp prop_UnionComm.
Proof.
Proof.
  rewrite /prop_UnionComm /= => s1 WF1 s2 WF2.
  
  move: (union_WF _ _ WF1 WF2) => WF12.
  move: (union_WF _ _ WF2 WF1) => WF21.
  
  apply/eqIntSetMemberP => // k.
  by rewrite !union_member // orbC.
Qed.

Theorem thm_Diff : toProp prop_Diff.
Proof.
  rewrite /prop_Diff /= => xs POS_xs ys POS_ys.
  
  move: (fromList_WF   xs)              => WF_xs.
  move: (fromList_WF   ys)              => WF_ys.
  move: (difference_WF _ _ WF_xs WF_ys) => WF_diff.
  
  split=> /=; first by apply valid_correct.
  apply/Eq_eq/StronglySorted_Ord_eq_In.
  - by apply toList_sorted.
  - apply StronglySorted_NoDup_Ord; first apply sort_StronglySorted.
    rewrite -sort_NoDup.
    apply diff_preserves_NoDup, nub_NoDup.
  - move=> a.
    rewrite !(rwP (elemP _ _)).
    rewrite sort_elem.
    rewrite diff_NoDup_elem; last apply nub_NoDup.
    rewrite !nub_elem.
    rewrite toAscList_member // difference_member // !fromList_member //.
Qed.

Theorem thm_Int : toProp prop_Int.
Proof.
  rewrite /prop_Int /= => xs _ ys _.

  move: (fromList_WF     xs)              => WF_xs.
  move: (fromList_WF     ys)              => WF_ys.
  move: (intersection_WF _ _ WF_xs WF_ys) => WF_both.

  split=> /=; first by apply valid_correct.
  apply/Eq_eq; fold toList.
  apply StronglySorted_Nlt_eq_In;
    [by apply to_List_sorted | apply StronglySorted_sort_nub_Nlt | ].
  move=> a.
  by rewrite !(rwP (elemP _ _))
             toList_member // intersection_member // !fromList_member //
             sort_elem nub_elem intersect_elem.
Qed.

Theorem thm_disjoint : toProp prop_disjoint.
Proof.
  rewrite /prop_disjoint /= => s1 WF1 s2 WF2.
  
  move: (intersection_WF _ _ WF1 WF2) => WF12.
  
  apply/Eq_eq/bool_eq_iff.
  rewrite disjoint_member // null_member //.
  split=> [is_disjoint | is_not_intersection] k.
  - rewrite intersection_member //; apply negbTE.
    apply is_disjoint.
  - move: (is_not_intersection k).
    rewrite intersection_member // => /negbT.
    by rewrite negb_andb.
Qed.

(********************************************************************
  Lists
********************************************************************)

(* SKIPPED: prop_Ordered *)

Theorem thm_List : toProp prop_List.
Proof.
  rewrite /prop_List /=; rewrite -/toList => xs POS_xs.
Proof.
  have WF_xs: WF (fromList xs) by apply fromList_WF.
  apply/Eq_eq/StronglySorted_Ord_eq_In.
  - apply StronglySorted_sort_nub.
  - apply toList_sorted, fromList_WF=> //.
  - move=> a.
    by rewrite !(rwP (elemP _ _))
               toList_member // fromList_member //
               sort_elem nub_elem.
Qed.

Theorem thm_DescList : toProp prop_DescList.
Proof.
  rewrite /prop_DescList /= => xs POS_xs.
  replace (toDescList (fromList xs)) with (reverse (toAscList (fromList xs)))
    by by rewrite !hs_coq_reverse_rev toDescList_spec //; apply fromList_WF.
  apply/Eq_eq; f_equal; apply/Eq_eq.
  by apply thm_List.
Qed.

Theorem thm_AscDescList : toProp prop_AscDescList.
Proof.
  rewrite /prop_AscDescList /= => xs POS_xs.
  rewrite /toAscList toDescList_spec; last by apply fromList_WF.
  by rewrite hs_coq_reverse_rev rev_involutive Eq_refl.
Qed.

(* SKIPPED: prop_fromList *)

(********************************************************************
  Bin invariants
********************************************************************)

(** *** Counterexample: thm_MaskPow2 is FALSE in the Coq model *)

(* The Coq model uses unbounded N (not 64-bit Word), so we can construct
   a WF IntSet whose Bin mask is 2^100 -- outside [2^0..2^63].
   We build: Bin 0 (2^100) (Tip 0 1) (Tip (2^100) 1). *)

Definition r_left_mp2 : range := (0%N, 6%N).
Definition r_right_mp2 : range := (2^94, 6)%N.
Definition r_top_mp2 : range := (0%N, 101%N).

Definition f_left_mp2 : N -> bool := bitmapInRange r_left_mp2 1.
Definition f_right_mp2 : N -> bool := bitmapInRange r_right_mp2 1.
Definition f_big_mp2 : N -> bool := fun i => f_left_mp2 i || f_right_mp2 i.

Definition big_set_mp2 : IntSet :=
  Bin 0%N (2^100)%N (Tip 0%N 1%N) (Tip (2^100)%N 1%N).

Lemma isBitMask_1_mp2 : isBitMask 1.
Proof. unfold isBitMask, WIDTH. lia. Qed.

Lemma Desc_left_mp2 : Desc (Tip 0%N 1%N) r_left_mp2 f_left_mp2.
Proof.
  apply DescTip.
  - reflexivity.
  - reflexivity.
  - intro i. reflexivity.
  - exact isBitMask_1_mp2.
Qed.

Lemma Desc_right_mp2 : Desc (Tip (2^100)%N 1%N) r_right_mp2 f_right_mp2.
Proof.
  apply DescTip.
  - unfold r_right_mp2. simpl. reflexivity.
  - reflexivity.
  - intro i. reflexivity.
  - exact isBitMask_1_mp2.
Qed.

Lemma isSubrange_left_mp2 : isSubrange r_left_mp2 (halfRange r_top_mp2 false) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma isSubrange_right_mp2 : isSubrange r_right_mp2 (halfRange r_top_mp2 true) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma Desc_big_mp2 : Desc big_set_mp2 r_top_mp2 f_big_mp2.
Proof.
  unfold big_set_mp2.
  eapply DescBin.
  - exact Desc_left_mp2.
  - exact Desc_right_mp2.
  - unfold r_top_mp2; simpl; lia.
  - exact isSubrange_left_mp2.
  - exact isSubrange_right_mp2.
  - reflexivity.
  - reflexivity.
  - intro i. reflexivity.
Qed.

Lemma WF_big_set_mp2 : WF big_set_mp2.
Proof.
  exists f_big_mp2. apply (DescSem _ r_top_mp2). exact Desc_big_mp2.
Qed.

Lemma pow2_100_not_in_powers :
  ~ In (2^100)%N
    (Coq.Lists.List.map (fun i : N => (2^i)%N)
       (GHC.Enum.enumFromTo 0%N 63%N)).
Proof.
  intro HIn.
  apply Coq.Lists.List.in_map_iff in HIn.
  destruct HIn as [x [Hpow Hin]].
  assert (Hx : x = 100%N) by (apply N.pow_inj_r with (a := 2%N); lia).
  subst x.
  revert Hin.
  vm_compute.
  intuition congruence.
Qed.

Lemma member_pow2_100_powersOf2_false : member (2^100)%N powersOf2 = false.
Proof.
  unfold powersOf2.
  rewrite fromList_member.
  apply negbTE. apply/negP. move/elemP.
  rewrite flat_map_cons_f.
  exact pow2_100_not_in_powers.
Qed.

Lemma prop_MaskPow2_big_set_false : prop_MaskPow2 big_set_mp2 = false.
Proof.
  unfold big_set_mp2.
  change (prop_MaskPow2 (Bin 0%N (2^100)%N (Tip 0%N 1%N) (Tip (2^100)%N 1%N)))
    with (member (2^100)%N powersOf2 && (prop_MaskPow2 (Tip 0%N 1%N) && prop_MaskPow2 (Tip (2^100)%N 1%N))).
  rewrite member_pow2_100_powersOf2_false. reflexivity.
Qed.

Theorem thm_MaskPow2_false : ~ (toProp prop_MaskPow2).
Proof.
  intro H.
  have := H big_set_mp2 WF_big_set_mp2.
  rewrite prop_MaskPow2_big_set_false.
  done.
Qed.

(** *** thm_MaskPow2: disproved above *)

(* "Check the invariant that the mask is a power of 2." *)
(* FALSE: disproved by thm_MaskPow2_false above.
   The Coq model uses unbounded N (not 64-bit Word), so a WF IntSet can have
   Bin masks > 2^63 (e.g., big_set_mp2 has keys {0, 2^100} and mask 2^100).
   powersOf2 only contains [2^0..2^63], so the check fails.
   Aborted to prevent unsound use. *)
Theorem thm_MaskPow2 : toProp prop_MaskPow2.
Proof.
Abort.

(* The original thm_MaskPow2 is false for unbounded N (see thm_MaskPow2_false).
   In Haskell, Word is 64-bit, so all keys satisfy k < 2^64 and all masks
   satisfy mask < 2^64. Under this constraint, the property holds.

   However, the Coq model's enumFromTo for N is off-by-one:
   enumFromTo 0 63 = map N.of_nat (seq 0 63) = [0..62], so powersOf2
   only contains 2^0 through 2^62 (not 2^63). Therefore the bound must
   be k < 2^63 (not 2^64) to ensure all masks are in powersOf2.
   A set with keys {0, 2^63} is WF and bounded by 2^64, but its mask
   2^63 is not in powersOf2, disproving the 2^64 version. *)

(* Auxiliary: for n <= 62, 2^n is in powersOf2.
   Proved by exhaustive case analysis on the 63 possible values of n. *)
Lemma member_powersOf2_le62 : forall n : N, (n <= 62)%N -> member (2^n)%N powersOf2 = true.
Proof.
  intro n.
  destruct n as [|p]; intro Hn.
  - vm_compute. reflexivity.
  - destruct p as [p|p|]; [ | | vm_compute; reflexivity].
    all: destruct p as [p|p|]; try (vm_compute; reflexivity).
    all: destruct p as [p|p|]; try (vm_compute; reflexivity).
    all: destruct p as [p|p|]; try (vm_compute; reflexivity).
    all: destruct p as [p|p|]; try (vm_compute; reflexivity).
    all: destruct p as [p|p|]; try (vm_compute; reflexivity).
    all: exfalso; lia.
Qed.

Definition bounded_WF (s : IntSet) :=
  WF s /\ forall k, member k s = true -> (k < 2^63)%N.

Theorem thm_MaskPow2_bounded : forall s, bounded_WF s -> prop_MaskPow2 s = true.
Proof.
  elim => [p m l IHl r IHr | p bm | ] [HWF Hbound] //=.
  (* Bin case: need member msk powersOf2 && prop_MaskPow2 l && prop_MaskPow2 r *)
  move: (HWF) => [f SEMf].
  inversion SEMf as [|s' r_top f' DESCf]; subst s' f'.
  inversion DESCf as [|l' rl fl r' rr fr p' m' r_top' f'
                        DESCl DESCr Hpos Hsubl Hsubr Hp Hm Hf];
    subst p' m' l' r' r_top' f' p m.
  apply/and3P; split.
  + (* member (rMask r_top) powersOf2 *)
    (* rMask (p,b) = 2^(b-1), so rewrite *)
    replace (rMask r_top) with (2^(rBits r_top - 1))%N
      by (destruct r_top; reflexivity).
    apply member_powersOf2_le62.
    (* Show rBits r_top - 1 <= 62 *)
    (* Get a key from the right child to bound rBits *)
    destruct (Desc_some_f DESCr) as [i2 Hi2].
    pose proof (Desc_inside DESCr Hi2) as Hirr.
    pose proof (inRange_isSubrange_true _ _ _ Hsubr Hirr) as Hihr.
    apply inRange_bounded in Hihr.
    rewrite rBits_halfRange in Hihr.
    assert (Hfi2 : f i2 = true).
    { rewrite Hf. rewrite Hi2. apply orbT. }
    specialize (Hbound i2).
    rewrite (member_Sem SEMf) in Hbound.
    specialize (Hbound Hfi2).
    pose proof (rPrefix_halfRange_otherhalf r_top Hpos) as Hpref.
    rewrite rBits_halfRange in Hpref.
    (* 2^(rBits r_top - 1) <= rPrefix(halfRange r_top true) <= i2 < 2^63 *)
    assert (Hpow : (2^(rBits r_top - 1) < 2^63)%N).
    { rewrite Hpref in Hihr. lia. }
    apply N.pow_lt_mono_r_iff in Hpow; lia.
  + (* IH for left child *)
    apply IHl. split.
    * eapply WF_Bin_left; exact HWF.
    * intros k Hk. apply Hbound.
      erewrite member_Sem in Hk; last by (eapply DescSem; exact DESCl).
      erewrite member_Sem; last by exact SEMf.
      rewrite Hf. rewrite Hk. apply orTb.
  + (* IH for right child *)
    apply IHr. split.
    * eapply WF_Bin_right; exact HWF.
    * intros k Hk. apply Hbound.
      erewrite member_Sem in Hk; last by (eapply DescSem; exact DESCr).
      erewrite member_Sem; last by exact SEMf.
      rewrite Hf. rewrite Hk. rewrite orbT. reflexivity.
Qed.

(* "Check that the prefix satisfies its invariant." *)
Theorem thm_Prefix : toProp prop_Prefix.
Proof.
  elim => [p m | p bm | ] //.
  rewrite /prop_Prefix -/prop_Prefix /toList (lock toAscList) /= => l IHl r IHr WFs;
    move: (WFs) => /WF_Bin_children [WFl WFr].
  move: (WFs) => [fs SEMs];
    inversion SEMs as [|s' [ps ms] fs' DESCs]; subst s' fs';
    inversion DESCs as [|l' rng_l fl r' rng_r fr p' m' rng_s' fs'
                         DESCl DESCr POSrng subrange_l subrange_r def_p def_m def_fs];
    subst p' m' l' r' rng_s' fs' p m.
  apply/and3P; split; try by (apply IHl || apply IHr).
  
  rewrite !Foldable_all_ssreflect. apply/allP => x MEM_x.
  rewrite match_nomatch.
  rewrite nomatch_spec.
  move: MEM_x.
  rewrite -(lock toAscList) in_elem toAscList_member // (member_Sem SEMs) => MEM_x.
  rewrite negb_involutive.
  rewrite def_fs in MEM_x. apply orb_true_iff in MEM_x. destruct MEM_x.
  eapply inRange_isSubrange_true; only 2: eapply (Desc_inside DESCl); only 1: isSubrange_true; assumption.
  eapply inRange_isSubrange_true; only 2: eapply (Desc_inside DESCr); only 1: isSubrange_true; assumption.
  assumption.
Qed.  

(* "Check that the left elements don't have the mask bit set, and the right ones
   do." *)
Theorem thm_LeftRight : toProp prop_LeftRight.
Proof.
  rewrite /prop_LeftRight /= => -[p m l r | // | // ] WFs; move: (WFs) => /WF_Bin_children [WFl WFr].
  move: (WFs) => /valid_maskRespected /=.
  move => /andP [mask_l mask_r]. move: mask_r.
  move => /andP [mask_r _]. move: mask_l mask_r.
  rewrite !Foldable_and_all !Foldable_all_ssreflect !flat_map_cons_f /zero /elems /toList.
  move=> /allP /= mask_l /allP /= mask_r.
  apply/andP; split; apply/allP => /= b /mapP [] /= x x_in {b}->; apply/Eq_eq.
  - by move: (mask_l _ x_in) => /N.eqb_spec ->.
  - move: (mask_r _ x_in) => /N.eqb_spec.
    case: (WF_Bin_mask_power_N WFs) => [i ?]; subst m.
    rewrite -N.shiftl_1_l => NEQ_bits.
    apply N.bits_inj_iff => ix.
    rewrite N.shiftl_1_l N.land_spec N.pow2_bits_eqb.
    rewrite -> N.shiftl_1_l in NEQ_bits.
    case: (N.eqb_spec i ix) => [? | NEQ]; first subst.
    + rewrite andb_true_r.
      rewrite <- N_land_pow2_testbit.
      rewrite negb_true_iff.
      rewrite N.eqb_neq.
      rewrite N.land_comm.
      assumption.
    + apply andb_false_r.
Qed.

(********************************************************************
  IntSet operations are like Set operations
********************************************************************)

(* Import SetProofs with depth limit to prevent typeclass loop *)
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 3.
Require SetProofs.
Unset Typeclasses Iterative Deepening.

(* Bridge: List.elem for N is equivalent to Coq's In *)
Lemma List_elem_In : forall (k : N) (xs : Coq.Init.Datatypes.list N),
  GHC.List.elem k xs = true <-> List.In k xs.
Proof.
  intros k xs. induction xs as [|x xs' IH].
  - simpl. split; intro H; inversion H.
  - simpl. rewrite orb_true_iff. split.
    + intros [Heq | Hin].
      * left. symmetry. apply (reflect_iff _ _ (Eq_eq k x)). exact Heq.
      * right. apply IH. exact Hin.
    + intros [Heq | Hin].
      * left. apply (reflect_iff _ _ (Eq_eq k x)). symmetry. exact Heq.
      * right. apply IH. exact Hin.
Qed.

(* Bridge: toSet produces a Bounded Set with sem matching IntSet.member *)
Lemma toSet_Bounded_sem : forall (s : IntSet),
  WF s ->
  exists s', s' = toSet s /\
    SetProofs.Bounded s' None None /\
    (forall k, SetProofs.sem s' k = Data.IntSet.Internal.member k s).
Proof.
  intros s [f Hsem].
  unfold toSet, op_z2218U__.
  pose proof (SetProofs.fromList_Desc (Data.IntSet.Internal.toList s)) as Hdesc.
  unfold SetProofs.Desc' in Hdesc.
  apply Hdesc. clear Hdesc.
  intros s' Hbounded _ Hsem_eq.
  exists s'. split; [reflexivity|]. split; [exact Hbounded|].
  intros k. rewrite Hsem_eq.
  apply Bool.eq_iff_eq_true.
  pose proof (IntSetProofs.member_Sem Hsem (i := k)) as Hmem.
  pose proof (IntSetProofs.toList_In _ _ Hsem k) as Hin.
  split; intro H.
  - apply List_elem_In in H. apply Hin in H. rewrite Hmem. exact H.
  - rewrite Hmem in H. apply Hin in H. apply List_elem_In. exact H.
Qed.

(* "Check that IntSet.isProperSubsetOf is the same as Set.isProperSubsetOf." *)
Theorem thm_isProperSubsetOf : toProp prop_isProperSubsetOf.
Proof.
  rewrite /prop_isProperSubsetOf /= => s1 WF1 s2 WF2.
  (* Needs size reasoning for proper subset — bridge infrastructure
     is available but the size< direction requires toSet_size +
     NoDup_incl_length reasoning. *)
  admit.
Admitted.

(* "In the above test, isProperSubsetOf almost always returns False (since a
   random set is almost never a subset of another random set).  So this second
   test checks the True case." *)
Theorem thm_isProperSubsetOf2 : toProp prop_isProperSubsetOf2.
Proof.
  rewrite /prop_isProperSubsetOf2 /= => s1 WF1 s2 WF2.
  move: (union_WF _ _ WF1 WF2) => WF12.
  apply/Eq_eq/bool_eq_iff.

  rewrite isProperSubsetOf_member //; split; first by intuition.
  move=> s1_diff; split=> // k k_in_s1.
  by rewrite union_member // k_in_s1 orTb.
Qed.

Theorem thm_isSubsetOf : toProp prop_isSubsetOf.
Proof.
  rewrite /prop_isSubsetOf /= => s1 WF1 s2 WF2.
  apply/Eq_eq.
  apply Bool.eq_iff_eq_true.
  destruct (toSet_Bounded_sem s1 WF1) as [ts1 [Ets1 [Hb1 Hsem1]]].
  destruct (toSet_Bounded_sem s2 WF2) as [ts2 [Ets2 [Hb2 Hsem2]]].
  subst ts1 ts2.
  split; intro H.
  - apply (proj2 (SetProofs.isSubsetOf_spec _ _ _ _ Hb1 Hb2)).
    assert (Hmem : forall k, Data.IntSet.Internal.member k s1 = true ->
                             Data.IntSet.Internal.member k s2 = true).
    { apply (proj1 (isSubsetOf_member s1 s2 WF1 WF2)). exact H. }
    intros i Hi. rewrite Hsem2. apply Hmem. rewrite <- Hsem1. exact Hi.
  - apply (proj2 (isSubsetOf_member s1 s2 WF1 WF2)).
    assert (Hsem_sub : forall i, SetProofs.sem (toSet s1) i = true ->
                                 SetProofs.sem (toSet s2) i = true).
    { apply (proj1 (SetProofs.isSubsetOf_spec _ _ _ _ Hb1 Hb2)). exact H. }
    intros k Hk. rewrite <- Hsem2. apply Hsem_sub. rewrite Hsem1. exact Hk.
Qed.

Theorem thm_isSubsetOf2 : toProp prop_isSubsetOf2.
Proof.
  rewrite /prop_isSubsetOf2 /= => s1 WF1 s2 WF2.
  move: (union_WF _ _ WF1 WF2) => WF12.
  rewrite isSubsetOf_member // => k.
  by rewrite union_member // => ->; rewrite orTb.
Qed.

Theorem thm_size : toProp prop_size.
Proof.
  rewrite /prop_size /= => s WF_s.
  rewrite size_spec //.
  split=> /=.
  - change @foldl' with @foldl; rewrite foldl_spec //.
    apply/Eq_eq.
    generalize (toList s). intro xs.
    rewrite <- fold_left_S_O.
    replace (0%N) with (N.of_nat 0) by reflexivity.
    generalize 0.
    induction xs.
    * reflexivity.
    * intros. rewrite IHxs. cbn - [N.of_nat].
      f_equal.
      rewrite Nat2N.inj_succ.
      Nomega.
  - apply Eq_refl.
Qed.

(* SKIPPED: prop_findMax, prop_findMin *)

Theorem thm_ord : toProp prop_ord.
Proof.
  rewrite /prop_ord /= => s1 WF1 s2 WF2.
  apply Eq_refl.
Qed.

(* SKIPPED: prop_readShow *)

Theorem thm_foldR : toProp prop_foldR.
Proof.
  rewrite /prop_foldR /= => s WF_s.
  by rewrite Eq_refl.
Qed.

Theorem thm_foldR' : toProp prop_foldR'.
Proof.
  rewrite /prop_foldR' /= => s WF_s.
  by rewrite Eq_refl.
Qed.

Theorem thm_foldL : toProp prop_foldL.
Proof.
  rewrite /prop_foldL /= => s WF_s.
  by rewrite foldl_spec // -hs_coq_foldl_base Eq_refl.
Qed.

Theorem thm_foldL' : toProp prop_foldL'.
Proof.
  rewrite /prop_foldL' /=; change @foldl' with @foldl; apply thm_foldL.
Qed.

Theorem thm_map : toProp prop_map.
Proof.
  rewrite /prop_map /map /= => s WF_s.
  rewrite map_id.
  apply/eqIntSetMemberP=> //; first by apply fromList_WF.
  move=> k.
  by rewrite fromList_member // toList_member // Eq_refl.
Qed.

(* SKIPPED: prop_maxView, prop_minView *)

Theorem thm_split : toProp prop_split.
Proof.
  rewrite /prop_split /= => s WF_ss x POS_x.
  rewrite split_filter //.
  
  have WF_lt:  WF (filter (fun y => y < x) s) by apply filter_WF.
  have WF_gt:  WF (filter (fun y => y > x) s) by apply filter_WF.
  have WF_del: WF (delete x s)                by apply delete_WF.
  move: (union_WF _ _ WF_lt WF_gt) => WF_union.

  rewrite !Foldable_all_ssreflect.
  repeat split=> /=; try by apply valid_correct.
  - apply/allP=> /= k.
    by rewrite in_elem toList_member // filter_member // => /andP [].
  - apply/allP=> /= k.
    by rewrite in_elem toList_member // filter_member // => /andP [].
  - apply/eqIntSetMemberP => // k.
    rewrite delete_member // union_member // !filter_member //.
    rewrite -andb_orr andbC; f_equal.
    apply Ord_lt_gt_antisym.
Qed.

Theorem thm_splitMember : toProp prop_splitMember.
Proof.
  rewrite /prop_splitMember /= => s WF_ss x POS_x.
  rewrite splitMember_filter //.
  
  have WF_lt:  WF (filter (fun y => y < x) s) by apply filter_WF.
  have WF_gt:  WF (filter (fun y => y > x) s) by apply filter_WF.
  have WF_del: WF (delete x s)                by apply delete_WF.
  move: (union_WF _ _ WF_lt WF_gt) => WF_union.

  rewrite !Foldable_all_ssreflect.
  repeat split=> //=; try by apply valid_correct.
  - apply/allP=> /= k.
    by rewrite in_elem toList_member // filter_member // => /andP [].
  - apply/allP=> /= k.
    by rewrite in_elem toList_member // filter_member // => /andP [].
  - by apply Eq_refl.
  - apply/eqIntSetMemberP => // k.
    rewrite delete_member // union_member // !filter_member //.
    rewrite -andb_orr andbC; f_equal.
    apply Ord_lt_gt_antisym.
Qed.

Theorem thm_splitRoot : toProp prop_splitRoot.
Proof.
  rewrite /prop_splitRoot /= => -[p m l r | p m | ] WFs //=.
  - move: (WFs) => /WF_Bin_children [WFl WFr].
    have WFlr: WF (union l r) by apply union_WF.
    have WFrl: WF (union r l) by apply union_WF.
    
    have: (m > 0%N). {
      move: (WFs) => [fs SEMs];
        inversion SEMs as [|s' [ps ms] fs' DESCs];
        subst s' fs';
        inversion DESCs as [|l' rng_l fl r' rng_r fr p' m' rng_s' fs'
                             DESCl DESCr POSrng subrange_l subrange_r def_p def_m def_fs];
        subst p' m' l' r' rng_s' fs' p m.
      unfold ">", Ord_Char___ => /=.
      apply/N.ltb_spec0.
       apply N_pow_pos_nonneg => //.
    }
    move=> /(Ord_gt_not_lt _ _)/negbTE ->.
    
    rewrite /unions !hs_coq_foldl'_list /= !(union_eq empty) /=.
    apply/andP; split.
    + apply null_list_none => -[x y] /in_flat_map [kl [/elemP IN_kl /in_flat_map [kr [/elemP IN_kr IN_xy]]]].
      move: IN_kl IN_kr; rewrite !toList_member // => IN_kl IN_kr.
      move: (Bin_left_lt_right WFs _ IN_kl _ IN_kr) IN_xy.
      by move=> /(Ord_lt_not_gt _ _)/negbTE ->.
    + by apply/eqIntSetMemberP => // k; rewrite Bin_member // union_member //.
  - apply/andP; split; by [elim: (foldrBits _ _ _ _) | apply/Eq_eq].
Qed.

Theorem thm_partition : toProp prop_partition.
Proof.
  rewrite /prop_partition /= => s WF_s _ _.
  rewrite partition_filter //.
  
  have WF_odd:   WF (filter GHC.Real.odd                 s) by apply filter_WF.
  have WF_even:  WF (filter (fun k => ~~ GHC.Real.odd k) s) by apply filter_WF.
  move: (union_WF _ _ WF_odd WF_even) => WF_union.
  
  rewrite !Foldable_all_ssreflect.
  repeat (split=> /=); try by apply valid_correct.
  - apply/allP=> /= k.
    by rewrite in_elem toList_member // filter_member // => /andP[].
  - apply/allP=> /= k.
    rewrite in_elem toList_member // filter_member // => /andP[].
    by rewrite /GHC.Real.odd negb_involutive.
  - apply/eqIntSetMemberP=> // k.
    rewrite union_member // !filter_member //.
    by case: (member k s)=> //=; rewrite orb_negb_r.
Qed.

Theorem thm_filter : toProp prop_filter.
Proof.
  rewrite /prop_filter /= => s WF_s _ _.
  
  have WF_odd:   WF (filter GHC.Real.odd                 s) by apply filter_WF.
  have WF_even:  WF (filter GHC.Real.even                s) by apply filter_WF.
  have WF_even': WF (filter (fun k => ~~ GHC.Real.odd k) s) by apply filter_WF.
  move: (union_WF _ _ WF_odd WF_even) => WF_union.
  
  repeat (split=> /=); try by apply valid_correct.
  rewrite partition_filter //.
  apply/andP; split; first by apply Eq_refl.
  apply/eqIntSetMemberP=> // k.
  rewrite !filter_member //.
  by rewrite /GHC.Real.odd negb_involutive.
Qed.

(* SKIPPED: prop_bitcount *)
