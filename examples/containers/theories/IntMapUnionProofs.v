From Coq Require Import Lia Program.Wf NArith.
Require Import DyadicIntervals CustomTactics BitUtils.
Require Import IntSetProofs IntMapProofs IntMapRecursion.
Require Import Data.IntMap.Internal.
Require Import MapProofs.Bounds.
Import IntMapProofs Data.IntMap.Internal.

(* Preservation and semantic contracts for the native translated algorithms.
   All deferred recursion is unfolded through IntMapRecursion's guarded rule.
   No universal well-formedness hypothesis is used. *)

Lemma union_Nil_l {a} (s : IntMap a) : union Nil s = s.
Proof.
  unfold union. rewrite IntMapRecursion.mergeWithKey'_eq.
  reflexivity.
Qed.

Lemma union_Bin_Bin {a} p1 m1 (l1 r1 : IntMap a) p2 m2 l2 r2 :
  let t1 := Bin p1 m1 l1 r1 in
  let t2 := Bin p2 m2 l2 r2 in
  union t1 t2 =
    if shorter m1 m2 then
      if nomatch p2 p1 m1 then link p1 t1 p2 t2 else
      if Data.IntSet.Internal.zero p2 m1 then Bin p1 m1 (union l1 t2) r1
      else Bin p1 m1 l1 (union r1 t2)
    else if shorter m2 m1 then
      if nomatch p1 p2 m2 then link p1 t1 p2 t2 else
      if Data.IntSet.Internal.zero p1 m2 then Bin p2 m2 (union t1 l2) r2
      else Bin p2 m2 l2 (union t1 r2)
    else if GHC.Base.op_zeze__ p1 p2 then
      Bin p1 m1 (union l1 l2) (union r1 r2)
    else link p1 t1 p2 t2.
Proof.
  cbn zeta. unfold union at 1.
  rewrite IntMapRecursion.mergeWithKey'_eq. reflexivity.
Qed.

Definition union_tip_right {a} (k : N) (v : a) : IntMap a -> IntMap a.
Proof.
  (* Keep the generated local fixpoint intact, including its extra arguments.
     Specializing those arguments inside the fixpoint would not be
     definitionally equal to the translated code. *)
  let rhs := constr:(fun l : IntMap a =>
    IntMapRecursion.mergeWithKey'_f Bin GHC.Base.const GHC.Base.id GHC.Base.id
      (fun _ _ => Nil) (Bin k k l l) (Tip k v)) in
  let rhs := eval cbv beta iota zeta delta [IntMapRecursion.mergeWithKey'_f] in rhs in
  lazymatch rhs with
  | context [?helper (Tip k v) k] => exact (helper (Tip k v) k)
  end.
Defined.

Lemma union_tip_right_eq {a} k (v : a) s :
  union s (Tip k v) = union_tip_right k v s.
Proof.
  unfold union. rewrite IntMapRecursion.mergeWithKey'_eq.
  unfold IntMapRecursion.mergeWithKey'_f.
  destruct s; reflexivity.
Qed.


Lemma union_Nil_r {a} (s : IntMap a) : union s Nil = s.
Proof.
  unfold union. rewrite IntMapRecursion.mergeWithKey'_eq.
  destruct s; reflexivity.
Qed.

Lemma union_Tip_l {a} k (v : a) s :
  union (Tip k v) s = insert k v s.
Proof.
  unfold union. rewrite IntMapRecursion.mergeWithKey'_eq.
  unfold IntMapRecursion.mergeWithKey'_f.
  induction s; cbn [insert GHC.Base.id GHC.Base.const];
    repeat match goal with
    | |- context [if ?t then _ else _] => destruct t
    end; cbn [GHC.Base.id GHC.Base.const] in *;
    try rewrite IHs1; try rewrite IHs2; try reflexivity.
Qed.

Lemma link_sym {a} p (s : IntMap a) q t :
  p <> q -> link p s q t = link q t p s.
Proof.
  intro Hneq.
  assert (Hd : rangeDisjoint (singletonRange p) (singletonRange q) = true).
  { apply disjoint_neq. apply N.eqb_neq. exact Hneq. }
  pose proof (singleton_Desc bool p true) as Hp.
  pose proof (singleton_Desc bool q false) as Hq.
  assert (E : link p (Tip p true) q (Tip q false) =
              link q (Tip q false) p (Tip p true)).
  { eapply Desc_unique.
    - eapply link_Desc; try exact Hp; try exact Hq; try reflexivity;
        try (rewrite rPrefix_singletonRange; reflexivity).
      + exact Hd.
    - eapply link_Desc; try exact Hq; try exact Hp; try reflexivity;
        try (rewrite rPrefix_singletonRange; reflexivity).
      + rewrite rangeDisjoint_sym. exact Hd.
    - intro i. exact (disjoint_reorder bool _ _ _ _ _ _ Hp Hq
        ltac:(rewrite rangeDisjoint_sym; exact Hd) i).
  }
  unfold link, linkWithMask in *.
  destruct (Data.IntSet.Internal.zero p (branchMask p q));
    destruct (Data.IntSet.Internal.zero q (branchMask q p));
    inversion E; subst; try discriminate; reflexivity.
Qed.

Lemma union_tip_right_insert {a} (s : IntMap a) r f :
  Desc s r f -> forall k v,
  union_tip_right k v s = insertWithKey (fun _ _ old => old) k v s.
Proof.
  intro HD. induction HD; intros key value; subst.
  - cbn [union_tip_right insertWithKey].
    change ((if (k =? key)%N then Tip k v else link k (Tip k v) key (Tip key value)) =
      (if (key =? k)%N then Tip key v else link key (Tip key value) k (Tip k v))).
    rewrite N.eqb_sym. destruct (key =? k)%N eqn:E.
    + apply N.eqb_eq in E. subst. reflexivity.
    + apply link_sym. apply N.eqb_neq in E. congruence.
  - cbn [union_tip_right insertWithKey].
    destruct (nomatch key (rPrefix r) (rMask r)) eqn:E.
    + apply link_sym. intro Heq. subst key.
      rewrite nomatch_spec in E by assumption.
      rewrite rPrefix_inRange in E. discriminate.
    + destruct (Data.IntSet.Internal.zero key (rMask r));
        rewrite ?IHHD1, ?IHHD2; reflexivity.
Qed.

Lemma union_Tip_r {a} (s : IntMap a) r f k (v : a) :
  Desc s r f ->
  union s (Tip k v) = insertWithKey (fun _ _ old => old) k v s.
Proof.
  intro HD. rewrite union_tip_right_eq.
  exact (union_tip_right_insert s r f HD k v).
Qed.

Local Ltac union_sem :=
  let i := fresh "i" in intro i;
  repeat match goal with
  | H : forall j : N, ?fn j = _ |- context [?fn i] => rewrite H
  end;
  unfold oro;
  repeat match goal with
  | |- context [if ?test then _ else _] =>
    let E := fresh "E" in destruct test eqn:E; simpl
  end;
  repeat match goal with
  | |- context [?fn i] =>
    is_var fn;
    lazymatch type of fn with
    | N -> option _ => let E := fresh "E" in destruct (fn i) eqn:E; simpl
    end
  end;
  try reflexivity;
  repeat point_to_inRange_Map;
  repeat saturate_inRange;
  try inRange_disjoint.

Program Fixpoint union_Desc
  a (s1 : IntMap a) r1 f1 s2 r2 f2 f
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i, f i = oro (f1 i) (f2 i)) ->
  Desc (union s1 s2) (commonRange r1 r2) f :=
  fun HD1 HD2 Hf => _.
Next Obligation.
  inversion HD1 as [a' k v r' f' Hf1 Hr1 |
    a' l1 rl1 fl1 t1 rt1 ft1 p1 m1 r' f' HL1 HR1 HB1 HS1 HT1 HP1 HM1 HF1]; subst.
  - repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
    rewrite union_Tip_l. eapply insert_Desc; try eassumption; try reflexivity.
    union_sem.
  - repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
    inversion HD2 as [a'' key2 value2 r'' f'' Hf2 Hr2 |
      a'' l2 rl2 fl2 t2 rt2 ft2 p2 m2 r'' f'' HL2 HR2 HB2 HS2 HT2 HP2 HM2 HF2]; subst.
    + repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
        apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
      erewrite union_Tip_r by eassumption.
      rewrite commonRange_sym by (eapply Desc_rNonneg; eassumption).
      eapply insertWithKey_Desc; try eassumption; try reflexivity.
      union_sem.
    + repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
        apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
      rewrite union_Bin_Bin.
      set (sl := Bin (rPrefix r1) (rMask r1) l1 t1) in *.
      set (sr := Bin (rPrefix r2) (rMask r2) l2 t2) in *.
      rewrite !IntSetProofs.shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r1));
        [|destruct (N.ltb_spec (rBits r1) (rBits r2))].
      * apply nomatch_zero_smaller; try assumption; intros.
        -- rewrite rangeDisjoint_sym in *.
           rewrite disjoint_commonRange in * by assumption.
           eapply link_Desc; [exact HD1 | exact HD2 |..]; auto.
        -- rewrite (isSubrange_commonRange_l r1 r2) in * by isSubrange_true.
           eapply DescBin; [eapply union_Desc | exact HR1 |..];
             try eassumption; try reflexivity.
           ++ subst sl sr. cbn. lia.
           ++ isSubrange_true; eapply Desc_rNonneg; eassumption.
           ++ union_sem.
        -- rewrite (isSubrange_commonRange_l r1 r2) in * by isSubrange_true.
           eapply DescBin; [exact HL1 | eapply union_Desc |..];
             try eassumption; try reflexivity.
           ++ subst sl sr. cbn. lia.
           ++ isSubrange_true; eapply Desc_rNonneg; eassumption.
           ++ union_sem.
      * apply nomatch_zero_smaller; try assumption; intros.
        -- rewrite disjoint_commonRange in * by assumption.
           eapply link_Desc; [exact HD1 | exact HD2 |..]; auto.
        -- rewrite (isSubrange_commonRange_r r1 r2) in * by isSubrange_true.
           eapply DescBin; [eapply union_Desc | exact HR2 |..];
             try eassumption; try reflexivity.
           ++ subst sl sr. cbn. lia.
           ++ isSubrange_true; eapply Desc_rNonneg; eassumption.
           ++ union_sem.
        -- rewrite (isSubrange_commonRange_r r1 r2) in * by isSubrange_true.
           eapply DescBin; [exact HL2 | eapply union_Desc |..];
             try eassumption; try reflexivity.
           ++ subst sl sr. cbn. lia.
           ++ isSubrange_true; eapply Desc_rNonneg; eassumption.
           ++ union_sem.
      * apply IntSetProofs.same_size_compare; try Nomega; intros.
        -- subst r2. rewrite commonRange_idem in *.
           eapply DescBin; try assumption; try reflexivity.
           ++ eapply union_Desc.
              ** subst sl sr. cbn. lia.
              ** exact HL1.
              ** exact HL2.
              ** intro i. reflexivity.
           ++ eapply union_Desc.
              ** subst sl sr. cbn. lia.
              ** exact HR1.
              ** exact HR2.
              ** intro i. reflexivity.
           ++ isSubrange_true; eapply Desc_rNonneg; eassumption.
           ++ isSubrange_true; eapply Desc_rNonneg; eassumption.
           ++ union_sem.
        -- rewrite disjoint_commonRange in * by assumption.
           eapply link_Desc; [exact HD1 | exact HD2 |..]; auto.
Qed.

Lemma union_Sem {a} (s1 : IntMap a) f1 s2 f2 :
  Sem s1 f1 -> Sem s2 f2 ->
  Sem (union s1 s2) (fun i => oro (f1 i) (f2 i)).
Proof.
  intros H1 H2. destruct H1; [|destruct H2].
  - rewrite union_Nil_l. eapply Sem_change_f; [exact H2|].
    intro i. rewrite H. reflexivity.
  - rewrite union_Nil_r. eapply Sem_change_f; [eapply DescSem; exact HD|].
    intro i. rewrite H. apply oro_None_r.
  - eapply DescSem. eapply union_Desc; eauto.
Qed.

Lemma union_WF {a} (s1 s2 : IntMap a) :
  WF s1 -> WF s2 -> WF (union s1 s2).
Proof.
  intros [f1 H1] [f2 H2]. eexists. exact (union_Sem s1 f1 s2 f2 H1 H2).
Qed.

Print Assumptions union_WF.

Definition difference_f {a b} :
  (IntMap a -> IntMap b -> IntMap a) -> IntMap a -> IntMap b -> IntMap a.
Proof.
  let rhs := eval unfold difference, mergeWithKey in (@difference a b) in
  lazymatch rhs with
  | context [mergeWithKey' ?bin' ?f ?g1 ?g2] =>
    exact (IntMapRecursion.mergeWithKey'_f bin' f g1 g2)
  end.
Defined.

Lemma difference_eq {a b} (s : IntMap a) (t : IntMap b) :
  difference s t = difference_f difference s t.
Proof.
  exact (IntMapRecursion.mergeWithKey'_eq _ _ _ _ s t).
Qed.

Definition difference_tip_left {a b} (k : N) (v : a) : IntMap b -> IntMap a.
Proof.
  let rhs := constr:(fun l : IntMap b =>
    difference_f (fun _ _ => Nil) (Tip k v) l) in
  let rhs := eval cbv beta iota zeta delta [difference_f IntMapRecursion.mergeWithKey'_f] in rhs in
  lazymatch rhs with
  | context [?helper (Tip k v) k] => exact (helper (Tip k v) k)
  end.
Defined.

Definition difference_tip_right {a b} (k : N) (v : b) : IntMap a -> IntMap a.
Proof.
  let rhs := constr:(fun l : IntMap a =>
    difference_f (fun _ _ => Nil) (Bin k k l l) (Tip k v)) in
  let rhs := eval cbv beta iota zeta delta [difference_f IntMapRecursion.mergeWithKey'_f] in rhs in
  lazymatch rhs with
  | context [?helper (Tip k v) k] => exact (helper (Tip k v) k)
  end.
Defined.

Lemma difference_Tip_l {a b} k (v : a) (s : IntMap b) :
  difference (Tip k v) s = if member k s then Nil else Tip k v.
Proof.
  rewrite difference_eq.
  change (difference_tip_left k v s = if member k s then Nil else Tip k v).
  induction s; cbn [difference_tip_left member].
  - destruct (nomatch k p m); [reflexivity|].
    destruct (Data.IntSet.Internal.zero k m);
      rewrite ?IHs1, ?IHs2;
      repeat match goal with |- context [if ?test then _ else _] => destruct test end;
      reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma difference_Tip_r {a b} (s : IntMap a) r f key (value : b) :
  Desc s r f -> difference s (Tip key value) = delete key s.
Proof.
  intro HD.
  rewrite difference_eq.
  transitivity (difference_tip_right key value s).
  - destruct s; reflexivity.
  - induction HD; subst; cbn [difference_tip_right delete].
    + change ((if (k =? key)%N then Nil else Tip k v) =
        (if (key =? k)%N then Nil else Tip k v)).
      rewrite N.eqb_sym. reflexivity.
    + destruct (nomatch key (rPrefix r) (rMask r)); [reflexivity|].
      destruct (Data.IntSet.Internal.zero key (rMask r));
        rewrite ?IHHD1, ?IHHD2; unfold GHC.Base.id.
      all: match goal with
      | |- bin _ _ ?l ?r = _ => destruct l; destruct r
      end; try reflexivity;
        match goal with H : Desc Nil _ _ |- _ => inversion H end.
Qed.

Lemma difference_Nil_l {a b} (s : IntMap b) :
  @difference a b Nil s = Nil.
Proof. rewrite difference_eq. reflexivity. Qed.

Lemma difference_Nil_r {a b} (s : IntMap a) :
  @difference a b s Nil = s.
Proof. rewrite difference_eq. destruct s; reflexivity. Qed.

Lemma bin_Nil_l {a} p m (s : IntMap a) : bin p m Nil s = s.
Proof. destruct s; reflexivity. Qed.

Lemma bin_Nil_r {a} p m (s : IntMap a) : bin p m s Nil = s.
Proof. destruct s; reflexivity. Qed.

Lemma difference_Bin_Bin {a b} p1 m1 (l1 r1 : IntMap a) p2 m2 (l2 r2 : IntMap b) :
  let t1 := Bin p1 m1 l1 r1 in
  let t2 := Bin p2 m2 l2 r2 in
  difference t1 t2 =
    if shorter m1 m2 then
      if nomatch p2 p1 m1 then t1 else
      if Data.IntSet.Internal.zero p2 m1 then bin p1 m1 (difference l1 t2) r1
      else bin p1 m1 l1 (difference r1 t2)
    else if shorter m2 m1 then
      if nomatch p1 p2 m2 then t1 else
      if Data.IntSet.Internal.zero p1 m2 then difference t1 l2
      else difference t1 r2
    else if GHC.Base.op_zeze__ p1 p2 then
      bin p1 m1 (difference l1 l2) (difference r1 r2)
    else t1.
Proof.
  cbn zeta. rewrite difference_eq. unfold difference_f, IntMapRecursion.mergeWithKey'_f.
  repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    try reflexivity.
  all: first [apply bin_Nil_l | apply bin_Nil_r].
Qed.

Program Fixpoint difference_Desc
  a b (s1 : IntMap a) r1 f1 (s2 : IntMap b) r2 f2 f
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i, f i = match f2 i with Some _ => None | None => f1 i end) ->
  Desc0 (difference s1 s2) r1 f := fun HD1 HD2 Hf => _.
Next Obligation.
  inversion HD1 as [a' k v r' f' Hf1 Hr1 |
    a' l1 rl1 fl1 t1 rt1 ft1 p1 m1 r' f' HL1 HR1 HB1 HS1 HT1 HP1 HM1 HF1]; subst.
  - repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
    rewrite difference_Tip_l, (member_Desc HD2).
    destruct (f2 k) eqn:E; cbn.
    + apply Desc0Nil. intro i. rewrite Hf, Hf1.
      destruct (i =? k)%N eqn:Ei.
      * apply N.eqb_eq in Ei. subst i. rewrite E. reflexivity.
      * destruct (f2 i); reflexivity.
    + eapply Desc0NotNil; [exact HD1 | apply isSubrange_refl |].
      intro i. rewrite Hf, Hf1.
      destruct (i =? k)%N eqn:Ei.
      * apply N.eqb_eq in Ei. subst i. rewrite E. reflexivity.
      * destruct (f2 i); reflexivity.
  - repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
    inversion HD2 as [b' key2 value2 r'' f'' Hf2 Hr2 |
      b' l2 rl2 fl2 t2 rt2 ft2 p2 m2 r'' f'' HL2 HR2 HB2 HS2 HT2 HP2 HM2 HF2]; subst.
    + repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
        apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
      erewrite difference_Tip_r by eassumption.
      eapply delete_Desc; [exact HD1 | apply isSubrange_refl |]. union_sem.
    + repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
        apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
      rewrite difference_Bin_Bin.
      set (sl := Bin (rPrefix r1) (rMask r1) l1 t1) in *.
      set (sr := Bin (rPrefix r2) (rMask r2) l2 t2) in *.
      rewrite !IntSetProofs.shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r1));
        [|destruct (N.ltb_spec (rBits r1) (rBits r2))].
      * apply nomatch_zero_smaller; try assumption; intros.
        -- eapply Desc0NotNil; [exact HD1 | apply isSubrange_refl |]. union_sem.
        -- eapply bin_Desc0.
           ++ eapply difference_Desc; try eassumption.
              ** subst sl sr. cbn. lia.
              ** intro i. reflexivity.
           ++ apply Desc_Desc0. exact HR1.
           ++ exact HB1.
           ++ exact HS1.
           ++ exact HT1.
           ++ reflexivity.
           ++ reflexivity.
           ++ union_sem.
        -- eapply bin_Desc0.
           ++ apply Desc_Desc0. exact HL1.
           ++ eapply difference_Desc; try eassumption.
              ** subst sl sr. cbn. lia.
              ** intro i. reflexivity.
           ++ exact HB1.
           ++ exact HS1.
           ++ exact HT1.
           ++ reflexivity.
           ++ reflexivity.
           ++ union_sem.
      * apply nomatch_zero_smaller; try assumption; intros.
        -- eapply Desc0NotNil; [exact HD1 | apply isSubrange_refl |]. union_sem.
        -- eapply difference_Desc; try eassumption.
           ++ subst sl sr. cbn. lia.
           ++ union_sem.
        -- eapply difference_Desc; try eassumption.
           ++ subst sl sr. cbn. lia.
           ++ union_sem.
      * apply IntSetProofs.same_size_compare; try Nomega; intros.
        -- subst r2. eapply bin_Desc0; try assumption; try reflexivity.
           ++ eapply difference_Desc; try eassumption.
              ** subst sl sr. cbn. lia.
              ** intro i. reflexivity.
           ++ eapply difference_Desc; try eassumption.
              ** subst sl sr. cbn. lia.
              ** intro i. reflexivity.
           ++ exact HS1.
           ++ exact HT1.
           ++ union_sem.
        -- eapply Desc0NotNil; [exact HD1 | apply isSubrange_refl |]. union_sem.
Qed.

Lemma difference_Sem {a b} (s1 : IntMap a) f1 (s2 : IntMap b) f2 :
  Sem s1 f1 -> Sem s2 f2 ->
  Sem (difference s1 s2)
    (fun i => match f2 i with Some _ => None | None => f1 i end).
Proof.
  intros H1 H2. destruct H1; [|destruct H2].
  - rewrite difference_Nil_l. apply SemNil. intro i. rewrite H.
    destruct (f2 i); reflexivity.
  - rewrite difference_Nil_r. eapply Sem_change_f; [eapply DescSem; exact HD|].
    intro i. rewrite H. reflexivity.
  - eapply Desc0_Sem. eapply difference_Desc; eauto.
    intro i. destruct (f0 i); reflexivity.
Qed.

Lemma difference_WF {a b} (s1 : IntMap a) (s2 : IntMap b) :
  WF s1 -> WF s2 -> WF (difference s1 s2).
Proof.
  intros [f1 H1] [f2 H2]. eexists. exact (difference_Sem s1 f1 s2 f2 H1 H2).
Qed.

Print Assumptions difference_WF.

Definition intersection_f {a b} :=
  @IntMapRecursion.mergeWithKey'_f a a b bin GHC.Base.const
    (GHC.Base.const Nil) (GHC.Base.const Nil).

Lemma intersection_eq {a b} (s : IntMap a) (t : IntMap b) :
  intersection s t = intersection_f intersection s t.
Proof. exact (IntMapRecursion.mergeWithKey'_eq _ _ _ _ s t). Qed.

Definition intersection_tip_left {a b} (k : N) (v : a) : IntMap b -> IntMap a.
Proof.
  let rhs := constr:(fun l : IntMap b =>
    intersection_f (fun _ _ => Nil) (Tip k v) l) in
  let rhs := eval cbv beta iota zeta delta [intersection_f IntMapRecursion.mergeWithKey'_f] in rhs in
  lazymatch rhs with
  | context [?helper (Tip k v) k] => exact (helper (Tip k v) k)
  end.
Defined.

Definition intersection_tip_right {a b} (k : N) (v : b) : IntMap a -> IntMap a.
Proof.
  let rhs := constr:(fun l : IntMap a =>
    intersection_f (fun _ _ => Nil) (Bin k k l l) (Tip k v)) in
  let rhs := eval cbv beta iota zeta delta [intersection_f IntMapRecursion.mergeWithKey'_f] in rhs in
  lazymatch rhs with
  | context [?helper (Tip k v) k] => exact (helper (Tip k v) k)
  end.
Defined.

Lemma intersection_Tip_l {a b} k (v : a) (s : IntMap b) :
  intersection (Tip k v) s = if member k s then Tip k v else Nil.
Proof.
  rewrite intersection_eq.
  change (intersection_tip_left k v s = if member k s then Tip k v else Nil).
  induction s; cbn [intersection_tip_left member].
  - destruct (nomatch k p m); [reflexivity|].
    destruct (Data.IntSet.Internal.zero k m);
      rewrite ?IHs1, ?IHs2;
      repeat match goal with |- context [if ?test then _ else _] => destruct test end;
      reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma intersection_Tip_r_raw {a b} (s : IntMap a) k (v : b) :
  intersection s (Tip k v) =
    if member k s then match lookup k s with Some w => Tip k w | None => Nil end
    else Nil.
Proof.
  rewrite intersection_eq.
  transitivity (intersection_tip_right k v s).
  - destruct s; reflexivity.
  - induction s; cbn [intersection_tip_right lookup member].
    + destruct (nomatch k p m); [reflexivity|].
      destruct (Data.IntSet.Internal.zero k m);
        rewrite ?IHs1, ?IHs2; unfold GHC.Base.const;
        rewrite ?bin_Nil_l, ?bin_Nil_r; reflexivity.
    + change ((if (k0 =? k)%N then Tip k0 a0 else Nil) =
        (if (k =? k0)%N then
           match (if (k =? k0)%N then Some a0 else None) with
           | Some w => Tip k w | None => Nil end else Nil)).
      rewrite N.eqb_sym. destruct (k =? k0)%N eqn:E; [|reflexivity].
      apply N.eqb_eq in E. subst. reflexivity.
    + reflexivity.
Qed.

Lemma intersection_Tip_r {a b} (s : IntMap a) r f k (v : b) :
  Desc s r f -> intersection s (Tip k v) =
    match f k with Some w => Tip k w | None => Nil end.
Proof.
  intro HD. rewrite intersection_Tip_r_raw, (member_Desc HD), (lookup_Desc HD).
  destruct (f k); reflexivity.
Qed.

Lemma intersection_Nil_l {a b} (s : IntMap b) :
  @intersection a b Nil s = Nil.
Proof. rewrite intersection_eq. reflexivity. Qed.

Lemma intersection_Nil_r {a b} (s : IntMap a) :
  @intersection a b s Nil = Nil.
Proof. rewrite intersection_eq. destruct s; reflexivity. Qed.

Lemma intersection_Bin_Bin {a b} p1 m1 (l1 r1 : IntMap a) p2 m2 (l2 r2 : IntMap b) :
  let t1 := Bin p1 m1 l1 r1 in
  let t2 := Bin p2 m2 l2 r2 in
  intersection t1 t2 =
    if shorter m1 m2 then
      if nomatch p2 p1 m1 then Nil else
      if Data.IntSet.Internal.zero p2 m1 then intersection l1 t2
      else intersection r1 t2
    else if shorter m2 m1 then
      if nomatch p1 p2 m2 then Nil else
      if Data.IntSet.Internal.zero p1 m2 then intersection t1 l2
      else intersection t1 r2
    else if GHC.Base.op_zeze__ p1 p2 then
      bin p1 m1 (intersection l1 l2) (intersection r1 r2)
    else Nil.
Proof.
  cbn zeta. rewrite intersection_eq.
  unfold intersection_f, IntMapRecursion.mergeWithKey'_f.
  repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    try reflexivity.
  all: first [apply bin_Nil_l | apply bin_Nil_r].
Qed.

Program Fixpoint intersection_Desc
  a b (s1 : IntMap a) r1 f1 (s2 : IntMap b) r2 f2 f
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i, f i = match f2 i with Some _ => f1 i | None => None end) ->
  Desc0 (intersection s1 s2) r1 f := fun HD1 HD2 Hf => _.
Next Obligation.
  inversion HD1 as [a' k v r' f' Hf1 Hr1 |
    a' l1 rl1 fl1 t1 rt1 ft1 p1 m1 r' f' HL1 HR1 HB1 HS1 HT1 HP1 HM1 HF1]; subst.
  - repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
    rewrite intersection_Tip_l, (member_Desc HD2).
    destruct (f2 k) eqn:E; cbn.
    + eapply Desc0NotNil; [exact HD1 | apply isSubrange_refl |].
      intro i. rewrite Hf, Hf1.
      destruct (i =? k)%N eqn:Ei.
      * apply N.eqb_eq in Ei. subst i. rewrite E. reflexivity.
      * destruct (f2 i); reflexivity.
    + apply Desc0Nil. intro i. rewrite Hf, Hf1.
      destruct (i =? k)%N eqn:Ei.
      * apply N.eqb_eq in Ei. subst i. rewrite E. reflexivity.
      * destruct (f2 i); reflexivity.
  - repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
    inversion HD2 as [b' key2 value2 r'' f'' Hf2 Hr2 |
      b' l2 rl2 fl2 t2 rt2 ft2 p2 m2 r'' f'' HL2 HR2 HB2 HS2 HT2 HP2 HM2 HF2]; subst.
    + repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
        apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
      rewrite (intersection_Tip_r _ _ _ _ _ HD1).
      destruct (f1 key2) eqn:E.
      * eapply Desc0NotNil; [apply singleton_Desc | |].
        -- unfold isSubrange. rewrite rPrefix_singletonRange.
           rewrite (Desc_inside HD1 E). cbn [singletonRange rBits].
           apply N.leb_le. change (0 <= rBits r1)%N. lia.
        -- intro i. rewrite Hf, Hf2.
           destruct (i =? key2)%N eqn:Ei.
           ++ apply N.eqb_eq in Ei. subst i. rewrite E. reflexivity.
           ++ reflexivity.
      * apply Desc0Nil. intro i. rewrite Hf, Hf2.
        destruct (i =? key2)%N eqn:Ei.
        -- apply N.eqb_eq in Ei. subst i. exact E.
        -- reflexivity.
    + repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
        apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
      rewrite intersection_Bin_Bin.
      set (sl := Bin (rPrefix r1) (rMask r1) l1 t1) in *.
      set (sr := Bin (rPrefix r2) (rMask r2) l2 t2) in *.
      rewrite !IntSetProofs.shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r1));
        [|destruct (N.ltb_spec (rBits r1) (rBits r2))].
      * apply nomatch_zero_smaller; try assumption; intros.
        -- apply Desc0Nil. union_sem.
        -- eapply Desc0_subRange.
           ++ eapply intersection_Desc; try eassumption.
              ** subst sl sr. cbn. lia.
              ** union_sem.
           ++ eapply isSubrange_trans; [exact HS1 | apply isSubrange_halfRange; exact HB1].
        -- eapply Desc0_subRange.
           ++ eapply intersection_Desc; try eassumption.
              ** subst sl sr. cbn. lia.
              ** union_sem.
           ++ eapply isSubrange_trans; [exact HT1 | apply isSubrange_halfRange; exact HB1].
      * apply nomatch_zero_smaller; try assumption; intros.
        -- apply Desc0Nil. union_sem.
        -- eapply intersection_Desc; try eassumption.
           ++ subst sl sr. cbn. lia.
           ++ union_sem.
        -- eapply intersection_Desc; try eassumption.
           ++ subst sl sr. cbn. lia.
           ++ union_sem.
      * apply IntSetProofs.same_size_compare; try Nomega; intros.
        -- subst r2. eapply bin_Desc0; try assumption; try reflexivity.
           ++ eapply intersection_Desc; try eassumption.
              ** subst sl sr. cbn. lia.
              ** intro i. reflexivity.
           ++ eapply intersection_Desc; try eassumption.
              ** subst sl sr. cbn. lia.
              ** intro i. reflexivity.
           ++ exact HS1.
           ++ exact HT1.
           ++ union_sem.
        -- apply Desc0Nil. union_sem.
Qed.

Lemma intersection_Sem {a b} (s1 : IntMap a) f1 (s2 : IntMap b) f2 :
  Sem s1 f1 -> Sem s2 f2 ->
  Sem (intersection s1 s2)
    (fun i => match f2 i with Some _ => f1 i | None => None end).
Proof.
  intros H1 H2. destruct H1; [|destruct H2].
  - rewrite intersection_Nil_l. apply SemNil. intro i. rewrite H.
    destruct (f2 i); reflexivity.
  - rewrite intersection_Nil_r. apply SemNil. intro i. rewrite H. reflexivity.
  - eapply Desc0_Sem. eapply intersection_Desc; eauto.
    intro i. destruct (f0 i); reflexivity.
Qed.

Lemma intersection_WF {a b} (s1 : IntMap a) (s2 : IntMap b) :
  WF s1 -> WF s2 -> WF (intersection s1 s2).
Proof.
  intros [f1 H1] [f2 H2]. eexists. exact (intersection_Sem s1 f1 s2 f2 H1 H2).
Qed.

Print Assumptions intersection_WF.

Lemma disjoint_Nil_l {a b} (s : IntMap b) : @disjoint a b Nil s = true.
Proof. rewrite IntMapRecursion.disjoint_eq. reflexivity. Qed.

Lemma disjoint_Nil_r {a b} (s : IntMap a) : @disjoint a b s Nil = true.
Proof. rewrite IntMapRecursion.disjoint_eq. destruct s; reflexivity. Qed.

Lemma disjoint_Tip_l {a b} k (v : a) (s : IntMap b) :
  disjoint (Tip k v) s = notMember k s.
Proof. rewrite IntMapRecursion.disjoint_eq. destruct s; reflexivity. Qed.

Lemma disjoint_Tip_r {a b} (s : IntMap a) k (v : b) :
  disjoint s (Tip k v) = notMember k s.
Proof.
  rewrite IntMapRecursion.disjoint_eq. destruct s; try reflexivity.
  change (negb (k0 =? k)%N = negb (k =? k0)%N).
  rewrite N.eqb_sym. reflexivity.
Qed.

Lemma disjoint_Bin_Bin {a b} p1 m1 (l1 r1 : IntMap a) p2 m2 (l2 r2 : IntMap b) :
  let t1 := Bin p1 m1 l1 r1 in
  let t2 := Bin p2 m2 l2 r2 in
  disjoint t1 t2 =
    if shorter m1 m2 then
      if nomatch p2 p1 m1 then true else
      if Data.IntSet.Internal.zero p2 m1 then disjoint l1 t2
      else disjoint r1 t2
    else if shorter m2 m1 then
      if nomatch p1 p2 m2 then true else
      if Data.IntSet.Internal.zero p1 m2 then disjoint t1 l2
      else disjoint t1 r2
    else if GHC.Base.op_zeze__ p1 p2 then
      andb (disjoint l1 l2) (disjoint r1 r2)
    else true.
Proof. cbn zeta. rewrite IntMapRecursion.disjoint_eq. reflexivity. Qed.

Lemma null_bin {a} p m (l r : IntMap a) :
  null (bin p m l r) = andb (null l) (null r).
Proof. destruct l; destruct r; reflexivity. Qed.

(* The boolean algorithm tests precisely whether intersection is empty.
   Its recursion has the same structural subproblems as intersection. *)
Program Fixpoint disjoint_intersection_Desc
  a b (s1 : IntMap a) r1 f1 (s2 : IntMap b) r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  disjoint s1 s2 = null (intersection s1 s2) := fun HD1 HD2 => _.
Next Obligation.
  inversion HD1 as [a' k v r' f' Hf1 Hr1 |
    a' l1 rl1 fl1 t1 rt1 ft1 p1 m1 r' f' HL1 HR1 HB1 HS1 HT1 HP1 HM1 HF1]; subst.
  - repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
    rewrite disjoint_Tip_l, intersection_Tip_l.
    unfold notMember. destruct (member k s2); reflexivity.
  - repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
    inversion HD2 as [b' key2 value2 r'' f'' Hf2 Hr2 |
      b' l2 rl2 fl2 t2 rt2 ft2 p2 m2 r'' f'' HL2 HR2 HB2 HS2 HT2 HP2 HM2 HF2]; subst.
    + repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
        apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
      rewrite disjoint_Tip_r, (intersection_Tip_r _ _ _ _ _ HD1).
      unfold notMember. rewrite (member_Desc HD1).
      destruct (f1 key2); reflexivity.
    + repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
        apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
      rewrite disjoint_Bin_Bin, intersection_Bin_Bin.
      repeat match goal with |- context [if ?test then _ else _] => destruct test end;
        rewrite ?null_bin;
        repeat erewrite disjoint_intersection_Desc by
          (first [eassumption | cbn; lia]); reflexivity.
Qed.

Lemma disjoint_intersection {a b} (s1 : IntMap a) (s2 : IntMap b) :
  WF s1 -> WF s2 -> disjoint s1 s2 = null (intersection s1 s2).
Proof.
  intros [f1 H1] [f2 H2]. destruct H1; [|destruct H2].
  - rewrite disjoint_Nil_l, intersection_Nil_l. reflexivity.
  - rewrite disjoint_Nil_r, intersection_Nil_r. reflexivity.
  - eapply disjoint_intersection_Desc; eassumption.
Qed.

Lemma disjoint_Sem {a b} (s1 : IntMap a) f1 (s2 : IntMap b) f2 :
  Sem s1 f1 -> Sem s2 f2 ->
  (disjoint s1 s2 = true <-> forall k, f1 k = None \/ f2 k = None).
Proof.
  intros H1 H2.
  rewrite (disjoint_intersection s1 s2 ltac:(exists f1; exact H1)
    ltac:(exists f2; exact H2)).
  pose proof (intersection_Sem s1 f1 s2 f2 H1 H2) as HI.
  rewrite (null_Sem HI).
  split.
  - intros H k. specialize (H k). destruct (f2 k); [left; exact H|right; reflexivity].
  - intros H k. destruct (H k) as [E|E]; rewrite E; [destruct (f2 k)|]; reflexivity.
Qed.

Lemma disjoint_spec {a b} (s1 : IntMap a) (s2 : IntMap b) :
  WF s1 -> WF s2 ->
  (disjoint s1 s2 = true <->
   forall k, lookup k s1 = None \/ lookup k s2 = None).
Proof.
  intros [f1 H1] [f2 H2]. rewrite (disjoint_Sem s1 f1 s2 f2 H1 H2).
  split; intros H k; specialize (H k);
    rewrite (lookup_Sem H1), (lookup_Sem H2) in *; exact H.
Qed.

Print Assumptions disjoint_spec.

Lemma intersection_lookup {a b} (s1 : IntMap a) (s2 : IntMap b) k :
  WF s1 -> WF s2 ->
  lookup k (intersection s1 s2) =
    match lookup k s2 with Some _ => lookup k s1 | None => None end.
Proof.
  intros [f1 H1] [f2 H2].
  rewrite (lookup_Sem (intersection_Sem s1 f1 s2 f2 H1 H2)).
  rewrite (lookup_Sem H1), (lookup_Sem H2). reflexivity.
Qed.

Lemma intersection_lookup_some {a b} (s1 : IntMap a) (s2 : IntMap b) k v :
  WF s1 -> WF s2 ->
  (lookup k (intersection s1 s2) = Some v <->
   lookup k s1 = Some v /\ exists w, lookup k s2 = Some w).
Proof.
  intros H1 H2. rewrite (intersection_lookup s1 s2 k H1 H2).
  destruct (lookup k s2) eqn:E.
  - split.
    + intro H. split; [exact H|eexists; reflexivity].
    + intros [H _]. exact H.
  - split; [discriminate|]. intros [_ [w H]]. discriminate.
Qed.

(* A surviving entry retains its original key and value. This is the fact
   needed to preserve payload-at-key invariants, not just structural WF. *)
Lemma intersection_preserves_keys {a b} (s1 : IntMap a) (s2 : IntMap b) k v :
  WF s1 -> WF s2 ->
  lookup k (intersection s1 s2) = Some v -> lookup k s1 = Some v.
Proof.
  intros H1 H2 H. apply (intersection_lookup_some s1 s2 k v H1 H2) in H.
  exact (proj1 H).
Qed.

Lemma filter_lookup {a} p (s : IntMap a) k :
  WF s ->
  lookup k (Data.IntMap.Internal.filter p s) =
    match lookup k s with Some v => if p v then Some v else None | None => None end.
Proof.
  intros [f H].
  pose proof (@filter_Sem a p s f
    (fun i => match f i with Some v => if p v then Some v else None | None => None end)
    H (fun _ => eq_refl)) as HF.
  rewrite (lookup_Sem HF), (lookup_Sem H). reflexivity.
Qed.

Lemma filter_lookup_some {a} p (s : IntMap a) k v :
  WF s ->
  (lookup k (Data.IntMap.Internal.filter p s) = Some v <->
   lookup k s = Some v /\ p v = true).
Proof.
  intro HW. rewrite (filter_lookup p s k HW).
  destruct (lookup k s) eqn:E; [destruct (p a0) eqn:Ep|];
    split; intros H; try discriminate.
  - inversion H; subst. split; [reflexivity|exact Ep].
  - destruct H as [H _]. exact H.
  - destruct H as [H Hp]. inversion H; subst. congruence.
  - destruct H as [H _]. discriminate.
Qed.

Lemma filter_preserves_keys {a} p (s : IntMap a) k v :
  WF s -> lookup k (Data.IntMap.Internal.filter p s) = Some v ->
  lookup k s = Some v.
Proof.
  intros HW H. apply (filter_lookup_some p s k v HW) in H. exact (proj1 H).
Qed.

Print Assumptions intersection_Sem.
Print Assumptions intersection_preserves_keys.
Print Assumptions filter_preserves_keys.
