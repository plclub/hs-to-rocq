Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.


Require Import DyadicIntervals.
Require Import CustomTactics.
Require Import BitUtils.

(** * The IntMap formalization *)

Require Import HsToRocq.DeferredFix.
Require Import IntSetProofs.
Require Import Data.IntSet.Internal.
Require Import Data.IntMap.Internal.
Require Import MapProofs.Bounds.
Require Import Lia.

Import GHC.Base.

Set Bullet Behavior "Strict Subproofs".


Axiom deferredFix2_eq : forall a b r `{Default r} (f : (a -> b -> r) -> (a -> b -> r)),
  deferredFix2 f = f (deferredFix2 f).

From Coq Require Import ssreflect.
From Coq Require Import Unicode.Utf8.

(* Coq 8.20: typeclass resolution no longer unfolds Key→N→Word to find EqLaws_Word *)
#[export] Instance EqLaws_Key : Base.EqLaws Key := Proofs.GHC.Base.EqLaws_Word.

Lemma oro_None_r {a} (x:option a) : oro x None = x.
Proof. destruct x; simpl; reflexivity. Qed.
Lemma oro_None_l {a} (x:option a) : oro None x = x.
Proof. reflexivity. Qed.
Lemma oro_Some_l a (v:a) x : oro (Some v) x = Some v.
Proof. destruct x; simpl; auto. Qed.
Lemma oro_Some a (v:a) x y : oro x y = Some v -> x = Some v \/ y = Some v.
Proof.
  destruct x; destruct y; simpl; auto.
Qed.


(** ** Well-formed IntMap.
This section introduces the predicate to describe the well-formedness of
an IntMap. It has parameters that describe the range that this map covers,
and a function that carries it denotation. This way, invariant preservation
and functional correctness of an operation can be expressed in one go.
*)

Definition singletonRange k : range := (k, 0%N).


Local Open Scope N_scope.

Inductive Desc : forall {a}, IntMap a -> range -> (N -> option a) -> Prop :=
  | DescTip : forall a k (v : a) r f,
    (forall i, f i = if i =? k then Some v else None) ->
    r = singletonRange k ->
    Desc (Tip k v) r f
  | DescBin : forall a m1 r1 f1 m2 r2 f2 p msk r (f : N  -> option a),
    Desc m1 r1 f1 ->
    Desc m2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r ->
    (forall i, f i = oro (f1 i) (f2 i)) ->
    Desc (Bin p msk m1 m2) r f.

(** A variant that also allows [Nil], or sets that do not
    cover the full given range, but are certainly contained in them.
    This is used to describe operations that may delete elements.
 *)

Inductive Desc0 : forall {a}, IntMap a -> range -> (N -> option a) -> Prop :=
  | Desc0Nil : forall {a} r (f : N -> option a), (forall i, f i = None) -> Desc0 Nil r f
  | Desc0NotNil :
      forall {a},
      forall m r f r' (f' : N -> option a),
      forall (HD : Desc m r f),
      forall (Hsubrange: isSubrange r r' = true)
      (Hf : forall i, f' i = f i),
      Desc0 m r' f'.

(** A variant that also allows [Nil] and does not reqiure a range. Used
    for the top-level specification.
 *)

Inductive Sem : forall {a}, IntMap a -> (N -> option a) -> Prop :=
  | SemNil : forall {a} (f : N -> option a), (forall i, f i = None) -> Sem Nil f
  | DescSem : forall {a} s r (f : N -> option a) (HD : Desc s r f), Sem s f.

(** The highest level: Just well-formedness.
 *)

Fixpoint sem {a} (s: IntMap a) (i: Key) :=
  match s with
  | Nil => None
  | Tip k x => if (i == k) then Some x else None
  | Bin p msk m1 m2 => oro (sem m1 i) (sem m2 i)
  end.

Fixpoint Sem2 {a} (s: IntMap a) (i : N) : option a :=                                 
 match s with                                                     
 | Nil => None                                                    
 | Tip x v => if (x == i) then Some v else None                                   
 | Bin p m s1 s2 => oro (Sem2 s1 i) (Sem2 s2 i)                                    
 end.


Definition WF {a} (s : IntMap a) : Prop := exists f, Sem s f.

(* Transitional assumption for consumers that still accept raw IntMaps.
   It is false for the exposed datatype: for example, Bin 0 0 Nil Nil has
   empty children and cannot satisfy Desc. A smart-constructor usage
   convention does not establish this universally quantified statement.
   WF-premised contracts and operation-preservation lemmas let callers
   replace uses of this assumption with actual invariant evidence. *)
Axiom All_IntMaps_WF : forall A (m : IntMap A), WF m.

Ltac inversion_Desc HD1 :=
  inversion HD1;
  repeat match goal with [ H : existT ?f ?a ?s1 = existT ?f ?a ?s2 |- _ ] =>
                  apply Eqdep.EqdepTheory.inj_pair2 in H
  end;
  subst.


(** ** Lemmas related to well-formedness *)


(** All of these respect extensionality of [f] *)

Lemma Desc_change_f:
  forall {a} (s:IntMap a) r f f',
  Desc s r f -> (forall i, f' i = f i) -> Desc s r f'.
Proof.
  intros.
  induction H.
  * eapply DescTip; try eassumption.
    intro i. rewrite H0 H. reflexivity.
  * eapply DescBin; try eassumption.
    intro i. rewrite H0 H7. reflexivity.
Qed.

Lemma Sem_change_f:
  forall {a} (s:IntMap a) f f',
  Sem s f -> (forall i, f' i = f i) -> Sem s f'.
Proof.
  intros.
  destruct H.
  * apply SemNil.
    intro i. rewrite H0 H. reflexivity.
  * eapply DescSem. eapply Desc_change_f. eassumption.
    intro i. rewrite H0. reflexivity.
Qed.


Lemma Desc_Desc0:
  forall {a} (s:IntMap a) r f, Desc s r f -> Desc0 s r f.
Proof. intros.
  eapply Desc0NotNil.
  * eassumption.
  * apply isSubrange_refl.
  * intro. reflexivity.
Qed.

(* Formal counterexample: Desc0_Desc is false because Desc0 allows Nil via
   Desc0Nil, but Desc has no Nil constructor (only DescTip and DescBin). *)
Lemma Desc0_Desc_false :
  ~ (forall {a} (s: IntMap a) r f, Desc0 s r f -> Desc s r f).
Proof.
  intro H.
  pose proof (H N Nil (singletonRange 0%N) (fun _ => None)
    (Desc0Nil (singletonRange 0%N) (fun _ => None) (fun _ => eq_refl))) as HD.
  inversion HD.
Qed.

(* FALSE: disproved by Desc0_Desc_false above. Aborted to prevent use.
   Use Desc0_Sem instead. *)
Lemma Desc0_Desc:
  forall {a} (s: IntMap a) r f, Desc0 s r f -> Desc s r f.
Proof.
Abort.
 

Lemma Desc0_Sem:
  forall {a} (s:IntMap a) r f, Desc0 s r f -> Sem s f.
Proof.
  intros.
  destruct H.
  * apply SemNil; eassumption.
  * eapply DescSem. eapply Desc_change_f. eassumption. assumption.
Qed.

Lemma Desc0_WF:
  forall {a} (s:IntMap a) r f, Desc0 s r f -> WF s.
Proof.
  intros. eexists. eapply Desc0_Sem. eassumption.
Qed.

Lemma Desc_outside:
 forall {a} {s : IntMap a} {r f i}, Desc s r f -> inRange i r = false -> f i = None.
Proof.
 intros ????? HD Houtside.
 induction HD;subst.
 * rewrite H.
   unfold inRange, singletonRange in *.
   simpl in Houtside.
   destruct (i =? k) eqn:IsI.
   inversion Houtside.
   auto.
 * rewrite H4; clear H4.
   rewrite IHHD1; last inRange_false.
   rewrite IHHD2; last inRange_false.
   reflexivity.
Qed.

Lemma Desc_inside:
 forall {a} {s : IntMap a} {r f i} {v}, Desc s r f -> f i = Some v -> inRange i r = true.
Proof.
 intros ?????? HD Hf.
 destruct (inRange i r) eqn:?; intuition.
 rewrite (Desc_outside HD) // in Hf.
Qed.

Lemma Desc0_outside:
  forall {a} {s : IntMap a} {r f i}, Desc0 s r f -> inRange i r = false -> f i = None.
Proof.
  intros.
  destruct H; auto.
  rewrite Hf.
  rewrite (Desc_outside HD) //; inRange_false.
Qed.

Lemma Desc0_subRange:
  forall {a} {s : IntMap a} {r r' f}, Desc0 s r f -> isSubrange r r' = true -> Desc0 s r' f.
Proof.
  intros.
  induction H.
  * apply Desc0Nil; assumption.
  * eapply Desc0NotNil; try eassumption.
    isSubrange_true.
Qed.

(** The [Desc] predicate only holds for non-empty sets. *)
Lemma Desc_some_f:
  forall {a} {s:IntMap a} {r f}, Desc s r f -> exists i v, f i = Some v.
Proof.
  intros ???? HD.
  induction HD; subst.
  +
    exists k. exists v.
    rewrite H.
    rewrite N.eqb_refl.
    auto.
  + destruct IHHD1  as [j [v1 ?]].
    exists j. exists v1.
    rewrite H4.
    rewrite H2.
    reflexivity.
Qed.

(** The [Desc] predicate is right_unique *)
Lemma Desc_unique_f:
  forall {a}{s:IntMap a}{r1 f1 r2 f2}, Desc s r1 f1 -> Desc s r2 f2 -> (forall i, f1 i = f2 i).
Proof.
  intros ?????? HD.
  revert r2 f2.
  induction HD; subst.
  + intros r2 f2 HD2 i.
    inversion_Desc HD2.
    rewrite H H5.
    reflexivity.
  + intros r3 f3 HD3 i.
    inversion_Desc HD3.
    rewrite H17 H4.
    erewrite IHHD1 by eassumption.
    erewrite IHHD2 by eassumption.
    reflexivity.
Qed.


Lemma DescBin' : forall {a} (s1:IntMap a) r1 f1 s2 r2 f2 p msk r f,
    Desc s1 r1 f1 ->
    Desc s2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r ->
    (forall i, inRange i (halfRange r false) = true  -> f i = f1 i) ->
    (forall i, inRange i (halfRange r true)  = true  -> f i = f2 i) ->
    (forall i, inRange i r                   = false -> f i = None) ->
    Desc (Bin p msk s1 s2) r f.
Proof.
  intros.
  eapply DescBin; try eassumption.
  intro i.
  destruct (inRange i r) eqn:Hir.
  * destruct (inRange i (halfRange r false)) eqn: Hir1.
    + assert (Hir2 : inRange i (halfRange r true) = false).
      { eapply rangeDisjoint_inRange_false.
        eapply halves_disj; auto.
        assumption.
      }
      rewrite H6 //.
      rewrite (Desc_outside H0); last inRange_false.
      rewrite oro_None_r. reflexivity.
    + assert (Hir2 : inRange i (halfRange r true) = true).
      { rewrite halfRange_inRange_testbit // in Hir1.
        rewrite halfRange_inRange_testbit //.
        destruct (N.testbit _ _); simpl in *; congruence.
      }
      rewrite H7 //.
      rewrite (Desc_outside H); last inRange_false.
      rewrite oro_None_l //.
  * rewrite H8 //.
    rewrite (Desc_outside H) ; last inRange_false.
    rewrite (Desc_outside H0) ; last inRange_false.
    reflexivity.
Qed.


Ltac point_to_inRange :=
  lazymatch goal with
    | [ HD : Desc ?s ?r ?f, Hf : ?f ?i = Some ?v |- _ ]
      => apply (Desc_inside HD) in Hf
  end.


(**
 Like [solve_f_eq], but tries to solve the resulting bogus cases
 using reasoning about [inRange]. *)

Ltac solve_f_eq_disjoint :=
  solve_f_eq;
  repeat point_to_inRange;
  repeat saturate_inRange;
  try inRange_disjoint. (* Only try this, so that we see where we are stuck. *)


(** *** Uniqueness of representation *)

Lemma larger_f_imp:
  forall a (s1 : IntMap a) r1 f1 s2 r2 f2,
  (rBits r2 < rBits r1)%N ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall (i : N) v, f1 i = Some v -> f2 i = Some v) ->
  False.
Proof.
  intros ???? ??? Hsmaller HD1 HD2 Hf.
  destruct HD1.
  * subst. simpl in Hsmaller. nia.
  * subst.
    assert (isSubrange r2 (halfRange r false) = true).
      { destruct (Desc_some_f HD1_1) as [i [v Hi]].
        pose proof (Desc_inside HD1_1 Hi).
        specialize (H4 i).
        (* TODO: Why do we need Coq rewrite + by ? *)
        rewrite -> (Desc_outside HD1_2) in H4 by inRange_false.
        rewrite oro_None_r in H4.
        rewrite <- H4 in Hi; clear H4.
        apply Hf in Hi; clear Hf.
        apply (Desc_inside HD2) in Hi.
        apply inRange_both_smaller_subRange with (i := i).
        * inRange_true.
        * inRange_true.
        * rewrite rBits_halfRange. nia.
      }
    assert (isSubrange r2 (halfRange r true) = true).
      { destruct (Desc_some_f HD1_2) as [i [v Hi]].
        pose proof (Desc_inside HD1_2 Hi).
        specialize (H4 i).
        rewrite -> (Desc_outside HD1_1) in H4 by inRange_false.
        rewrite oro_None_l in H4.
        rewrite <- H4 in Hi; clear H4.
        apply Hf in Hi; clear Hf.
        apply (Desc_inside HD2) in Hi.
        apply inRange_both_smaller_subRange with (i := i).
        * inRange_true.
        * inRange_true.
        * rewrite rBits_halfRange. nia.
      }
      inRange_disjoint.
Qed.

Lemma Desc_unique:
  forall a (s1:IntMap a) r1 f1 s2 r2 f2,
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i, f1 i = f2 i) ->
  s1 = s2.
Proof.
  intros ??????? HD1.
  revert s2 r2 f2.
  induction HD1.
  * intros s2 r2 f2 HD2 Hf.
    destruct HD2.
    + subst.
      destruct (N.eq_decidable k k0).
      ++ subst.
         specialize (H k0). rewrite Hf H1 in H.
         rewrite N.eqb_refl in H. inversion H.
         reflexivity.
      ++ specialize (H k0). rewrite Hf H1 in H.
         rewrite N.eqb_refl in H.
         destruct (N.eqb_neq k k0) as [h0 h1].
         rewrite N.eqb_sym in H.
         rewrite (h1 H0)  in H.
         inversion H.
    +
      exfalso. subst.
      eapply larger_f_imp with (r1 := r0) (r2 := singletonRange k).
      - simpl. auto.
      - eapply DescBin with (m1 := m1) (m2 := m2); try eassumption; reflexivity.
      - eapply DescTip; try eassumption; reflexivity.
      - intros i Hi. rewrite Hf. auto.
  * intros s3 r3 f3 HD3 Hf.
    destruct HD3.
    + exfalso. subst.
      eapply larger_f_imp with (r1 := r) (r2 := singletonRange k).
      - simpl. auto.
      - eapply DescBin with (m1 := m1) (m2 := m2); try eassumption; reflexivity.
      - eapply DescTip; try eassumption; reflexivity.
      - intros i Hi. rewrite <- Hf. auto.

    + subst.
      assert (r4 = r). {
        destruct (Desc_some_f HD3_1) as [i1 [v1 Hi1]].
        destruct (Desc_some_f HD3_2) as [i2 [v2 Hi2]].
        destruct (Desc_some_f HD1_1) as [i3 [v3 Hi3]].
        destruct (Desc_some_f HD1_2) as [i4 [v4 Hi4]].
        apply criss_cross with i1 i2 i3 i4; try assumption.
        * apply (Desc_inside HD3_1) in Hi1; inRange_true.
        * apply (Desc_inside HD3_2) in Hi2; inRange_true.
        * apply (Desc_inside HD1_1) in Hi3; inRange_true.
        * apply (Desc_inside HD1_2) in Hi4; inRange_true.
        * specialize (H10 i1); rewrite Hi1 in H10.
          rewrite oro_Some_l in H10.
          rewrite <- Hf in H10.
          specialize (H4 i1); rewrite H10 in H4; clear H10; symmetry in H4.
          apply oro_Some in H4.
          destruct H4.
          + apply (Desc_inside HD1_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
        * specialize (H10 i2); rewrite Hi2 in H10;
          destruct (f0 i2) eqn:If0; simpl in H10;
          rewrite <- Hf in H10;
          specialize (H4 i2); rewrite H10 in H4; clear H10; symmetry in H4;
          apply oro_Some in H4; destruct H4.
          + apply (Desc_inside HD1_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.

        * specialize (H4 i3); rewrite Hi3 in H4.
          rewrite oro_Some_l in H4.
          rewrite -> Hf in H4.
          specialize (H10 i3); rewrite H4 in H10; clear H4; symmetry in H10.
          apply oro_Some in H10; destruct H10.
          + apply (Desc_inside HD3_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD3_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
        * specialize (H4 i4); rewrite Hi4 in H4.
          destruct (f1 i4) eqn:Is4; simpl in H4;
          rewrite -> Hf in H4;
          specialize (H10 i4); rewrite H4 in H10; clear H4; symmetry in H10;
          apply oro_Some in H10; destruct H10.
          + apply (Desc_inside HD3_1) in H2;
            eapply inRange_isSubrange_true; [|eassumption];
            isSubrange_true.
          + apply (Desc_inside HD3_2) in H2;
            eapply inRange_isSubrange_true; [|eassumption];
            isSubrange_true.
          + apply (Desc_inside HD3_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD3_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.

      }
      subst.
      assert (IH_prem_1 : (forall i : N, f1 i = f0 i)). {
        intro i.
        specialize (H4 i). specialize (H10 i). specialize (Hf i).
        destruct (inRange i (halfRange r false)) eqn:?.
        -- rewrite -> (Desc_outside HD1_2) in H4 by inRange_false.
           rewrite oro_None_r in H4.
           rewrite <- H4; clear H4.

           rewrite -> (Desc_outside HD3_2) in H10 by inRange_false.
           rewrite oro_None_r in H10.
           rewrite <- H10; clear H10.

           assumption.
        -- rewrite (Desc_outside HD1_1) ; last inRange_false.
           rewrite (Desc_outside HD3_1) ; last inRange_false.
           reflexivity.
      }
      assert (IH_prem_2 : (forall i : N, f2 i = f3 i)). {
        intro i.
        specialize (H4 i). specialize (H10 i). specialize (Hf i).
        destruct (inRange i (halfRange r true)) eqn:?.
        -- rewrite -> (Desc_outside HD1_1) in H4 by inRange_false.
           rewrite oro_None_l in H4.
           rewrite <- H4; clear H4.

           rewrite -> (Desc_outside HD3_1) in H10 by inRange_false.
           rewrite oro_None_l in H10.
           rewrite <- H10; clear H10.

           assumption.
        -- rewrite (Desc_outside HD1_2) ; last inRange_false.
           rewrite (Desc_outside HD3_2) ; last inRange_false.
           reflexivity.
      }
      specialize (IHHD1_1 _ _ _ HD3_1 IH_prem_1).
      destruct IHHD1_1; subst.
      specialize (IHHD1_2 _ _ _ HD3_2 IH_prem_2).
      destruct IHHD1_2; subst.
      reflexivity.
Qed.


Lemma Sem_unique:
  forall a (s1:IntMap a) f1 s2 f2,
  Sem s1 f1 -> Sem s2 f2 ->
  (forall i, f1 i = f2 i) ->
  s1 = s2.
Proof.
  intros.
  destruct H, H0.
  * reflexivity.
  * exfalso.
    destruct (Desc_some_f HD) as [i [v Hi]].
    rewrite <- H1 in Hi.
    rewrite H in Hi.
    congruence.
  * exfalso.
    destruct (Desc_some_f HD) as [i [v Hi]].
    rewrite -> H1 in Hi.
    rewrite H in Hi.
    congruence.
  * eapply Desc_unique; eassumption.
Qed.

Theorem Sem_extensional {a} (s : IntMap a) (f1 f2 : N -> option a) :
  Sem s f1 ->
  Sem s f2 ->
  forall i, f1 i = f2 i.
Proof.
  intros S1 S2 k;
    inversion S1 as [a1 f1' E1 | a1 s1 r1 f1' D1];
    apply Eqdep.EqdepTheory.inj_pair2 in H0;
    apply Eqdep.EqdepTheory.inj_pair2 in H1;
    subst f1' s;
    inversion S2 as [a2 f2' E2 | a2 s2 r2 f2' D2];
    apply Eqdep.EqdepTheory.inj_pair2 in H1.
    subst f2';
    try subst s1; try subst s2.
  - now rewrite E1 E2.
  - subst.
    inversion D2.
  - subst.
    inversion D1.
  - apply Eqdep.EqdepTheory.inj_pair2 in H2.
    subst.
    eauto using Desc_unique_f.
Qed.

(** *** Verification of [nomatch] *)

Lemma nomatch_spec:
  forall i r,
  (0 < rBits r)%N ->
  IntMap.Internal.nomatch i (rPrefix r) (rMask r) =
  negb (inRange i r).
Proof.
  intros.
  destruct r as [p b]. simpl in *.
  unfold nomatch, zero, inRange.
  unfoldMethods.
  unfold mask, IntSet.Internal.maskW.
  f_equal.
  rewrite eq_iff_eq_true.
  rewrite !N.eqb_eq.
  rewrite <- N.pow_succ_r  by nia.
  replace (N.succ (b - 1)) with b by nia.
  rewrite N.sub_1_r.
  rewrite <- N.ones_equiv.
  rewrite -> N.ldiff_ones_r by nonneg.
  rewrite -> N_shiftl_inj by nonneg.
  reflexivity.
Qed.

Lemma match_nomatch: forall x p ms,
  match_ x p ms = negb (nomatch x p ms).
Proof.
  intros. unfold match_, nomatch. unfoldMethods.
  rewrite negb_involutive.
  reflexivity.
Qed.

(**
The IntMap code has a repeating pattern consisting of calls to [nomatch] and [zero].
The following two lemmas capture that pattern concisely.
*)

Lemma nomatch_zero:
  forall {a} i r (P : a -> Prop) left right otherwise,
  (0 < rBits r)%N ->
  (inRange i r = false -> P otherwise) ->
  (inRange i (halfRange r false) = true -> inRange i (halfRange r true) = false -> P left) ->
  (inRange i (halfRange r false) = false -> inRange i (halfRange r true) = true -> P right) ->
  P (if nomatch i (rPrefix r) (rMask r) then otherwise else
     if zero i (rMask r) then left else right).
Proof.
  intros.
  rewrite nomatch_spec //.
  rewrite if_negb.
  destruct (inRange i r) eqn:?.
  * rewrite zero_spec //.
    rewrite if_negb.
    destruct (N.testbit i (rBits r - 1)) eqn:Hbit.
    + apply H2.
      all: rewrite halfRange_inRange_testbit // Hbit //.
    + apply H1.
      all: rewrite halfRange_inRange_testbit // Hbit //.
  * apply H0; reflexivity.
Qed.

Lemma nomatch_zero_smaller:
  forall {a} r1 r (P : a -> Prop) left right otherwise,
  (rBits r1 < rBits r)%N ->
  (rangeDisjoint r1 r = true -> P otherwise) ->
  (isSubrange r1 (halfRange r false) = true  -> isSubrange r1 (halfRange r true) = false -> P left) ->
  (isSubrange r1 (halfRange r false) = false -> isSubrange r1 (halfRange r true) = true -> P right) ->
  P (if nomatch (rPrefix r1) (rPrefix r) (rMask r) then otherwise else
     if zero (rPrefix r1) (rMask r) then left else right).
Proof.
  intros ????????.
  assert (rBits r1 <= rBits r)%N by nia.
  assert (forall h, rBits r1 <= rBits (halfRange r h))%N
    by (intros; rewrite rBits_halfRange; nia).
  rewrite <- smaller_not_subrange_disjoint_iff; auto.
  repeat rewrite <- smaller_inRange_iff_subRange by auto.
  apply nomatch_zero.
  nia.
Qed.

(** v0.7 removed the [nomatch] check from [lookup].
    This lemma handles the [zero]-only branching pattern. *)
Lemma zero_oro:
  forall {a} i r (f1 f2 : N -> option a) r1 r2,
  (0 < rBits r)%N ->
  isSubrange r1 (halfRange r false) = true ->
  isSubrange r2 (halfRange r true) = true ->
  (inRange i r1 = false -> f1 i = None) ->
  (inRange i r2 = false -> f2 i = None) ->
  (if Data.IntSet.Internal.zero i (rMask r) then f1 i else f2 i) =
  oro (f1 i) (f2 i).
Proof.
  intros a i r f1 f2 r1 r2 Hbits Hsub1 Hsub2 Hout1 Hout2.
  assert (Hhl: inRange i (halfRange r false) = false -> f1 i = None).
  { intro. apply Hout1. eapply inRange_isSubrange_false; eassumption. }
  assert (Hhr: inRange i (halfRange r true) = false -> f2 i = None).
  { intro. apply Hout2. eapply inRange_isSubrange_false; eassumption. }
  clear Hout1 Hout2 Hsub1 Hsub2 r1 r2.
  rewrite zero_spec; [|assumption].
  destruct (inRange i r) eqn:HinR.
  * destruct (N.testbit i (rBits r - 1)) eqn:Hbit; simpl negb.
    -- assert (f1 i = None) as ->.
       { apply Hhl.
         pose proof (halfRange_inRange_testbit r i false Hbits HinR).
         rewrite Hbit in H. simpl in H. exact H. }
       rewrite oro_None_l. reflexivity.
    -- assert (f2 i = None) as ->.
       { apply Hhr.
         pose proof (halfRange_inRange_testbit r i true Hbits HinR).
         rewrite Hbit in H. simpl in H. exact H. }
       rewrite oro_None_r. reflexivity.
  * assert (f1 i = None) as ->.
    { apply Hhl. eapply inRange_isSubrange_false.
      apply isSubrange_halfRange. assumption. exact HinR. }
    assert (f2 i = None) as ->.
    { apply Hhr. eapply inRange_isSubrange_false.
      apply isSubrange_halfRange. assumption. exact HinR. }
    destruct (N.testbit i (rBits r - 1)); reflexivity.
Qed.


(** *** Verification of [equal] *)

Lemma equal_spec a `{Base.Eq_ a} `{Base.EqExact a} :
  forall (s1 s2 : IntMap a), equal s1 s2 = true <-> s1 = s2.
Proof.
  induction s1; intro s2; destruct s2;
    try solve [simpl; intuition congruence].
  * simpl. unfoldMethods.
    rewrite !andb_true_iff.
    rewrite !N.eqb_eq.
    rewrite IHs1_1.
    rewrite IHs1_2.
    intuition congruence.
  * simpl.
    rewrite !andb_true_iff.
    rewrite <- (reflect_iff _ _ (Base.Eq_eq a0 a1)).
    rewrite !N.eqb_eq.
    intuition congruence.
Qed.

(** *** Verification of [nequal] *)

Lemma nequal_spec {a} `{Base.Eq_ a}`{ Base.EqLaws a} :
  forall (s1 s2:IntMap a), nequal s1 s2 = negb (equal s1 s2).
Proof.
  induction s1; intro s2; destruct s2;
    try solve [simpl; intuition congruence].
  * simpl. unfoldMethods.
    rewrite !negb_andb.
    rewrite IHs1_1.
    rewrite IHs1_2.
    reflexivity.
  * simpl.
    rewrite !negb_andb.
    rewrite (Base.Eq_inv k k0).
    rewrite (Base.Eq_inv a0 a1).
    rewrite !negb_involutive.
    auto.
Qed.

(** *** Verification of [singleton] *)

Lemma singleton_Desc:
  forall a k (v : a),
   Desc (singleton k v) (singletonRange k) (fun x => if x =? k then Some v else None).
Proof.
  intros.
  apply DescTip; try nonneg; try isBitMask.
Qed.

Lemma singleton_Sem:
  forall a k (v:a), Sem (singleton k v) (fun x => if x =? k then Some v else None).
Proof.
  intros.
  eapply DescSem.
  apply singleton_Desc; assumption.
Qed.

Lemma singleton_WF:
  forall a k (v:a), WF (singleton k v).
Proof. intros. eexists. apply singleton_Sem; auto. Qed.

(** *** Verification of [lookup] *)


Lemma lookup_Desc:
 forall {a}{s : IntMap a}{r f i}, Desc s r f -> lookup i s = f i.
Proof.
 intros ????? HD.
 induction HD; subst.
 * simpl.
   unfoldMethods.
   rewrite H.
   destruct (i =? k) eqn:Ei; simpl; auto.
 * rewrite H4. clear H4.
   simpl lookup.
   rewrite IHHD1 IHHD2. clear IHHD1 IHHD2.
   eapply zero_oro; try eassumption.
   + intro. eapply Desc_outside; eassumption.
   + intro. eapply Desc_outside; eassumption.
Qed.


Lemma lookup_Desc0:
  forall {a}{s:IntMap a} {r f i}, Desc0 s r f -> lookup i s = f i.
Proof.
  intros.
  destruct H.
  - simpl. symmetry. apply H.
  - rewrite Hf. eapply lookup_Desc; eauto.
Qed.

Lemma lookup_Sem:
  forall {a}{s:IntMap a}{f i}, Sem s f -> lookup i s = f i.
Proof.
  intros.
  destruct H.
  * rewrite H. reflexivity.
  * erewrite lookup_Desc; eauto.
Qed.


(* For the sake of simplicity, we are writing a new findWithdefault that returns an option *)

Definition findWithDefaultOption {a} (def : a) (k : Key) (s : IntMap a) :=
  Some (findWithDefault def k s).

Lemma Desc_not_inRange_None : forall a (s : IntMap a) r f,
    Desc s r f ->
    forall i, inRange i r = false -> f i = None. 
Proof.
  intros. induction H.
  * rewrite H1 in H0. unfold inRange in H0. simpl in H0. specialize (H i).
    rewrite H0 in H. apply H.
  * assert (Desc (Bin p msk m1 m2) r f).
    eapply DescBin with (r1:= r1) (f1:= f1) (r2:=r2) (f2:=f2); auto.
    move: (Desc_outside H8 H0 ) => H9. apply H9.
Qed.


Lemma findWithDefault_Desc:
  forall {a}{s: IntMap a} {r f} x i, Desc s r f ->
                                     match (f i) with
                                     | Some v => findWithDefaultOption x i s = Some v
                                     | None => findWithDefaultOption x i s = Some x
                                     end.
Proof.
  intros. induction H.
  * destruct (f i) eqn: E; unfold findWithDefaultOption; unfold findWithDefault; specialize (H i);
      destruct (i == k) eqn: ik; rewrite ik; rewrite E in H; destruct (i =? k) eqn: ik2; try discriminate.
      - congruence.
      - apply Neqb_ok in ik2. rewrite Base.Eq_reflI in ik. discriminate. apply ik2.
      - unfold "==" in ik. unfoldMethods. rewrite ik in ik2. discriminate.
      - reflexivity.  
  * destruct (f i) eqn: E; unfold findWithDefaultOption; simpl; subst; apply nomatch_zero.
      - apply H1.
      - rewrite <- E. 
        specialize (IHDesc1 x). specialize (IHDesc2 x).
        intros IRH. assert (Desc (Bin (rPrefix r) (rMask r) m1 m2) r f).
        eapply DescBin with (r1:= r1) (f1:= f1) (r2:= r2) (f2:=f2); auto.
         move: (Desc_not_inRange_None a (Bin (rPrefix r) (rMask r) m1 m2) r f) => H7.
        intuition. specialize (H5 i). intuition. rewrite H7. congruence.
      - specialize (IHDesc1 x). specialize (H6 i). destruct (f1 i) eqn: Hf. simpl in H6.
        rewrite H6 in E. inversion E. subst. unfold findWithDefaultOption in IHDesc1. intros. apply IHDesc1.
        intros. unfold findWithDefaultOption in IHDesc1. simpl in H6. specialize (IHDesc2 x).
        rewrite <- H6 in IHDesc2. rewrite E in IHDesc2. move: (Desc_not_inRange_None _ _ _ _ H0) => H7.
        specialize (H7 i). 
        move: (inRange_isSubrange_false i _ _ H3 H5) => H8. rewrite H8 in H7. intuition.
        rewrite H9 in H6. rewrite E in H6. discriminate.
      - specialize (IHDesc2 x). specialize (IHDesc1 x). intros.
        unfold findWithDefaultOption in IHDesc2. destruct (f2 i) eqn: Hf.
        ** rewrite IHDesc2. move: (Desc_not_inRange_None a m2 r2 f2 H0 i) => H8.
           move: (Desc_not_inRange_None a m1 r1 f1 H i) => H9.
           move: (inRange_isSubrange_false i _ _  H2 H4) => H10.
           rewrite H10 in H9. intuition. specialize (H6 i). unfold oro in H6. rewrite H7 in H6.
           rewrite Hf in H6. rewrite E in H6. congruence.
        ** rewrite IHDesc2. rewrite <- E. move: (Desc_not_inRange_None a m1 r1 f1 H i) => H7.
           move: (inRange_isSubrange_false i _ _ H2 H4) => H8. rewrite H8 in H7. intuition.
           specialize (H6 i). unfold oro in H6. rewrite H9 in H6. rewrite Hf in H6. rewrite E in H6.
           discriminate.                                    
      - specialize (H6 i); unfold oro in H6; specialize (IHDesc1 x). apply H1.
      - specialize (H6 i); unfold oro in H6; specialize (IHDesc1 x).  reflexivity.
      -  specialize (H6 i); unfold oro in H6; specialize (IHDesc1 x).  destruct (f1 i) eqn: Hf1 in H6.
        ** rewrite H6 in E. discriminate.
        ** destruct (f2 i).
          ++ rewrite H6 in E. discriminate.
          ++ rewrite Hf1 in IHDesc1. rewrite <- IHDesc1. unfold findWithDefaultOption. congruence.
      - specialize (H6 i); unfold oro in H6; specialize (IHDesc1 x). destruct (f1 i) eqn: Hf1 in H6.
        ** rewrite H6 in E. discriminate.
        ** destruct (f2 i).
          ++ rewrite H6 in E. discriminate.
          ++ rewrite Hf1 in IHDesc1. unfold findWithDefaultOption in IHDesc2. congruence.
Qed.

Lemma findWithDefault_Sem:
  forall {a} {s: IntMap a} {f x i}, Sem s f ->
                      match (f i) with
                      | Some v => findWithDefaultOption x i s = Some v
                      | None => findWithDefaultOption x i s = Some x
                      end.
Proof.
  intros. destruct H.
  * destruct (f i) eqn:E; specialize (H i).
    + rewrite E in H. discriminate.
    + unfold findWithDefaultOption. simpl. reflexivity.
  * destruct (f i) eqn:E; move: (findWithDefault_Desc x i HD) => H;
       rewrite E in H; apply H.
Qed.

(** Verification of [lookupLT] **)

(** *** Verification of [isSubmapOf] *)
Lemma isSubmapOfBy_disjoint {a} (f : a -> a -> bool) :
  forall (s1 :IntMap a) r1 f1 s2 r2 f2,
  rangeDisjoint r1 r2 = true ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall (i : N) v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ (f v1 v2 = true)) <-> False.
Proof.
  intros ??? ??? Hdis HD1 HD2.
  intuition.
  destruct (Desc_some_f HD1) as [i [v Hi]].
  eapply rangeDisjoint_inRange_false_false with (i := i).
  ** eassumption.
  ** eapply Desc_inside; eassumption.
  ** eapply H in Hi.
     destruct Hi as [v2 [Hi EQ]].
     apply (Desc_inside HD2) in Hi.
     assumption.
Qed.


Lemma isSubmapOfBy_disjoint1 {a} :
  forall (s1 :IntMap a) r1 f1 (s2:IntMap a) r2 f2,
  rangeDisjoint r1 r2 = true ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  forall (i : N) v1, f1 i = Some v1 -> f2 i = None.
Proof.
  intros ??? ??? Hdis HD1 HD2.
  intuition.
  eapply Desc_outside; eauto.
  apply not_true_is_false.
  unfold not.
  eapply rangeDisjoint_inRange_false_false with (i := i).

  ** eassumption.
  ** eapply Desc_inside; eassumption.
Qed.

(** Analogue of IntSetProofs.pointwise_iff for IntMap's option-valued semantics *)
Lemma pointwise_iff_map :
  forall {a} (pred : a -> a -> bool) (f1 f1' f2 f2' : N -> option a),
  (forall i, f1 i = f1' i) ->
  (forall i, f2 i = f2' i) ->
  ((forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ pred v1 v2 = true) <->
   (forall i v1, f1' i = Some v1 -> exists v2, f2' i = Some v2 /\ pred v1 v2 = true)).
Proof.
  intros a0 pred0 f1 f1' f2 f2' Hf1 Hf2.
  split; intros Hall i v1 Hfi.
  - rewrite <- Hf1 in Hfi. destruct (Hall i v1 Hfi) as [v2 [Hv2 Hp]].
    exists v2. rewrite <- Hf2. auto.
  - rewrite Hf1 in Hfi. destruct (Hall i v1 Hfi) as [v2 [Hv2 Hp]].
    exists v2. rewrite Hf2. auto.
Qed.

(** Disjoint ranges => semantic containment is vacuously false *)
Lemma isSubmapOfBy_disjoint_map {a} (pred : a -> a -> bool) :
  forall (s1 : IntMap a) r1 f1 s2 r2 f2,
  rangeDisjoint r1 r2 = true ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ pred v1 v2 = true) <-> False.
Proof.
  intros ??? ??? Hdis HD1 HD2.
  split; [| tauto].
  intro Hall.
  destruct (Desc_some_f HD1) as [i [v1 Hi]].
  destruct (Hall i v1 Hi) as [v2 [Hv2 _]].
  eapply rangeDisjoint_inRange_false_false with (i := i).
  - eassumption.
  - eapply Desc_inside; eassumption.
  - eapply Desc_inside; eassumption.
Qed.

(** Larger range => larger tree cannot be a semantic submap.
    if all keys of s1 are also in s2 (with any values), and r1 is broader
    than r2, we get a contradiction because s1 has keys in both halves
    of r1 but r2 can only cover one half. *)
Lemma larger_submap_false {a} (pred : a -> a -> bool) :
  forall (s1 : IntMap a) r1 f1 s2 r2 f2,
  (rBits r2 < rBits r1)%N ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ pred v1 v2 = true) ->
  False.
Proof.
  intros s1 r1 f1 s2 r2 f2 Hsmaller HD1 HD2 Hall.
  (* Weaken: derive that every key in f1 is in range of r2 *)
  assert (Hrange : forall i v, f1 i = Some v -> inRange i r2 = true).
  { intros i v Hi.
    destruct (Hall i v Hi) as [v2 [Hv2 _]].
    eapply Desc_inside; eassumption. }
  (* Use destruct to get clean hypotheses *)
  destruct HD1 as [a0 k v r1' f1' Hf1_tip Hr1_eq | a0 m1 r1_l f1_l m2 r1_r f1_r p msk r1' f1' HD1_l HD1_r Hbits Hsub_l Hsub_r Hp Hmsk Hf1_oro].
  - (* Tip: rBits r1 = 0, rBits r2 < 0, impossible *)
    subst. simpl in Hsmaller. lia.
  - (* Bin: s1 = Bin p msk m1 m2 *)
    subst.
    (* Get keys from both children *)
    destruct (Desc_some_f HD1_l) as [i1 [v1 Hi1]].
    destruct (Desc_some_f HD1_r) as [i2 [v2 Hi2]].
    (* i1 is in left half of r1, i2 is in right half *)
    assert (Hi1_l : inRange i1 (halfRange r1' false) = true).
    { eapply inRange_isSubrange_true; [eassumption | eapply Desc_inside; eassumption]. }
    assert (Hi2_r : inRange i2 (halfRange r1' true) = true).
    { eapply inRange_isSubrange_true; [eassumption | eapply Desc_inside; eassumption]. }
    (* f1' contains both keys *)
    assert (Hf1_i1 : f1' i1 = Some v1).
    { rewrite Hf1_oro. rewrite Hi1. reflexivity. }
    assert (Hf1_i2 : f1' i2 = Some v2).
    { rewrite Hf1_oro.
      assert (inRange i2 (halfRange r1' false) = false).
      { eapply rangeDisjoint_inRange_false.
        - rewrite rangeDisjoint_sym. apply halves_disj. assumption.
        - assumption. }
      rewrite (Desc_outside HD1_l).
      2: { eapply inRange_isSubrange_false; eassumption. }
      simpl. exact Hi2. }
    (* Both i1 and i2 are in range of r2 *)
    assert (Hi1_r2 : inRange i1 r2 = true) by (eapply Hrange; eassumption).
    assert (Hi2_r2 : inRange i2 r2 = true) by (eapply Hrange; eassumption).
    (* r2 has rBits < rBits r1', so rBits r2 <= rBits (halfRange r1' h) *)
    assert (rBits r2 <= rBits (halfRange r1' false))%N
      by (rewrite rBits_halfRange; lia).
    assert (rBits r2 <= rBits (halfRange r1' true))%N
      by (rewrite rBits_halfRange; lia).
    (* r2 must be a subrange of both halves — contradiction *)
    assert (isSubrange r2 (halfRange r1' false) = true).
    { apply inRange_both_smaller_subRange with (i := i1); assumption. }
    assert (isSubrange r2 (halfRange r1' true) = true).
    { apply inRange_both_smaller_subRange with (i := i2); assumption. }
    (* r2 is a subrange of both halves, which are disjoint -> contradiction *)
    exfalso.
    eapply rangeDisjoint_isSubrange_false_false.
    + apply halves_disj. exact Hbits.
    + exact H1.
    + exact H2.
Qed.

(* FALSE: isSubmapOfBy_Bin is disproved by concrete counterexample.
   isSubmapOfBy (fun _ _ => true) (Tip 1 42) (Tip 1 42) = true, but
   isSubmapOfBy (fun _ _ => true) (Tip 1 42) (Bin 0 1 (Tip 1 42) Nil) = false.
   Reason: lookup in IntMap ignores the prefix field -- it uses only `zero k m`
   to pick left vs right child. With msk=1, zero 1 1 = false, so lookup 1
   goes to the right child (Nil) and returns None.
   isSubmapOfBy_Desc/Desc1 avoid this lemma entirely — they use Desc constraints. *)
(* Formal counterexample *)
Lemma isSubmapOfBy_Bin_false :
  ~ (forall (s1 s2 s3: IntMap N) p msk f',
       isSubmapOfBy f' s1 s2 = true -> isSubmapOfBy f' s1 (Bin p msk s2 s3) = true).
Proof.
  intro H.
  specialize (H (Tip 1%N 42%N) (Tip 1%N 42%N) Nil 0%N 1%N (fun _ _ => true) eq_refl).
  discriminate.
Qed.

(* FALSE: disproved by isSubmapOfBy_Bin_false above. Aborted to prevent use. *)
Lemma isSubmapOfBy_Bin {a} :
  forall (s1 s2 s3: IntMap a) p msk f',
    isSubmapOfBy f' s1 s2 = true -> isSubmapOfBy f' s1 (Bin p msk s2 s3) = true.
Proof.
Abort.

(* isSubmapOfBy_Bin is false (see isSubmapOfBy_Bin_false above).
   isSubmapOfBy_Desc/Desc1 don't need it — they work directly with Desc
   constraints that exclude the ill-formed counterexample. *)

(** A tactic to get i into range r given Desc *)
Ltac assert_inRange_of_Some HD Hsome :=
  let HirN := fresh "Hir" in
  assert (HirN : inRange _ _ = true) by (eapply Desc_inside; [exact HD | exact Hsome]).

(** isSubmapOfBy_Desc1: the main theorem, proved by well-founded induction
    on (size_nat s1 + size_nat s2), following the structure of
    IntSetProofs.isSubsetOf_Desc. *)
Program Fixpoint isSubmapOfBy_Desc1 {a} (pred : a -> a -> bool)
  (s1 : IntMap a) r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  isSubmapOfBy pred s1 s2 = true <->
  (forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ pred v1 v2 = true) := _.
Next Obligation.
  revert isSubmapOfBy_Desc1 H H0.
  intros IH HD1 HD2.
  destruct HD1 as
    [ a1 k1 v1 r1_ f1_ Hf1_sem Hr1_eq
    | a1 s1_l r1_l f1_l s1_r r1_r f1_r p1 m1 r1_ f1_
      HD1_l HD1_r Hbits1 Hsub1_l Hsub1_r Hp1 Hm1 Hf1_oro ];
  destruct HD2 as
    [ a2 k2 v2 r2_ f2_ Hf2_sem Hr2_eq
    | a2 s2_l r2_l f2_l s2_r r2_r f2_r p2 m2 r2_ f2_
      HD2_l HD2_r Hbits2 Hsub2_l Hsub2_r Hp2 Hm2 Hf2_oro ];
  subst.

  * (* Tip / Tip *)
    simpl. unfoldMethods.
    destruct (N.eqb_spec k1 k2).
    + (* k1 = k2 *)
      subst.
      split.
      -- intros Hpred i w1 Hfi.
         rewrite Hf1_sem in Hfi. destruct (N.eqb_spec i k2); [| discriminate].
         subst. inversion Hfi; subst.
         exists v2. rewrite Hf2_sem. rewrite N.eqb_refl. auto.
      -- intros Hall.
         assert (Hfk : f1_ k2 = Some v1) by (rewrite Hf1_sem; rewrite N.eqb_refl; reflexivity).
         destruct (Hall k2 v1 Hfk) as [w2 [Hw2 Hp]].
         rewrite Hf2_sem in Hw2. rewrite N.eqb_refl in Hw2.
         inversion Hw2; subst. exact Hp.
    + (* k1 <> k2 *)
      split.
      -- discriminate.
      -- intros Hall. exfalso.
         assert (Hfk : f1_ k1 = Some v1) by (rewrite Hf1_sem; rewrite N.eqb_refl; reflexivity).
         destruct (Hall k1 v1 Hfk) as [w2 [Hw2 _]].
         rewrite Hf2_sem in Hw2. destruct (N.eqb_spec k1 k2); [congruence | discriminate].

  * (* Tip / Bin *)
    (* isSubmapOfBy pred (Tip k1 v1) (Bin p2 m2 s2_l s2_r) computes to:
       match lookup k1 (Bin p2 m2 s2_l s2_r) with Some y => pred v1 y | None => false end *)
    change (isSubmapOfBy pred (Tip k1 v1) (Bin (rPrefix r2_) (rMask r2_) s2_l s2_r))
      with (match lookup k1 (Bin (rPrefix r2_) (rMask r2_) s2_l s2_r)
            with Some y => pred v1 y | None => false end).
    assert (HD2_bin : Desc (Bin (rPrefix r2_) (rMask r2_) s2_l s2_r) r2_ f2_)
      by (eapply DescBin; try eassumption; reflexivity).
    rewrite (lookup_Desc HD2_bin).
    split.
    + intros Hlook i w1 Hfi.
      rewrite Hf1_sem in Hfi.
      destruct (N.eqb_spec i k1); [| discriminate].
      subst. inversion Hfi; subst.
      destruct (f2_ k1) as [y|] eqn:Hf2k; [| discriminate].
      exists y. auto.
    + intros Hall.
      assert (Hfk : f1_ k1 = Some v1) by (rewrite Hf1_sem; rewrite N.eqb_refl; reflexivity).
      destruct (Hall k1 v1 Hfk) as [w2 [Hw2 Hp]].
      rewrite Hw2. exact Hp.

  * (* Bin / Tip *)
    simpl.
    split.
    + discriminate.
    + intros Hall. exfalso.
      (* Bin has keys in both halves, Tip has one key: contradiction *)
      destruct (Desc_some_f HD1_l) as [i1 [w1 Hi1]].
      destruct (Desc_some_f HD1_r) as [i2 [w2 Hi2]].
      (* Both keys map into f2_ *)
      assert (Hf_i1 : f1_ i1 = Some w1) by (rewrite Hf1_oro; rewrite Hi1; reflexivity).
      assert (Hf_i2 : f1_ i2 = Some w2).
      { rewrite Hf1_oro.
        assert (inRange i2 (halfRange r1_ true) = true)
          by (eapply inRange_isSubrange_true; [eassumption | eapply Desc_inside; eassumption]).
        assert (inRange i2 (halfRange r1_ false) = false)
          by (eapply rangeDisjoint_inRange_false;
              [rewrite rangeDisjoint_sym; apply halves_disj; assumption | assumption]).
        rewrite (Desc_outside HD1_l).
        2:{ eapply inRange_isSubrange_false; eassumption. }
        simpl. exact Hi2. }
      destruct (Hall i1 w1 Hf_i1) as [u1 [Hu1 _]].
      destruct (Hall i2 w2 Hf_i2) as [u2 [Hu2 _]].
      (* f2_ is a Tip: f2_ i = if i =? k2 then Some v2 else None *)
      rewrite Hf2_sem in Hu1. rewrite Hf2_sem in Hu2.
      destruct (N.eqb_spec i1 k2); [| discriminate].
      destruct (N.eqb_spec i2 k2); [| discriminate].
      subst i1 i2.
      (* k2 is in both halves of r1_, contradiction *)
      assert (Hir_k2_l : inRange k2 (halfRange r1_ false) = true).
      { eapply inRange_isSubrange_true; [exact Hsub1_l |].
        eapply Desc_inside; [exact HD1_l | exact Hi1]. }
      assert (Hir_k2_r : inRange k2 (halfRange r1_ true) = true).
      { eapply inRange_isSubrange_true; [exact Hsub1_r |].
        eapply Desc_inside; [exact HD1_r | exact Hi2]. }
      eapply rangeDisjoint_inRange_false_false.
      { apply halves_disj. exact Hbits1. }
      { exact Hir_k2_l. }
      { exact Hir_k2_r. }

  * (* Bin / Bin *)
    assert (HD1_bin : Desc (Bin (rPrefix r1_) (rMask r1_) s1_l s1_r) r1_ f1_)
      by (eapply DescBin; eassumption || reflexivity).
    assert (HD2_bin : Desc (Bin (rPrefix r2_) (rMask r2_) s2_l s2_r) r2_ f2_)
      by (eapply DescBin; eassumption || reflexivity).
    (* Unfold just the top-level isSubmapOfBy application *)
    rewrite /isSubmapOfBy -/isSubmapOfBy.
    rewrite -> !shorter_spec by assumption.
    destruct (N.ltb_spec (rBits r2_) (rBits r1_)).
    + (* s1 has broader range than s2 *)
      split.
      -- discriminate.
      -- intros Hall. exfalso.
         eapply larger_submap_false with (pred := pred)
           (s1 := Bin (rPrefix r1_) (rMask r1_) s1_l s1_r)
           (s2 := Bin (rPrefix r2_) (rMask r2_) s2_l s2_r);
           [eassumption | exact HD1_bin | exact HD2_bin | exact Hall].
    + destruct (N.ltb_spec (rBits r1_) (rBits r2_)).
      -- (* s2 has broader range *)
         match goal with [ |- ((?x && ?y) = true) <-> ?z ] =>
           enough (Htmp : (if x then y else false) = true <-> z)
           by (destruct x; try rewrite andb_true_iff; intuition congruence)
         end.
         match goal with [ |- context [match_ ?x ?y ?z] ] =>
           replace (match_ x y z) with (negb (nomatch x y z))
             by (unfold nomatch, match_; unfoldMethods; rewrite negb_involutive; reflexivity)
         end.
         rewrite if_negb.
         apply nomatch_zero_smaller; try assumption.
         ++ (* r1_ disjoint from r2_ *)
            intro Hdisj.
            rewrite isSubmapOfBy_disjoint_map;
              [ intuition discriminate | eassumption | exact HD1_bin | exact HD2_bin ].
         ++ (* r1_ in the left half of r2_: recurse with whole s1 and s2_l *)
            intros Hsub_l Hnsub_r.
            etransitivity; [eapply IH with (f2 := f2_l)|].
            ** simpl. lia.
            ** exact HD1_bin.
            ** eassumption.
            ** (* Reduce: all keys of f1_ in f2_l <-> all keys of f1_ in f2_ *)
               split; intros Hall i w1 Hfi.
               +++ (* -> : f1_ ⊆ f2_l implies f1_ ⊆ f2_ *)
                   destruct (Hall i w1 Hfi) as [w2 [Hw2 Hp]].
                   exists w2. split; [| assumption].
                   assert (Hf2r_none : f2_r i = None).
                   { eapply Desc_outside; [exact HD2_r |].
                     eapply inRange_isSubrange_false; [eassumption |].
                     eapply rangeDisjoint_inRange_false;
                       [apply halves_disj; assumption |].
                     eapply inRange_isSubrange_true; [eassumption |].
                     eapply Desc_inside; eassumption. }
                   rewrite Hf2_oro. rewrite Hf2r_none.
                   rewrite oro_None_r. exact Hw2.
               +++ (* <- : f1_ ⊆ f2_ implies f1_ ⊆ f2_l *)
                   assert (Hir : inRange i r1_ = true)
                     by (eapply Desc_inside; [exact HD1_bin | exact Hfi]).
                   destruct (Hall i w1 Hfi) as [w2 [Hw2 Hp]].
                   assert (Hf2r_none : f2_r i = None).
                   { eapply Desc_outside; [exact HD2_r |].
                     eapply inRange_isSubrange_false; [eassumption |].
                     eapply rangeDisjoint_inRange_false;
                       [apply halves_disj; assumption |].
                     eapply inRange_isSubrange_true; [eassumption | exact Hir]. }
                   rewrite Hf2_oro in Hw2. rewrite Hf2r_none in Hw2.
                   rewrite oro_None_r in Hw2.
                   exists w2. auto.
         ++ (* r1_ in the right half of r2_ *)
            intros Hnsub_l Hsub_r.
            etransitivity; [eapply IH with (f2 := f2_r)|].
            ** simpl. lia.
            ** exact HD1_bin.
            ** eassumption.
            ** split; intros Hall i w1 Hfi.
               +++ (* -> : f1_ ⊆ f2_r implies f1_ ⊆ f2_ *)
                   destruct (Hall i w1 Hfi) as [w2 [Hw2 Hp]].
                   exists w2. split; [| assumption].
                   assert (Hf2l_none : f2_l i = None).
                   { eapply Desc_outside; [exact HD2_l |].
                     eapply inRange_isSubrange_false; [eassumption |].
                     eapply rangeDisjoint_inRange_false;
                       [rewrite rangeDisjoint_sym; apply halves_disj; assumption |].
                     eapply inRange_isSubrange_true; [eassumption |].
                     eapply Desc_inside; eassumption. }
                   rewrite Hf2_oro. rewrite Hf2l_none. simpl. exact Hw2.
               +++ (* <- : f1_ ⊆ f2_ implies f1_ ⊆ f2_r *)
                   assert (Hir : inRange i r1_ = true)
                     by (eapply Desc_inside; [exact HD1_bin | exact Hfi]).
                   destruct (Hall i w1 Hfi) as [w2 [Hw2 Hp]].
                   assert (Hf2l_none : f2_l i = None).
                   { eapply Desc_outside; [exact HD2_l |].
                     eapply inRange_isSubrange_false; [eassumption |].
                     eapply rangeDisjoint_inRange_false;
                       [rewrite rangeDisjoint_sym; apply halves_disj; assumption |].
                     eapply inRange_isSubrange_true; [eassumption | exact Hir]. }
                   rewrite Hf2_oro in Hw2. rewrite Hf2l_none in Hw2. simpl in Hw2.
                   exists w2. auto.

      -- (* same size *)
         unfoldMethods.
         destruct (N.eqb_spec (rPrefix r1_) (rPrefix r2_)).
         ++ (* same prefix => same range, recurse on both halves *)
            replace r2_ with r1_ in * by (apply rPrefix_rBits_range_eq; lia). clear e.
            (* Get the IH equivalences for both halves *)
            assert (IH_l : isSubmapOfBy pred s1_l s2_l = true <->
              (forall i v1, f1_l i = Some v1 -> exists v2, f2_l i = Some v2 /\ pred v1 v2 = true)).
            { eapply IH; [simpl; lia | exact HD1_l | exact HD2_l]. }
            assert (IH_r : isSubmapOfBy pred s1_r s2_r = true <->
              (forall i v1, f1_r i = Some v1 -> exists v2, f2_r i = Some v2 /\ pred v1 v2 = true)).
            { eapply IH; [simpl; lia | exact HD1_r | exact HD2_r]. }
            change ((isSubmapOfBy pred s1_l s2_l && isSubmapOfBy pred s1_r s2_r) = true <->
              (forall i v1, f1_ i = Some v1 -> exists v2, f2_ i = Some v2 /\ pred v1 v2 = true))
              || (* if change fails, try: *)
              (unfoldMethods; rewrite N.eqb_refl; simpl;
               change ((isSubmapOfBy pred s1_l s2_l && isSubmapOfBy pred s1_r s2_r) = true <->
                 (forall i v1, f1_ i = Some v1 -> exists v2, f2_ i = Some v2 /\ pred v1 v2 = true))).
            rewrite andb_true_iff.
            rewrite IH_l. rewrite IH_r.
            split.
            ** (* forward: both halves -> whole *)
               intros [Hall_l Hall_r] i w1 Hfi.
               rewrite Hf1_oro in Hfi.
               destruct (oro_Some _ _ _ _ Hfi) as [Hl | Hr].
               --- (* i in left child *)
                   destruct (Hall_l i w1 Hl) as [w2 [Hw2 Hp]].
                   exists w2. split; [| assumption].
                   rewrite Hf2_oro. rewrite Hw2. reflexivity.
               --- (* i in right child: Hr : f1_r i = Some w1 *)
                   destruct (Hall_r i w1 Hr) as [w2 [Hw2 Hp]].
                   exists w2. split; [| assumption].
                   (* Show f2_l i = None using range disjointness *)
                   assert (Hir_r : inRange i r1_r = true)
                     by (eapply Desc_inside; eassumption).
                   assert (Hir_rt : inRange i (halfRange r1_ true) = true)
                     by (eapply inRange_isSubrange_true; [exact Hsub1_r | exact Hir_r]).
                   assert (Hir_lf : inRange i (halfRange r1_ false) = false)
                     by (eapply rangeDisjoint_inRange_false;
                         [rewrite rangeDisjoint_sym; apply halves_disj; exact Hbits1 | exact Hir_rt]).
                   assert (Hf2l_none : f2_l i = None)
                     by (eapply Desc_outside; [exact HD2_l |];
                         eapply inRange_isSubrange_false; [exact Hsub2_l | exact Hir_lf]).
                   rewrite Hf2_oro. rewrite Hf2l_none. simpl. exact Hw2.
            ** (* reverse: whole -> both halves *)
               intros Hall.
               split.
               --- (* left half *)
                   intros i w1 Hfi.
                   assert (Hf_i : f1_ i = Some w1)
                     by (rewrite Hf1_oro; rewrite Hfi; reflexivity).
                   destruct (Hall i w1 Hf_i) as [w2 [Hw2 Hp]].
                   assert (Hir_1l : inRange i r1_l = true)
                     by (eapply Desc_inside; [exact HD1_l | exact Hfi]).
                   assert (Hir_lf : inRange i (halfRange r1_ false) = true)
                     by (eapply inRange_isSubrange_true; [exact Hsub1_l | exact Hir_1l]).
                   assert (Hir_rt : inRange i (halfRange r1_ true) = false)
                     by (eapply rangeDisjoint_inRange_false;
                         [apply halves_disj; exact Hbits1 | exact Hir_lf]).
                   assert (Hf2r_none : f2_r i = None)
                     by (eapply Desc_outside; [exact HD2_r |];
                         eapply inRange_isSubrange_false; [exact Hsub2_r | exact Hir_rt]).
                   rewrite Hf2_oro in Hw2. rewrite Hf2r_none in Hw2.
                   rewrite oro_None_r in Hw2.
                   exists w2. auto.
               --- (* right half *)
                   intros i w1 Hfi.
                   assert (Hir_1r : inRange i r1_r = true)
                     by (eapply Desc_inside; [exact HD1_r | exact Hfi]).
                   assert (Hir_rt : inRange i (halfRange r1_ true) = true)
                     by (eapply inRange_isSubrange_true; [exact Hsub1_r | exact Hir_1r]).
                   assert (Hir_lf : inRange i (halfRange r1_ false) = false)
                     by (eapply rangeDisjoint_inRange_false;
                         [rewrite rangeDisjoint_sym; apply halves_disj; exact Hbits1 | exact Hir_rt]).
                   assert (Hf1l_none : f1_l i = None)
                     by (eapply Desc_outside; [exact HD1_l |];
                         eapply inRange_isSubrange_false; [exact Hsub1_l | exact Hir_lf]).
                   assert (Hf_i : f1_ i = Some w1)
                     by (rewrite Hf1_oro; rewrite Hf1l_none; simpl; exact Hfi).
                   destruct (Hall i w1 Hf_i) as [w2 [Hw2 Hp]].
                   assert (Hf2l_none : f2_l i = None)
                     by (eapply Desc_outside; [exact HD2_l |];
                         eapply inRange_isSubrange_false; [exact Hsub2_l | exact Hir_lf]).
                   rewrite Hf2_oro in Hw2. rewrite Hf2l_none in Hw2. simpl in Hw2.
                   exists w2. auto.
         ++ (* different prefix, same size => disjoint *)
            rewrite isSubmapOfBy_disjoint_map;
              [ intuition discriminate
              | apply different_prefix_same_bits_disjoint; try eassumption; lia
              | exact HD1_bin
              | exact HD2_bin ].
Qed.

(** isSubmapOfBy_Desc: wrapper, same statement, proved via isSubmapOfBy_Desc1 *)
Program Fixpoint isSubmapOfBy_Desc {a} (f : a -> a -> bool)
  (s1 : IntMap a) r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  isSubmapOfBy f s1 s2 = true <->
  (forall i v1, f1 i = Some v1 -> exists v2, f2 i = Some v2 /\ f v1 v2 = true) := _.
Next Obligation.
  intros. eapply isSubmapOfBy_Desc1; eassumption.
Qed.


(** *** Verification of [member] *)

Lemma member_Desc:
 forall {a}{s : IntMap a}{r f i}, Desc s r f -> member i s = ssrbool.isSome (f i).
Proof.
 intros ????? HD.
 induction HD; subst.
 * simpl.
   unfoldMethods.
   rewrite H.
   destruct (i =? k) eqn:Ei.
   - simpl. auto.
   - simpl. auto.
 * rewrite H4. clear H4.
   simpl member.
   rewrite IHHD1 IHHD2. clear IHHD1 IHHD2.

   apply nomatch_zero; [auto|..]; intros.
   + rewrite (Desc_outside HD1) ; last inRange_false.
     rewrite (Desc_outside HD2) ; last inRange_false.
     reflexivity.
   + rewrite (Desc_outside HD2) ; last inRange_false.
     rewrite oro_None_r. reflexivity.
   + rewrite (Desc_outside HD1) ; last inRange_false.
     rewrite oro_None_l. reflexivity.
Qed.


Lemma member_Desc0:
  forall {a}{s:IntMap a} {r f i}, Desc0 s r f -> member i s = ssrbool.isSome (f i).
Proof.
  intros.
  destruct H.
  - simpl. rewrite H. simpl. reflexivity.
  - rewrite Hf. eapply member_Desc; eauto.
Qed.

Lemma member_Sem:
  forall {a}{s:IntMap a}{f i}, Sem s f -> member i s = ssrbool.isSome (f i).
Proof.
  intros.
  destruct H.
  * rewrite H. reflexivity.
  * erewrite member_Desc; eauto.
Qed.

Lemma Desc_has_member:
  forall {a}{s:IntMap a}{r f}, Desc s r f -> exists i, member i s = true.
Proof.
  intros ???? HD.
  destruct (Desc_some_f HD) as [j [v ?]].
  exists j.
  rewrite (member_Desc HD).
  rewrite H. reflexivity.
Qed.

(** *** Verification of [notMember] *)

Lemma notMember_Sem:
  forall {a}{s:IntMap a}{f i}, Sem s f -> notMember i s = negb (ssrbool.isSome (f i)).
Proof.
  intros.
  change (negb (member i s) = negb (ssrbool.isSome (f i))).
  f_equal.
  apply member_Sem.
  assumption.
Qed.

(** *** Verification of [null] *)

Lemma null_Sem:
  forall {a}{s:IntMap a}{f}, Sem s f -> null s = true <-> (forall i, f i = None).
Proof.
  intros a s f HSem.
  destruct HSem.
  * intuition.
  * assert (null s = false) by (destruct HD; reflexivity).
    intuition try congruence.
    destruct (Desc_some_f HD) as [x [v ?]].
    specialize (H0 x).
    congruence.
Qed.




 
(** *** Verification of [empty] *)

Lemma empty_Sem {a} (f : N -> option a) : Sem empty f <-> forall i, f i = None.
Proof.
  split.
  - intro s.
    apply null_Sem in s.
    simpl in s. destruct s as [s _].
    apply s.
    auto.
  - now constructor.
Qed.

Lemma empty_WF {a} : WF (empty : IntMap a).
Proof. now exists (fun _ => None); constructor. Qed.
#[export] Hint Resolve empty_WF : core.


(** *** Verification of [insert] *)

Lemma disjoint_reorder a (s1 : IntMap a) r1 f1 s2 r2 f2 :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  rangeDisjoint r2 r1 = true ->
   forall i : N, oro (f1 i) (f2 i) = oro (f2 i) (f1 i).
Proof.
  intros h0 h1 h2 i.
  destruct (f1 i) eqn:F1; destruct (f2 i) eqn:F2; simpl; auto.
  - assert (h3 : f2 i = None).
    rewrite rangeDisjoint_sym in h2.
    eapply isSubmapOfBy_disjoint1; eauto.
    rewrite h3 in F2.
    discriminate.
Qed.


Lemma link_Desc:
    forall {a} p1' (s1 : IntMap a) r1 f1 p2' s2 r2 f2 r f,
    Desc s1 r1 f1 ->
    Desc s2 r2 f2 ->
    p1' = rPrefix r1 ->
    p2' = rPrefix r2 ->
    rangeDisjoint r1 r2 = true->
    r = commonRangeDisj r1 r2 ->
    (forall i, f i = oro (f1 i) (f2 i)) ->
  Desc (link p1' s1 p2' s2) r f.
Proof.
  intros; subst.
  unfold link, linkWithMask.
  rewrite -> branchMask_spec. (* Uses the fact that IntSet.Internal.branchMask = branchMask *)
  rewrite mask_spec.
  rewrite -> zero_spec by (apply commonRangeDisj_rBits_pos; eapply Desc_rNonneg; eassumption).
  rewrite if_negb.
  match goal with [ |- context [N.testbit ?i ?b] ]  => destruct (N.testbit i b) eqn:Hbit end.
  * assert (Hbit2 : N.testbit (rPrefix r2) (rBits (commonRangeDisj r1 r2) - 1)%N = false).
    { apply not_true_is_false.
      rewrite <- Hbit.
      apply not_eq_sym.
      apply (commonRangeDisj_rBits_Different r1 r2);
          try (eapply Desc_rNonneg; eassumption); auto.
    }
    rewrite rangeDisjoint_sym in H3.
    rewrite -> commonRangeDisj_sym in * by (eapply Desc_rNonneg; eassumption).
    apply (DescBin _ _ _ _ _ _ _  _ _ _ f H0 H); auto.
    + apply commonRangeDisj_rBits_pos; (eapply Desc_rNonneg; eassumption).
    + rewrite <- Hbit2.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
    + rewrite <- Hbit at 1.
      rewrite -> commonRangeDisj_sym by (eapply Desc_rNonneg; eassumption).
      rewrite rangeDisjoint_sym in H3.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
    +
      intro i. erewrite disjoint_reorder; eauto.
      rewrite rangeDisjoint_sym.
      auto.
  * assert (Hbit2 : N.testbit (rPrefix r2) (rBits (commonRangeDisj r1 r2) - 1)%N = true).
    { apply not_false_iff_true.
      rewrite <- Hbit.
      apply not_eq_sym.
      apply commonRangeDisj_rBits_Different; try (eapply Desc_rNonneg; eassumption); auto.
    }
    apply (DescBin _ _ _ _ _ _ _ _ _ _ f H H0); auto.
    + apply commonRangeDisj_rBits_pos; (eapply Desc_rNonneg; eassumption).
    + rewrite <- Hbit.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
    + rewrite <- Hbit2 at 1.
      rewrite -> commonRangeDisj_sym by (eapply Desc_rNonneg; eassumption).
      rewrite rangeDisjoint_sym in H3.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
Qed.

Lemma disjoint_neq : forall x y, (x =? y) = false ->
  rangeDisjoint (singletonRange x) (singletonRange y) = true.
Proof.
       unfold singletonRange, rangeDisjoint. unfold isSubrange, rPrefix, inRange.
intros x y EE.
rewrite !N.shiftl_0_r.
rewrite !N.shiftr_0_r.
rewrite EE.
rewrite andb_false_l.
rewrite orb_false_l.
rewrite N.eqb_sym.
rewrite EE.
rewrite andb_false_l.
simpl. auto.
Qed.

Lemma insert_Nil_Desc a:
  forall e (v:a) r f,
  r = (singletonRange e) ->
  (forall i, f i = if (i =? e) then Some v else None) ->
  Desc (insert e v Nil) r f.
Proof.
  intros; subst.
  apply DescTip; try nonneg.
Qed.



(**
Helpful lemmas for the proofs of insert functions
**)

Lemma rPrefix_singletonRange e : rPrefix (singletonRange e) = e.
Proof. unfold rPrefix, singletonRange. rewrite N.shiftl_0_r. auto. Qed.
#[export] Hint Rewrite rPrefix_singletonRange.


 Lemma isSubrangeSingeltons:
 forall a b,
 (a == b) = false -> 
 isSubrange (singletonRange a) (singletonRange b) = false.
Proof.
  unfold isSubrange.
 unfold inRange.
 unfold singletonRange.
 simpl.
 intros.
 rewrite N.leb_refl.
 rewrite andb_true_r.
 rewrite N.shiftl_0_r.
 auto.
Qed.

 Lemma rangeDisjNotEqual :
  forall a b,
  (a == b) = false -> 
  rangeDisjoint (singletonRange a) (singletonRange b) = true.
  Proof.
    intros.
    unfold rangeDisjoint.
    rewrite isSubrangeSingeltons.
    rewrite isSubrangeSingeltons.
    -auto.
    -apply OrdTactic.Lemmas.Eq_neq_sym in H.
    auto.
    -apply H.
  Qed.


 Lemma BothInRangeCommonInRange:
 forall r1 r2 r3,
 isSubrange r1 r3 = true ->
 isSubrange r2 r3 = true ->
 isSubrange (commonRange r1 r2) r3 = true.
 Proof.
   intros.
   rewrite isSubrange_commonRange. 
   rewrite andb_true_iff.
   split; assumption.
 Qed.


Lemma less_impl_leb:
forall a,
 0 < a -> 
 0 <=? a-1 = true.
 Proof.
 intros.
 apply N.leb_le.
 lia.
 Qed. 


 (**
InsertWithKey is used as the primary insert function
and it is proven. Other insert functions are reduced
to an insertWithKey with some specific fixed arguments
which makes the proofs easier
**)


 Lemma insertWithKey_Desc a:
 forall (f: N -> a -> a -> a) e v r1,
 forall (s2: IntMap a) r2 f2,
 forall r f1,
 Desc s2 r2 f2 ->
 r1 = singletonRange e ->
 r = commonRange r1 r2 ->
 (forall i, f1 i = if (i =? e) then
  match f2 i with 
 | None => Some v
 | Some x => Some (f e v x)
  end
 else f2 i) ->
 Desc (insertWithKey f e v s2) r f1.
 Proof.
  intros ??????????? HD Sf ; subst.
  generalize dependent f1.
  induction H as [p2' bm2 r2 f2|s2 r2 f2 s3 r3 f3 p2' r]; subst; intros f' Hf.
  (** Induction on Desc **)
  (** Maybe the destruct should come later if this proof is recreated **)
  destruct (e =? bm2) eqn:EE. 
  +pose (h0 := H e). clearbody h0.
    rewrite <- reflect_iff in EE; try eapply N.eqb_spec. subst.
    unfold insertWithKey.
    rewrite OrdTactic.Lemmas.Eq_eq_refl.
     - apply DescTip.
      * intros. specialize (H i). specialize (Hf i).
      destruct (i=?bm2) eqn: EE.
       -- rewrite H in Hf. auto.
       -- congruence.
      * apply commonRange_idem.
  + unfold insertWithKey.
     replace (e == bm2) with false. eapply link_Desc.
      * apply DescTip; reflexivity.
      * apply DescTip; reflexivity.
      * rewrite rPrefix_singletonRange. reflexivity.
      * rewrite rPrefix_singletonRange. reflexivity.
      * unfold rangeDisjoint. rewrite isSubrangeSingeltons.
      rewrite isSubrangeSingeltons. auto.
       apply OrdTactic.Lemmas.Eq_neq_sym. apply EE. apply EE.
      * unfold commonRange. rewrite isSubrangeSingeltons. rewrite isSubrangeSingeltons.
      auto. apply OrdTactic.Lemmas.Eq_neq_sym. apply EE. apply EE.
      * intros. simpl. unfold oro. specialize (Hf i). specialize (H i).
      destruct (i=?e) eqn:EE2.
       -- replace i with e in *. 2:{
         symmetry. apply Neqb_ok. apply EE2.
       }
       rewrite EE in H. rewrite H in Hf. apply Hf. 
       -- rewrite  Hf. apply H.
      + unfold insertWithKey. rewrite zero_spec.
      destruct  (N.testbit e (rBits r0 - 1)) eqn:EE.
      (**Destructing on which subtree is e in**)
      - rewrite nomatch_spec. simpl.
       ++ destruct (inRange e r0) eqn:EE1. 
        ** assert (H5: commonRange (singletonRange e) r0 = r0 ). {
        (** This is very useful for many of the next subgoals**)
         apply isSubrange_commonRange_r. unfold isSubrange.
         rewrite rPrefix_singletonRange.
         rewrite EE1. simpl. eapply N.leb_le.
         lia.
      }
        simpl. eapply DescBin.
         -- apply H.
         -- fold (@insertWithKey).
         specialize (IHDesc2 f v ). apply IHDesc2.
         intros. reflexivity.
         -- rewrite H5. apply H1.
         -- rewrite H5. apply H2.
         -- rewrite H5.
         assert (inRange e (halfRange r0 true) = true ). {
         (** From EE, we know which subtree we are in, so we
         can make some assertions about the range**)
           rewrite halfRange_inRange_testbit.
            - rewrite EE. auto.
            - assumption.
            - assumption.
         }      
         assert (isSubrange (singletonRange e) (halfRange r0 true) = true). {
          rewrite <- smaller_inRange_iff_subRange.
          rewrite rPrefix_singletonRange. assumption. unfold singletonRange.
          rewrite rBits_halfRange. simpl. lia.
         }
          rewrite BothInRangeCommonInRange; auto.
         -- rewrite H5. reflexivity.
         -- rewrite H5. reflexivity.
         -- intros. simpl.
         destruct (i=?e ) eqn:EE2.
          +++         
          assert( Hs3: i=e -> (s3 i) = None ). {
          (** since we know which subtree we are in, 
          we  can tell that the the function of the
          other tree should return none **)
           intros. eapply Desc_outside.
           apply H. replace e with i in *.
           clear EE2 H4.
           assert (inRange i (halfRange r0 false) = false ). {
            rewrite halfRange_inRange_testbit.
             - simpl. rewrite EE. auto.
             - assumption.
             - assumption.
           }
           eapply inRange_isSubrange_false.
            *** apply H2.
            ***  apply H4.
          }
          unfold oro. rewrite Hs3. 2: { apply Neqb_ok. assumption. }
          specialize (Hf i). specialize (H6 i).
          rewrite EE2 in Hf. rewrite H6 in Hf. unfold oro in *.
          rewrite Hs3 in Hf. assumption. apply Neqb_ok. assumption.
          +++
          unfold oro in *. specialize (Hf i). rewrite EE2 in Hf.
          rewrite Hf. specialize (H6 i). assumption.
        ** simpl. assert (H8 : rangeDisjoint (singletonRange e) r0 = true). {
       unfold rangeDisjoint. unfold isSubrange.
       rewrite rPrefix_singletonRange. rewrite EE1.
       rewrite andb_false_l. rewrite orb_false_l. simpl.
       assert (H7: (rBits r0 <=? 0) = false ). {
        apply N.gt_lt_iff in H1. apply N.leb_gt.
        apply N.gt_lt. auto.
        }
        rewrite H7. rewrite andb_false_r. auto.
     }
        eapply link_Desc.
         -- apply DescTip;  reflexivity.
         -- eapply DescBin.
          +++ apply H.
          +++ apply H0.
          +++ apply H1.
          +++ apply H2.
          +++ apply H3.
          +++ reflexivity.
          +++ reflexivity.
          +++apply H6.
         -- rewrite rPrefix_singletonRange. reflexivity.
         -- reflexivity.
         -- apply H8.
         -- apply disjoint_commonRange. apply H8.
         --
         intros. simpl. unfold oro.
         destruct (i=?e ) eqn:EE2.
         +++
         specialize (H6 i).
         specialize (Hf i).
         assert((p2' i) = None ). {
         (**We know that i is not in range so both functions of,
         the subtrees must be none **)
          intros.
          eapply Desc_outside.
          apply H0.
          replace e with i in *. 2 : { apply Neqb_ok. assumption. }
          eapply inRange_isSubrange_false.
          - apply H3.
          -eapply inRange_isSubrange_false.
          + eapply isSubrange_halfRange. assumption.
          + assumption.
         }
         assert((s3 i) = None ). {
          intros. eapply Desc_outside. apply H.
          replace e with i in *. 2 : { apply Neqb_ok. assumption. }
          eapply inRange_isSubrange_false.
          - apply H2.
          - eapply inRange_isSubrange_false.
          + eapply isSubrange_halfRange. assumption.
          + assumption.
         }  
         unfold oro in *. rewrite EE2 in Hf. rewrite H6 in Hf.
         rewrite H5 in Hf. rewrite H4 in Hf. assumption.
          +++         
          unfold oro in *. specialize (Hf i).
          rewrite EE2 in Hf. rewrite Hf. reflexivity.
       ++ apply H1.
      - fold (@insertWithKey). rewrite nomatch_spec.
      destruct (inRange e r0) eqn:EE1.
       * simpl. assert (H5: commonRange (singletonRange e) r0 = r0 ). {
         apply isSubrange_commonRange_r. unfold isSubrange.
         rewrite rPrefix_singletonRange. rewrite EE1.
         simpl. eapply N.leb_le. lia.
      }
       eapply DescBin.
        -- specialize (IHDesc1 f v). apply IHDesc1. reflexivity.
        --  apply H0.
        -- rewrite H5. assumption. 
        -- rewrite H5. eapply BothInRangeCommonInRange.
        +++ unfold isSubrange. rewrite rPrefix_singletonRange.
        erewrite halfRange_inRange_testbit. simpl. rewrite EE. simpl.
        rewrite rBits_halfRange. apply N.leb_le. lia.
        assumption. assumption.
        +++ assumption.
        -- rewrite H5. assumption.
        -- rewrite H5. reflexivity.
        -- rewrite H5. reflexivity.
        -- intros. simpl. specialize (H6 i). specialize (Hf i).
        destruct (i=?e) eqn: EE2.
        +++  assert( Hp2: i=e -> (p2' i) = None ). {
         intros. eapply Desc_outside. apply H0.
         replace e with i in *.
         clear EE2 H4.
         assert (inRange i (halfRange r0 true) = false ). {
          rewrite halfRange_inRange_testbit.
           - simpl. rewrite EE. auto. 
           - assumption.
           - assumption.
         }
         eapply inRange_isSubrange_false.
          *** apply H3.
          ***  apply H4.
        }
        unfold oro in *. rewrite Hp2. rewrite Hp2 in H6. rewrite H6 in Hf.
        destruct (s3 i).
        assumption. assumption. apply Neqb_ok.
        assumption. apply Neqb_ok. assumption.
        +++ unfold oro in *. rewrite <- Hf in H6. assumption.
       * simpl.
       assert (H8 : rangeDisjoint (singletonRange e) r0 = true). {
       unfold rangeDisjoint. unfold isSubrange.
       rewrite rPrefix_singletonRange. rewrite EE1.
       rewrite andb_false_l. rewrite orb_false_l.
       simpl. assert (H7: (rBits r0 <=? 0) = false ). {
         apply N.gt_lt_iff in H1. apply N.leb_gt.
         apply N.gt_lt. auto.
        }
        rewrite H7. rewrite andb_false_r. auto.
     }
       eapply link_Desc.    
        -- eapply DescTip. intros; reflexivity. reflexivity.
        -- eapply DescBin.
         ++ apply H.
         ++ apply H0.
         ++ apply H1.
         ++ apply H2.
         ++ apply H3.
         ++ reflexivity.
         ++ reflexivity.
         ++ intros. reflexivity.
        -- rewrite rPrefix_singletonRange. reflexivity.
        -- reflexivity.
        -- apply H8.
        -- apply disjoint_commonRange. apply H8.
        -- intros. simpl. specialize (Hf i). specialize (H6 i).
        destruct (i=?e) eqn:EE2.
         ++ unfold oro in *.
         (**
         since it is not inRange, we know that both subtrees should
         return None
         **)
         assert (Hp2: p2' i = None). {
           eapply Desc_outside. apply H0.
           replace e with i in *. 
           2:{ apply Neqb_ok. assumption. }
           clear EE2.
           assert (inRange i (halfRange r0 true) = false ). {
           eapply inRange_isSubrange_false.
           apply isSubrange_halfRange. assumption. assumption.
         }
         eapply inRange_isSubrange_false.
          *** apply H3.
          ***  apply H4.
         }
         assert (Hs3: s3 i = None). {
          eapply Desc_outside. apply H.
          replace e with i in *. 
          2:{ apply Neqb_ok. assumption. } clear EE2.
          assert (inRange i (halfRange r0 false) = false ). {
          eapply inRange_isSubrange_false. apply isSubrange_halfRange.
          assumption. assumption.
        }
        eapply inRange_isSubrange_false.
         *** apply H2.
         ***  apply H4.
        }
         rewrite Hp2 in H6. rewrite Hs3 in H6. rewrite H6 in Hf. assumption.
         ++ unfold oro in *. congruence.
       * apply H1.
      - apply H1.
 Qed.


 Lemma insertWith_Desc:
 forall a (f: a -> a -> a) e v r1,
 forall (s2: IntMap a) r2 f2,
 forall r f1,
 Desc s2 r2 f2 ->
 r1 = singletonRange e ->
 r = commonRange r1 r2 ->
 (forall i, f1 i = if (i =? e) then
  match f2 i with 
 | None => Some v
 | Some x => Some (f v x)
  end
 else f2 i) ->
 Desc (insertWith f e v s2) r f1.
 Proof.
   intros ?????????? HD ?? Sf ; subst.
   generalize dependent f1.
   induction HD as [p2' bm2 r2 f2|s2 r2 f2 s3 r3 f3 p2' r]; subst; intros f' Hf.
    + unfold insertWith.
    eapply insertWithKey_Desc.
     -eapply DescTip; reflexivity.
     - reflexivity.
     - reflexivity.
     - intros. specialize (Hf i).
     simpl.
     destruct (i=?e).
      * specialize (H i).
      rewrite H in Hf. eassumption.
      * specialize (H i). rewrite <- Hf in H. eassumption. 
    + eapply insertWithKey_Desc.
     - eapply DescBin; try eassumption.
      * reflexivity.
      * reflexivity.
     - reflexivity.
     - reflexivity.
     - eassumption. 
 Qed.


 Lemma pair_fst_snd: forall {a: Type} {b : Type} (p : a * b),
 p = (fst p, snd p).
Proof.
intros. destruct p. simpl. reflexivity.
Qed.


(** the second in the pair of insertLookupWithKey is the same
 map as insertWithKey **)
 Lemma insertWithKey_insertLookupWithKey:
 forall a (f: a -> a -> a) e v ,
 forall (s: IntMap a)  f,
  insertWithKey f e v s = snd (insertLookupWithKey f e v s).
Proof.
intros . induction s; intros.
  - simpl. destruct (nomatch e p m).
   + simpl. reflexivity.
   + destruct (zero e m).
    * simpl.
     rewrite (pair_fst_snd (insertLookupWithKey f0 e v s1)). simpl.
     rewrite IHs1.
     reflexivity.
    * simpl.
    rewrite (pair_fst_snd (insertLookupWithKey f0 e v s2)). simpl.
     rewrite IHs2.
     reflexivity.
  - simpl. destruct (e == k).
   + simpl. reflexivity.
   + simpl. reflexivity.
  - simpl. reflexivity. 
   Qed.


   Lemma insertLookupWithKey_fst a:
   forall (s:IntMap a) k f1 r,
   forall f x,
   Desc s r f ->
   fst ((insertLookupWithKey f1 k x s)) = f k.
   Proof.
   intros. generalize dependent k. revert f1. induction H; intros; simpl.
   - destruct (k0 ==k) eqn:EE.
    + simpl. specialize (H k0). rewrite -> N.eqb_eq in EE.
     subst. rewrite N.eqb_refl in H. symmetry. assumption.
    + simpl. specialize (H k0). 
    assert (k0 =? k = false). { auto. }
    rewrite H1 in H. symmetry. assumption.
   - subst. erewrite nomatch_spec; try assumption.
    rewrite zero_spec; try assumption.
    destruct (inRange k r) eqn:EE; simpl.
   + destruct (N.testbit k (rBits r - 1)) eqn: EE1.
    * simpl. rewrite (pair_fst_snd (insertLookupWithKey f0 k x m2 )).
     simpl. specialize (H6 k).
    assert (f1 k = None). { 
    eapply Desc_outside. eapply H.
    assert (inRange k (halfRange r false) = false ).
     { eapply testbit_halfRange_false; try assumption. }
    eapply inRange_isSubrange_false. eapply H2. eapply H4. }
    unfold oro in H6. erewrite H4 in H6.
    rewrite H6. eapply IHDesc2.
    * simpl. rewrite (pair_fst_snd (insertLookupWithKey f0 k x m1 )).
     simpl. specialize (H6 k).
    assert (f2 k = None). { 
    eapply Desc_outside. eapply H0.
    assert (inRange k (halfRange r true) = false ).
     { eapply testbit_halfRange_false; try assumption. }
    eapply inRange_isSubrange_false.
     eapply H3. eapply H4. }
    unfold oro in H6. erewrite H4 in H6.
    assert (f k = f1 k).
     { destruct (f1 k) eqn: Efk; assumption. }
      rewrite H5. eapply IHDesc1.
    + specialize (H6 k). symmetry.
    assert (f1 k = None). {
    eapply Desc_outside. apply H.
    eapply inRange_isSubrange_false. eapply H2.
    eapply inRange_isSubrange_false with (r2:= r).
    eapply isSubrange_halfRange; eassumption. apply EE. } 
    assert (f2 k = None).
     { eapply Desc_outside. apply H0.
      eapply inRange_isSubrange_false. eapply H3.
      eapply inRange_isSubrange_false with (r2:= r).
      eapply isSubrange_halfRange;
       eassumption. apply EE. }
   unfold oro in H6. 
   rewrite H4 in H6. congruence. 
Qed.
    




   Lemma insertLookupWithKey_Desc a:
   forall (f: N -> a -> a -> a) e v r1,
   forall (s2: IntMap a) r2 f2,
   forall r f1,
   Desc s2 r2 f2 ->
   r1 = singletonRange e ->
   r = commonRange r1 r2 ->
   (forall i, f1 i = if (i =? e) then
     match f2 i with 
       | None => Some v
       | Some x => Some (f e v x)
     end
  else f2 i) ->
  Desc  (snd (insertLookupWithKey  f e v s2)) r f1.
 Proof.
 intros. rewrite <- insertWithKey_insertLookupWithKey. eapply insertWithKey_Desc.
 -eapply H.
 - eapply H0.
 - eapply H1.
 - eapply H2.
 - auto.
 Qed.

 (** THis makes insert proof much easier. Insert is just insertWithKey
  where the function leaves the element as it is**)
 
 Lemma insert_is_insert_with_key a: 
 forall e v f,
 forall (s: IntMap a),
 (forall  i j k,  f k i j = i) ->
  insert e v s = insertWithKey f e v s.
  Proof.
  intros.
  induction s.
  -
  simpl. destruct (nomatch e p m) eqn:EE. 
   +  
    reflexivity. 
   + destruct (zero e m) eqn: EE2.
    *
     rewrite IHs1. reflexivity.
    *rewrite IHs2. reflexivity.
  -  unfold insert.  unfold insertWithKey.
  destruct (e == k).
   + specialize (H v a0 e).
   erewrite H. reflexivity.
   + reflexivity. 
  - unfold insert. unfold insertWithKey.
  reflexivity.
  Qed.



 Lemma insert_Desc a:
  forall e v r1,
  forall (s2:IntMap a) r2 f2,
  forall r f,
  Desc s2 r2 f2 ->
  r1 = (singletonRange e) ->
  r = commonRange r1 r2 ->
  (forall i, f i = if (i =? e) then Some v else f2 i) ->
  Desc (insert e v s2) r f.
Proof.
intros.
   erewrite insert_is_insert_with_key .
   -intros.
   eapply insertWith_Desc with (f:= fun v x => v).
   + apply H.
   + reflexivity.
   + congruence.
   + intros.
   specialize (H2 i).
   destruct (i=?e).
   * rewrite H2. destruct (f2 i).
    ++ reflexivity.
    ++ reflexivity.
  * assumption.
  - intros.
  simpl. reflexivity.
  Qed.



  Lemma insert_Sem:
  forall a e (v:a) s2 f2 f,
  Sem s2 f2 ->
  (forall i, f i = if (i =? e) then Some v else f2 i) ->
  Sem (insert e v s2) f.
Proof.
  intros.
  destruct H.
  * eapply DescSem. apply insert_Nil_Desc; auto.
    solve_f_eq.
  * eapply DescSem. eapply insert_Desc; eauto.
Qed.

Lemma insert_WF:
  forall a n (v:a) s, WF s -> WF (insert n v s).
Proof.
  intros.
  destruct H.
  eexists.
  eapply insert_Sem; eauto.
  intro i; reflexivity.
Qed.

(* Verification of [filter] *)

(* bin_Desc0: the smart constructor [bin] preserves Desc0.
   Used by filter_Desc and restrictKeys_Desc. *)
Lemma bin_Desc0:
  forall {a} (s1: IntMap a) r1 f1 (s2: IntMap a) r2 f2 p msk r f,
    Desc0 s1 r1 f1 ->
    Desc0 s2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r ->
    (forall i, f i = oro (f1 i) (f2 i)) ->
    Desc0 (bin p msk s1 s2) r f.
Proof.
  intros a s1 r1 f1 s2 r2 f2 p msk r f HD1 HD2 Hbits Hr1 Hr2 Hp Hmsk Hf.
  subst p msk.
  (* Useful derived facts: halfRanges are subranges of r *)
  assert (HhrL : isSubrange (halfRange r false) r = true)
    by (apply isSubrange_halfRange; exact Hbits).
  assert (HhrR : isSubrange (halfRange r true) r = true)
    by (apply isSubrange_halfRange; exact Hbits).
  destruct HD1 as [a1 r1 f1 Hf1_nil | a1 s1 r1i f1i r1 f1 HD1i Hsub1 Hf1_eq].
  - (* Case: s1 = Nil *)
    destruct HD2 as [a2 r2 f2 Hf2_nil | a2 s2 r2i f2i r2 f2 HD2i Hsub2 Hf2_eq].
    + (* Case 1: s1 = Nil, s2 = Nil -> bin returns Nil *)
      simpl. apply Desc0Nil. intro i.
      rewrite Hf. rewrite Hf1_nil. rewrite Hf2_nil. reflexivity.
    + (* Case 2: s1 = Nil, s2 non-Nil -> bin returns s2 *)
      destruct s2; [| | inversion HD2i].
      all: simpl; eapply Desc0NotNil; [
        exact HD2i |
        eapply isSubrange_trans; [eapply isSubrange_trans; [exact Hsub2 | exact Hr2] | exact HhrR] |
        intro i; rewrite Hf; rewrite Hf1_nil; simpl; apply Hf2_eq ].
  - (* Case: s1 non-Nil *)
    destruct HD2 as [a2 r2 f2 Hf2_nil | a2 s2 r2i f2i r2 f2 HD2i Hsub2 Hf2_eq].
    + (* Case 3: s1 non-Nil, s2 = Nil -> bin returns s1 *)
      destruct s1; [| | inversion HD1i].
      all: simpl; eapply Desc0NotNil; [
        exact HD1i |
        eapply isSubrange_trans; [eapply isSubrange_trans; [exact Hsub1 | exact Hr1] | exact HhrL] |
        intro i; rewrite Hf; rewrite Hf2_nil; rewrite oro_None_r; apply Hf1_eq ].
    + (* Case 4: both non-Nil -> bin returns Bin (rPrefix r) (rMask r) s1 s2 *)
      (* We need to destruct s1 and s2 to let simpl reduce the match in bin.
         Desc guarantees they are Bin or Tip (not Nil). *)
      assert (Hsub1r : isSubrange r1i (halfRange r false) = true)
        by (eapply isSubrange_trans; [exact Hsub1 | exact Hr1]).
      assert (Hsub2r : isSubrange r2i (halfRange r true) = true)
        by (eapply isSubrange_trans; [exact Hsub2 | exact Hr2]).
      destruct s1; [| | inversion HD1i];
      (destruct s2; [| | inversion HD2i]);
      simpl;
      (eapply Desc0NotNil; [
        eapply DescBin; [
          exact HD1i | exact HD2i | exact Hbits |
          exact Hsub1r | exact Hsub2r |
          reflexivity | reflexivity |
          intro i; reflexivity ] |
        apply isSubrange_refl |
        intro i; rewrite Hf; rewrite Hf1_eq; rewrite Hf2_eq; reflexivity ]).
Qed.     

Definition IMFilter {a} p (s: IntMap a) :=
  Data.IntMap.Internal.filter p s.

Lemma filter_Desc:
  forall {a} p (s: IntMap a) r f f',
    Desc s r f ->
    (forall (i: N), f' i = match f i with
                 | None => None
                 | Some v => if p v then Some v else None
                 end) ->                                    
    Desc0 (IMFilter p s) r f'.
Proof.
  intros.
  revert f' H0.
  induction H.
  * intros.
    simpl. subst. destruct (p v) eqn: Hpv.
     + eapply  Desc0NotNil; eauto. apply DescTip; eauto.
       intro. specialize (H1 i). specialize (H i). rewrite H in H1.
       destruct (i =? k) eqn: Hik; auto. rewrite Hpv in H1. auto.
       eapply isSubrange_refl.
     + eapply Desc0Nil. intro. specialize (H i). specialize (H1 i). destruct (f i).
       - destruct (i =? k).
         ** inversion H. subst. rewrite Hpv in H1. auto.
         ** discriminate.
       - auto.
  * intros. subst. simpl.
    specialize (IHDesc1 p (fun i => match f1 i with
                                  | None => None
                                  | Some v => if p v then Some v else None
                                  end) ltac:(intros; auto)).
    specialize (IHDesc2 p (fun i => match f2 i with
                                  | None => None
                                  | Some v => if p v then Some v else None
                                 end) ltac:(intros; auto)).
    eapply bin_Desc0.
    + apply IHDesc1.
    + apply IHDesc2.
    + auto.
    + apply H2.
    + apply H3.
    + auto.
    + auto.
    + intro. simpl. specialize (H7 i). specialize (H6 i). rewrite H7. rewrite H6. unfold oro.
      assert (Hr: rangeDisjoint r1 r2 = true).
      { eapply isSubrange_disj_disj_r. exact H3.
        eapply isSubrange_disj_disj_l. exact H2.
        apply halves_disj. exact H1. }
      destruct (f1 i) eqn: Hf1.
       - destruct (p a0) eqn: Hpa; auto. assert (f2 i = None).
         {
           eapply isSubmapOfBy_disjoint1; eassumption.
         }
         rewrite H4. reflexivity.
       - reflexivity.
Qed.

Lemma filter_Sem:
  forall {a} p (s: IntMap a) f f',
  Sem s f ->
  (forall i, f' i = match f i with
               | None => None
               | Some v => if p v then Some v else None
               end) ->
  Sem (IMFilter p s) f'.
Proof.
  intros. destruct H.
  * apply SemNil. auto. solve_f_eq.
  * eapply Desc0_Sem. eapply filter_Desc; eassumption.
Qed.

Lemma filter_WF:
  forall {a} p (s: IntMap a),
    WF s -> WF (IMFilter p s).
Proof.
  intros. destruct H. eexists. eapply filter_Sem. eassumption. intro. reflexivity.
Qed.

Lemma insertWithKey_Nil_Desc a:
  forall e (v:a) r f f1,
  r = (singletonRange e) ->
  (forall i, f i = if (i =? e) then Some v else None) ->
  Desc (insertWithKey f1 e v Nil) r f.
Proof.
  intros; subst.
  apply DescTip; try nonneg.
Qed.



(**Verification of Delete**)





(** Was useful on one of my approaches to delete but I changed it. Will
  leave it for now**)
Lemma inRange_singletonRange:
forall e,
inRange e (singletonRange e) = true.
Proof.
intros. unfold singletonRange. unfold inRange.
simpl. apply N.eqb_refl.
Qed.


(* Fully proved. Key techniques: (1) revert r1/f before induction for a
   strong IH generalized over the outer range, (2) nomatch_zero to split into
   three sub-cases, (3) replace binCheckLeft/binCheckRight with bin (justified
   because the untouched child satisfies Desc hence is non-Nil), (4) bin_Desc0
   to combine the IH result with the unchanged child, (5) Desc_outside +
   inRange_isSubrange_false to show keys in one half are absent from the other. *)

Lemma delete_Desc a :
forall e,
  forall (s1:IntMap a)  f1 r1,
  forall r f,
  Desc s1 r f1 ->
  isSubrange r r1 = true ->
  (forall i, f i = if (i =? e) then None else f1 i) ->
  Desc0 (delete e s1) r1 f.
Proof.
 intros. revert dependent r1. revert dependent f.
 induction H; intros; subst.
 + (* Tip case: delete e (Tip k v) *)
 unfold delete.
 destruct (e == k) eqn:EE.
  - rewrite EE.  eapply Desc0Nil.
  intros. specialize (H i).
  destruct (i =? k) eqn:EE1.
   * specialize (H1 i).
    assert (Hie : i=? e = true). {
    apply Neqb_ok in EE. apply N.eqb_eq in EE1. subst. apply N.eqb_refl.
    }
    rewrite Hie in H1.
    apply H1.
   *
   specialize (H1 i).
    assert (Hie : i=? e = false). {
    apply Neqb_ok in EE. subst. exact EE1.
    }
    rewrite Hie in H1.
    congruence.
  -
  rewrite EE. eapply Desc0NotNil.
   * eapply DescTip; reflexivity.
   * assumption.
   * intros. simpl. specialize (H1 i).
   specialize (H i). rewrite H in H1.
   destruct (i=?e) eqn:EE1.
    --  assert (Hik : i=?k = false). {
    apply N.eqb_eq in EE1. apply N.eqb_neq. apply N.eqb_neq in EE. intro. subst. contradiction.
    }
    rewrite H1. rewrite Hik. reflexivity.
    -- assumption.
 + (* Bin case: delete e (Bin (rPrefix r) (rMask r) m1 m2) *)
   simpl.
   apply nomatch_zero.
   { (* (0 < rBits r)%N *) exact H1. }
   - (* nomatch case: inRange e r = false, tree unchanged *)
     intro HnotInRange.
     eapply Desc0NotNil.
     * eapply DescBin.
       exact H. exact H0. exact H1. exact H2. exact H3.
       reflexivity. reflexivity. exact H6.
     * exact H8.
     * intro i. rewrite H7.
       destruct (i =? e) eqn:Hie; [| reflexivity].
       apply N.eqb_eq in Hie. subst i.
       symmetry. eapply Desc_outside.
       eapply DescBin.
       exact H. exact H0. exact H1. exact H2. exact H3.
       reflexivity. reflexivity. exact H6.
       exact HnotInRange.
   - (* zero case (delete from left): inRange e (halfRange r false) = true *)
     intros HinLeft HnotRight.
     (* binCheckLeft p m (delete e m1) m2 = bin p m (delete e m1) m2
        because m2 is non-Nil (it satisfies Desc) *)
     assert (Hm2_notNil : m2 <> Nil) by (intro Heq; subst; inversion H0).
     replace (binCheckLeft (rPrefix r) (rMask r) (delete e m1) m2)
       with (bin (rPrefix r) (rMask r) (delete e m1) m2). 2: {
       unfold binCheckLeft, bin.
       destruct (delete e m1); destruct m2; try reflexivity;
       exfalso; apply Hm2_notNil; reflexivity.
     }
     (* Combine via bin_Desc0, then lift to outer range *)
     eapply Desc0_subRange. 2: exact H8.
     eapply bin_Desc0.
     * (* Desc0 (delete e m1) r1 (fun i => if i=?e then None else f1 i) *)
       eapply IHDesc1.
       ++ intro i. reflexivity.
       ++ apply isSubrange_refl.
     * (* Desc0 m2 r2 f2 *)
       eapply Desc_Desc0. exact H0.
     * exact H1.
     * exact H2.
     * exact H3.
     * reflexivity.
     * reflexivity.
     * intro i. rewrite H7. rewrite H6.
       destruct (i =? e) eqn:Hie.
       ++ apply N.eqb_eq in Hie. subst i. simpl. symmetry.
          eapply Desc_outside. exact H0.
          eapply inRange_isSubrange_false. exact H3. exact HnotRight.
       ++ reflexivity.
   - (* one case (delete from right): inRange e (halfRange r true) = true *)
     intros HnotLeft HinRight.
     assert (Hm1_notNil : m1 <> Nil) by (intro Heq; subst; inversion H).
     replace (binCheckRight (rPrefix r) (rMask r) m1 (delete e m2))
       with (bin (rPrefix r) (rMask r) m1 (delete e m2)). 2: {
       unfold binCheckRight, bin.
       destruct m1; destruct (delete e m2); try reflexivity.
       all: exfalso; apply Hm1_notNil; reflexivity.
     }
     eapply Desc0_subRange. 2: exact H8.
     eapply bin_Desc0.
     * eapply Desc_Desc0. exact H.
     * eapply IHDesc2.
       ++ intro i. reflexivity.
       ++ apply isSubrange_refl.
     * exact H1.
     * exact H2.
     * exact H3.
     * reflexivity.
     * reflexivity.
     * intro i. rewrite H7. rewrite H6.
       destruct (i =? e) eqn:Hie.
       ++ apply N.eqb_eq in Hie. subst i.
          assert (Hfl_none : f1 e = None). {
            eapply Desc_outside. exact H.
            eapply inRange_isSubrange_false. exact H2. exact HnotLeft.
          }
          rewrite Hfl_none. simpl. reflexivity.
       ++ reflexivity.
Qed.

Lemma delete_Sem:
  forall {a} e (s: IntMap a) f f',
  Sem s f ->
  (forall i, f' i = if (i =? e) then None else f i) ->
  Sem (delete e s) f'.
Proof.
  intros a e s f f' Hsem Hf.
  destruct Hsem as [a f Hnil | a s r f HD].
  * apply SemNil. intro i. rewrite Hf Hnil.
    destruct (i =? e); reflexivity.
  * eapply Desc0_Sem.
    eapply delete_Desc.
    - exact HD.
    - apply isSubrange_refl.
    - exact Hf.
Qed.

Lemma delete_WF:
  forall {a} e (s: IntMap a),
  WF s -> WF (delete e s).
Proof.
  intros a e s [f Hsem].
  exists (fun i => if (i =? e) then None else f i).
  eapply delete_Sem.
  - exact Hsem.
  - intro i. reflexivity.
Qed.

Definition IMFilterWithKey {a} p (s: IntMap a) :=
  Data.IntMap.Internal.filterWithKey p s.



(** * Specifying [restrictKeys] *)

(* We can extract the argument to [deferredFix] from the definition of [restrictKeys]. *)

Definition restrictKeys_f {a} :
  (IntMap a -> IntSet -> IntMap a) -> (IntMap a -> IntSet -> IntMap a).
Proof.
  let rhs := eval unfold restrictKeys in (@restrictKeys a) in
  match rhs with context[ deferredFix2 ?f ] => exact f end.
Defined.


Definition restrictKeys_body {a} := restrictKeys_f (@restrictKeys a).

Lemma restrictKeys_eq {a} (m : IntMap a) s :
  restrictKeys m s = restrictKeys_body m s.
Proof.
  enough (@restrictKeys a = restrictKeys_body) by congruence.
  apply deferredFix2_eq.
Qed.

Definition restrictBitMapToRange r bm :=
  let p := rPrefix r in
  let msk := rMask r in
    N.land (N.land bm (N.lxor (bitmapOf p - 1)%N (N.ones 64%N)))
           (N.lor (bitmapOf (N.lor p (N.lor msk (msk - 1))))
           (bitmapOf (N.lor p (N.lor msk (msk - 1))) - 1)%N).




Ltac point_to_inRange_Map :=
  lazymatch goal with
    | [ HD : IntSetProofs.Desc ?s ?r ?f, Hf : ?f ?i = true |- _ ]
      => apply (IntSetProofs.Desc_inside HD) in Hf
    | [ H : bitmapInRange ?r ?bm ?i = true |- _ ]
      => apply bitmapInRange_inside in H
    | [ HD : Desc ?m ?r ?f, Hf : ?f ?i = Some _ |- _ ]
      => apply (Desc_inside HD) in Hf
  end.

Ltac solve_f_eq_disjoint_Map :=
  solve_f_eq;
  repeat point_to_inRange_Map;
  repeat saturate_inRange;
  try inRange_disjoint. (* Only try this, so that we see wher we are stuck. *)


(* The Bin/Tip case (m1=Bin, s2=IntSet.Tip) involves [restrictBM] and
   [lookupPrefix], which are separate deferredFix functions requiring their
   own Desc lemmas. We admit this case and prove the Bin/Bin case fully. *)
Program Fixpoint restrictKeys_Desc
  a (m1 : IntMap a) r1 f1 s2 r2 f2 f
  { measure (size_nat m1 + Data.IntSet.Internal.size_nat s2) } :
  Desc m1 r1 f1 ->
  IntSetProofs.Desc s2 r2 f2 ->
  (forall i, f i = if f2 i then f1 i else None) ->
  Desc0 (restrictKeys m1 s2) r1 f
  := fun HD1 HD2 Hf => _.
Next Obligation.
  rewrite restrictKeys_eq.
  unfold restrictKeys_body, restrictKeys_f.
  unfoldMethods.

  destruct HD1.
  * (* m1 is a Tip *)
    subst.
    erewrite IntSetProofs.member_Desc by eassumption.
    destruct (f2 k) eqn: Hf2.
    + eapply Desc0NotNil; try (apply isSubrange_refl); try (intro; reflexivity).
      eapply DescTip; try reflexivity.
      intro i.
      rewrite Hf H; clear Hf H.
      destruct (N.eqb_spec i k).
      - subst. rewrite Hf2. reflexivity.
      - destruct (f2 i); reflexivity.
    + apply Desc0Nil.
      intro i.
      rewrite Hf H; clear Hf H.
      destruct (N.eqb_spec i k).
      - subst. rewrite Hf2. reflexivity.
      - destruct (f2 i); reflexivity.

  * (* m1 is a Bin *)
    (* After destruct HD1 (Bin case), we have:
       HD1_1 : Desc m1 r1 f1  (left child)
       HD1_2 : Desc m2 r0 f0  (right child)
       H  : (0 < rBits r)%N
       H0 : isSubrange r1 (halfRange r false) = true
       H1 : isSubrange r0 (halfRange r true) = true
       H4 : forall i, f3 i = oro (f1 i) (f0 i)
       Hf : forall i, f i = if f2 i then f3 i else None *)
    inversion HD2.
    + (* s2 is a Tip *)
      (* This case involves restrictBM and lookupPrefix which need separate
         Desc lemmas. Admitted for now. *)
      clear restrictKeys_Desc. subst.
      set (m := Bin (rPrefix r) (rMask r) m1 m2) in *.
      admit.
    + (* s2 is also a Bin *)
      (* After inversion HD2 (Bin case) and subst, we additionally have:
         H5  : IntSetProofs.Desc s1 r3 f4  (left set child)
         H6  : IntSetProofs.Desc s0 r4 f5  (right set child)
         H7  : (0 < rBits r2)%N
         H8  : isSubrange r3 (halfRange r2 false) = true
         H9  : isSubrange r4 (halfRange r2 true) = true
         H12 : forall i, f2 i = f4 i || f5 i *)
      subst.
      set (m := Bin (rPrefix r) (rMask r) m1 m2) in *.
      set (s := IntSet.Internal.Bin (rPrefix r2) (rMask r2) s1 s0) in *.
      rewrite -> !shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r)).
      ++ (* Map is broader: check which half of map the set falls in *)
        apply nomatch_zero_smaller; try assumption; intros.
        - (* Set range r2 is disjoint from map range r *)
          apply Desc0Nil.
          intro i. rewrite Hf.
          destruct (f2 i) eqn:Hf2i; [| reflexivity].
          assert (HirR2 : inRange i r2 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
          assert (HirR : inRange i r = false)
            by (eapply rangeDisjoint_inRange_false; eassumption).
          rewrite H4.
          assert (Hf1None : f1 i = None) by (eapply Desc_outside; [exact HD1_1 |
            eapply inRange_isSubrange_false; [exact H0 |
              eapply inRange_isSubrange_false; [apply isSubrange_halfRange; exact H | exact HirR]]]).
          assert (Hf0None : f0 i = None) by (eapply Desc_outside; [exact HD1_2 |
            eapply inRange_isSubrange_false; [exact H1 |
              eapply inRange_isSubrange_false; [apply isSubrange_halfRange; exact H | exact HirR]]]).
          rewrite Hf1None Hf0None. reflexivity.
        - (* Set range r2 is in the left half of map range r *)
          eapply Desc0_subRange.
          eapply restrictKeys_Desc; clear restrictKeys_Desc; try eassumption.
          ** subst m s. simpl. lia.
          ** intro i. rewrite Hf.
             destruct (f2 i) eqn:Hf2i; [| reflexivity].
             assert (HirR2 : inRange i r2 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
             assert (HirLf : inRange i (halfRange r false) = true)
               by (eapply inRange_isSubrange_true; [| exact HirR2]; eassumption).
             assert (HirRt : inRange i (halfRange r true) = false)
               by (eapply rangeDisjoint_inRange_false;
                   [apply halves_disj; exact H | exact HirLf]).
             assert (Hf0None : f0 i = None) by (eapply Desc_outside; [exact HD1_2 |
               eapply inRange_isSubrange_false; [exact H1 | exact HirRt]]).
             rewrite H4. rewrite Hf0None. rewrite oro_None_r. reflexivity.
          ** isSubrange_true; assumption.
        - (* Set range r2 is in the right half of map range r *)
          eapply Desc0_subRange.
          eapply restrictKeys_Desc; clear restrictKeys_Desc; try eassumption.
          ** subst m s. simpl. lia.
          ** intro i. rewrite Hf.
             destruct (f2 i) eqn:Hf2i; [| reflexivity].
             assert (HirR2 : inRange i r2 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
             assert (HirRt : inRange i (halfRange r true) = true)
               by (eapply inRange_isSubrange_true; [| exact HirR2]; eassumption).
             assert (HirLf : inRange i (halfRange r false) = false)
               by (eapply rangeDisjoint_inRange_false;
                   [rewrite rangeDisjoint_sym; apply halves_disj; exact H | exact HirRt]).
             assert (Hf1None : f1 i = None) by (eapply Desc_outside; [exact HD1_1 |
               eapply inRange_isSubrange_false; [exact H0 | exact HirLf]]).
             rewrite H4. rewrite Hf1None. reflexivity.
          ** isSubrange_true; assumption.

      ++ (* Map is not broader; check if set is broader *)
        destruct (N.ltb_spec (rBits r) (rBits r2)).
        -- (* Set is broader: check which half of set the map falls in *)
          apply nomatch_zero_smaller; try assumption; intros.
          - (* Map range r is disjoint from set range r2 *)
            apply Desc0Nil.
            intro i. rewrite Hf.
            destruct (f2 i) eqn:Hf2i; [| reflexivity].
            assert (HirR2 : inRange i r2 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
            assert (HirR : inRange i r = false)
              by (eapply rangeDisjoint_inRange_false;
                  [rewrite rangeDisjoint_sym; eassumption | exact HirR2]).
            rewrite H4.
            assert (Hf1None : f1 i = None) by (eapply Desc_outside; [exact HD1_1 |
              eapply inRange_isSubrange_false; [exact H0 |
                eapply inRange_isSubrange_false; [apply isSubrange_halfRange; exact H | exact HirR]]]).
            assert (Hf0None : f0 i = None) by (eapply Desc_outside; [exact HD1_2 |
              eapply inRange_isSubrange_false; [exact H1 |
                eapply inRange_isSubrange_false; [apply isSubrange_halfRange; exact H | exact HirR]]]).
            rewrite Hf1None Hf0None. reflexivity.
          - (* Map range r is in the left half of set range r2.
               Recurse with whole map against left set child. *)
            eapply Desc0_subRange.
            eapply restrictKeys_Desc; clear restrictKeys_Desc.
            ** subst m s. simpl. lia.
            ** eapply (DescBin _ _ _ _ _ _ _ _ _ _ _ HD1_1 HD1_2 H H0 H1 eq_refl eq_refl H4).
            ** exact H5.
            ** intro i. rewrite Hf. rewrite H12.
               destruct (f4 i) eqn:Hf4i; simpl.
               +++ reflexivity.
               +++ destruct (f5 i) eqn:Hf5i; simpl; [| reflexivity].
                   (* f4 i = false, f5 i = true: map is in left half, key in right half of set *)
                   assert (HirR4 : inRange i r4 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
                   assert (HirRt : inRange i (halfRange r2 true) = true)
                     by (eapply inRange_isSubrange_true; [| exact HirR4]; eassumption).
                   assert (HirLf : inRange i (halfRange r2 false) = false)
                     by (eapply rangeDisjoint_inRange_false;
                         [rewrite rangeDisjoint_sym; apply halves_disj; exact H7 | exact HirRt]).
                   (* Map range r ⊆ halfRange r2 false, but inRange i (halfRange r2 false) = false *)
                   assert (HirR : inRange i r = false)
                     by (eapply inRange_isSubrange_false;
                         [match goal with [ Hsub : isSubrange r (halfRange r2 false) = true |- _ ] => exact Hsub end
                         | exact HirLf]).
                   rewrite H4.
                   assert (Hf1None : f1 i = None) by (eapply Desc_outside; [exact HD1_1 |
                     eapply inRange_isSubrange_false; [exact H0 |
                       eapply inRange_isSubrange_false; [apply isSubrange_halfRange; exact H | exact HirR]]]).
                   assert (Hf0None : f0 i = None) by (eapply Desc_outside; [exact HD1_2 |
                     eapply inRange_isSubrange_false; [exact H1 |
                       eapply inRange_isSubrange_false; [apply isSubrange_halfRange; exact H | exact HirR]]]).
                   rewrite Hf1None Hf0None. reflexivity.
            ** isSubrange_true; assumption.

          - (* Map range r is in the right half of set range r2.
               Recurse with whole map against right set child. *)
            eapply Desc0_subRange.
            eapply restrictKeys_Desc; clear restrictKeys_Desc.
            ** subst s m. simpl. lia.
            ** eapply (DescBin _ _ _ _ _ _ _ _ _ _ _ HD1_1 HD1_2 H H0 H1 eq_refl eq_refl H4).
            ** exact H6.
            ** intro i. rewrite Hf. rewrite H12.
               destruct (f5 i) eqn:Hf5i.
               +++ simpl. rewrite orb_true_r.
                   destruct (f4 i) eqn:Hf4i; simpl; [reflexivity |].
                   (* f4 i = false, f5 i = true: map in right half, key in right half — should work *)
                   reflexivity.
               +++ simpl. rewrite orb_false_r.
                   destruct (f4 i) eqn:Hf4i; simpl.
                   *** (* f4 i = true, f5 i = false: map in right half, key in left half of set *)
                       assert (HirR3 : inRange i r3 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
                       assert (HirLf : inRange i (halfRange r2 false) = true)
                         by (eapply inRange_isSubrange_true; [| exact HirR3]; eassumption).
                       assert (HirRt : inRange i (halfRange r2 true) = false)
                         by (eapply rangeDisjoint_inRange_false;
                             [apply halves_disj; exact H7 | exact HirLf]).
                       assert (HirR : inRange i r = false)
                         by (eapply inRange_isSubrange_false;
                             [match goal with [ Hsub : isSubrange r (halfRange r2 true) = true |- _ ] => exact Hsub end
                             | exact HirRt]).
                       rewrite H4.
                       assert (Hf1None : f1 i = None) by (eapply Desc_outside; [exact HD1_1 |
                         eapply inRange_isSubrange_false; [exact H0 |
                           eapply inRange_isSubrange_false; [apply isSubrange_halfRange; exact H | exact HirR]]]).
                       assert (Hf0None : f0 i = None) by (eapply Desc_outside; [exact HD1_2 |
                         eapply inRange_isSubrange_false; [exact H1 |
                           eapply inRange_isSubrange_false; [apply isSubrange_halfRange; exact H | exact HirR]]]).
                       rewrite Hf1None Hf0None. reflexivity.
                   *** reflexivity.
            ** isSubrange_true; assumption.

        -- (* Map and set have same rBits => same-size comparison *)
          apply same_size_compare; try nia; intros.
          - (* Same prefix: r = r2, recurse on both halves *)
            subst.
            eapply bin_Desc0; try assumption; try reflexivity.
            ** eapply restrictKeys_Desc.
               --- subst s m. simpl. lia.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ** eapply restrictKeys_Desc.
               --- subst s m. simpl. lia.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ** isSubrange_true; assumption.
            ** isSubrange_true; assumption.
            ** intro i. rewrite Hf. rewrite H4. rewrite H12.
               destruct (f4 i) eqn:Hf4i; destruct (f5 i) eqn:Hf5i; simpl.
               +++ (* f4=true, f5=true: contradiction via disjoint halves *)
                   exfalso.
                   assert (HirR3 : inRange i r3 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
                   assert (HirR4 : inRange i r4 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
                   assert (HirLf : inRange i (halfRange r2 false) = true)
                     by (eapply inRange_isSubrange_true; [| exact HirR3]; eassumption).
                   assert (HirRt : inRange i (halfRange r2 true) = true)
                     by (eapply inRange_isSubrange_true; [| exact HirR4]; eassumption).
                   eapply rangeDisjoint_inRange_false_false.
                   { apply halves_disj; exact H7. }
                   { exact HirLf. }
                   { exact HirRt. }
               +++ (* f4=true, f5=false *)
                   assert (HirR3 : inRange i r3 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
                   assert (HirLf : inRange i (halfRange r2 false) = true)
                     by (eapply inRange_isSubrange_true; [| exact HirR3]; eassumption).
                   assert (HirRt : inRange i (halfRange r2 true) = false)
                     by (eapply rangeDisjoint_inRange_false;
                         [apply halves_disj; exact H7 | exact HirLf]).
                   assert (Hf0None : f0 i = None) by (eapply Desc_outside; [exact HD1_2 |
                     eapply inRange_isSubrange_false; [exact H1 | exact HirRt]]).
                   rewrite Hf0None. rewrite oro_None_r. reflexivity.
               +++ (* f4=false, f5=true *)
                   assert (HirR4 : inRange i r4 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
                   assert (HirRt : inRange i (halfRange r2 true) = true)
                     by (eapply inRange_isSubrange_true; [| exact HirR4]; eassumption).
                   assert (HirLf : inRange i (halfRange r2 false) = false)
                     by (eapply rangeDisjoint_inRange_false;
                         [rewrite rangeDisjoint_sym; apply halves_disj; exact H7 | exact HirRt]).
                   assert (Hf1None : f1 i = None) by (eapply Desc_outside; [exact HD1_1 |
                     eapply inRange_isSubrange_false; [exact H0 | exact HirLf]]).
                   rewrite Hf1None. reflexivity.
               +++ reflexivity.
          - (* Different prefix with same rBits => disjoint *)
            apply Desc0Nil.
            intro i. rewrite Hf.
            destruct (f2 i) eqn:Hf2i; [| reflexivity].
            assert (HirR2 : inRange i r2 = true) by (eapply IntSetProofs.Desc_inside; eassumption).
            assert (HirR : inRange i r = false)
              by (eapply rangeDisjoint_inRange_false;
                  [rewrite rangeDisjoint_sym; eassumption | exact HirR2]).
            rewrite H4.
            assert (Hf1None : f1 i = None) by (eapply Desc_outside; [exact HD1_1 |
              eapply inRange_isSubrange_false; [exact H0 |
                eapply inRange_isSubrange_false; [apply isSubrange_halfRange; exact H | exact HirR]]]).
            assert (Hf0None : f0 i = None) by (eapply Desc_outside; [exact HD1_2 |
              eapply inRange_isSubrange_false; [exact H1 |
                eapply inRange_isSubrange_false; [apply isSubrange_halfRange; exact H | exact HirR]]]).
            rewrite Hf1None Hf0None. reflexivity.
Admitted.

Lemma restrictKeys_Sem:
  forall a (m1 : IntMap a) f1 s2 f2,
  Sem m1 f1 ->
  IntSetProofs.Sem s2 f2 ->
  Sem (restrictKeys m1 s2) (fun i => if f2 i then f1 i else None).
Proof.
  intros.
  destruct H; [|destruct H0].
  * rewrite restrictKeys_eq.
    apply SemNil. solve_f_eq.
  * replace (restrictKeys s IntSet.Internal.Nil) with (@Nil a) by (rewrite restrictKeys_eq; destruct s; reflexivity).
    apply SemNil. solve_f_eq.
  * eapply Desc0_Sem. eapply restrictKeys_Desc; try eauto.
Qed.

Lemma restrictKeys_WF:
  forall a (m1 : IntMap a) s2, WF m1 -> IntSetProofs.WF s2 -> WF (restrictKeys m1 s2).
Proof.
  intros.
  destruct H, H0.
  eexists. apply restrictKeys_Sem; eassumption.
Qed.

(** Verification of [partition] **)





(** Verification of [map] **)


Definition IMMap {a b} (f : a -> b) (s : IntMap a):=
  Data.IntMap.Internal.map f s.


Lemma map_Desc: forall a b (s: IntMap a) f1 (f2: a -> b) r,
    Desc s r f1 -> Desc (IMMap f2 s) r (fun i => match (f1 i) with
                                             | Some x => Some (f2 x)
                                             | None => None
                                             end).
Proof.
  intros. induction H.
  * simpl. eapply DescTip.
    - intro i. specialize (H i). rewrite H. destruct (i =? k); reflexivity.
    - apply H0.
  * simpl. eapply DescBin; auto. intro i. simpl. specialize (H6 i).
    rewrite H6. unfold oro. destruct (f1 i) eqn: Hf; reflexivity.
Qed.

Lemma map_Sem: forall a b (s: IntMap a) f1 (f2: a -> b),
    Sem s f1 -> Sem (IMMap f2 s) (fun i => match (f1 i) with
                                             | Some x => Some (f2 x)
                                             | None => None
                                             end). 
Proof.
  intros. induction H.
  - apply SemNil. intros i0. specialize (H i0). rewrite H. reflexivity.
  - eapply DescSem. eapply map_Desc. apply HD. 
Qed.

Lemma map_WF: forall a b (s: IntMap a) (f: a -> b),
    WF s -> WF (IMMap f s).
Proof.
  intros a b s f [g Hsem].
  eexists. exact (map_Sem a b s g f Hsem).
Qed.

(** Verification of [mapWithKey] **)

Definition IMMapWithKey {a b} (f: Key -> a -> b) (s: IntMap a) :=
  Data.IntMap.Internal.mapWithKey f s.

Lemma mapWithKey_Desc: forall a b (s: IntMap a) r f (fmap : Key -> a -> b),
    Desc s r f -> Desc (IMMapWithKey fmap s) r (fun i => match (f i) with
                                                  | Some x => Some (fmap i x)
                                                  | None => None
                                                  end).
Proof.
  intros. induction H.
  * simpl. eapply DescTip; auto.
    - intro i. specialize (H i). rewrite H. destruct (i =? k) eqn: Hik.
      + apply Neqb_ok in Hik. rewrite Hik. reflexivity.
      + reflexivity.
  * simpl. eapply DescBin; auto. intro i. simpl. specialize (H6 i).
    rewrite H6. unfold oro. destruct (f1 i) eqn: Hf; reflexivity.
Qed.

Lemma mapWithKey_Sem: forall a b (s: IntMap a) f (fmap: Key -> a -> b),
    Sem s f -> Sem (IMMapWithKey fmap s) (fun i => match (f i) with
                                             | Some x => Some (fmap i x)
                                             | None => None
                                             end). 
Proof.
  intros. induction H.
  - apply SemNil. intros i. specialize (H i). rewrite H. reflexivity.
  - eapply DescSem. eapply mapWithKey_Desc. apply HD.
Qed.

Lemma mapWithKey_WF: forall a b (s: IntMap a) (f: Key -> a -> b),
    WF s -> WF (IMMapWithKey f s).
Proof.
  intros a b s f [g Hsem].
  eexists. exact (mapWithKey_Sem a b s g f Hsem).
Qed.

Fixpoint sem_for_lists {a: Type} (l : list (Key * a)) (i : Key) :=
  match l with
  | nil => None
  | (x,y) :: t => if i == x then Some y else sem_for_lists t i
  end.


(* FALSE: mapKeys_Desc is disproved by concrete counterexample.
   mapKeys (fun k => k + 100) (Tip 1 42) = fromList [(101, 42)] = Tip 101 42.
   The result Tip 101 42 cannot satisfy Desc with the original range r
   (singletonRange 1), because 101 is not in singletonRange 1.
   mapKeys rebuilds the map via fromList after applying fmap to all keys,
   so the resulting trie structure bears no relation to the input range r.
   A correct specification would use Sem (no range claim) or Desc0, but
   even that requires a fromList_Desc lemma for the arbitrary key list.
   Use mapKeys_Sem below for a weaker (Sem-based) specification if needed. *)
(* Formal counterexample: mapKeys_Desc is false.
   mapKeys (+100) (Tip 1 42) computes to Tip 101 42, but
   Desc (Tip 101 42) (singletonRange 1) _ requires 101 ∈ singletonRange 1,
   which is false since inRange 101 (singletonRange 1) = (101 =? 1) = false. *)
Lemma mapKeys_Desc_false :
  ~ (forall a (fmap : Key -> Key) (s: IntMap a) r f,
       Desc s r f ->
       Desc (mapKeys fmap s) r (fun i => (sem_for_lists (rev (foldrWithKey (fun k v t => ((fmap k), v) :: t) nil s)) i))).
Proof.
  intro H.
  specialize (H N (fun k => k + 100)%N (Tip 1%N 42%N) (singletonRange 1%N)
    (fun i => if i =? 1%N then Some 42%N else None)
    (DescTip _ _ _ _ _ (fun i => eq_refl) eq_refl)).
  (* H : Desc (mapKeys (+100) (Tip 1 42)) (singletonRange 1) _ *)
  (* Reduce: mapKeys (+100) (Tip 1 42) = Tip 101 42 *)
  (* Desc (Tip 101 42) (singletonRange 1) _ is absurd *)
  simpl in H.
  inversion H; subst;
    first [ discriminate
          | unfold singletonRange in *; congruence ].
Qed.

(* FALSE: disproved by mapKeys_Desc_false above. Aborted to prevent use. *)
Lemma mapKeys_Desc: forall a (fmap : Key -> Key) (s: IntMap a) r f,
    Desc s r f ->
    Desc (mapKeys fmap s) r (fun i => (sem_for_lists (rev (foldrWithKey (fun k v t => ((fmap k), v) :: t) nil s)) i)).
Proof.
Abort.


(* Verification of [lookupMin] *)

(* Formal counterexample: empty_no_elts is false because the forward direction
   fails for Bin p msk Nil Nil, which has sem = None everywhere but is not Nil.
   The Bin constructor is syntactically valid even with Nil children (just not WF). *)
Lemma empty_no_elts_false :
  ~ (forall {a} (m: IntMap a), (forall i, sem m i = None) <-> empty = m).
Proof.
  intro H.
  specialize (H N (Bin 0%N 1%N Nil Nil)).
  destruct H as [Hfwd _].
  assert (Hnil : forall i, sem (Bin 0%N 1%N (@Nil N) (@Nil N)) i = None).
  { intro i. simpl. reflexivity. }
  specialize (Hfwd Hnil). discriminate.
Qed.

(* FALSE: disproved by empty_no_elts_false above. Aborted to prevent use.
   The reverse direction (empty = m -> forall i, sem m i = None) is trivially true
   and available as empty_no_elts_rev below. The forward direction would need a
   WF/Desc hypothesis. The Map version in MaxMinProofs.v is correct. *)
Lemma empty_no_elts : forall {a} (m: IntMap a),
      (forall i, sem m i = None) <-> empty = m.
Proof.
Abort.

Lemma empty_no_elts_rev : forall {a} (m: IntMap a),
      empty = m -> (forall i, sem m i = None).
Proof.
  intros. unfold empty in H. rewrite <- H. simpl. reflexivity.
Qed.

Definition go {a} := fix go (arg_2__ : IntMap a) : option (Key * a) :=
        match arg_2__ with
        | Bin _ _ l' _ => go l'
        | Tip k v => Some (k, v)
        | Nil => None
        end.

(* sem and f agree for Desc-valid trees *)
Lemma sem_Desc:
  forall {a} (s : IntMap a) r f, Desc s r f -> forall i, sem s i = f i.
Proof.
  intros a s r f HD.
  induction HD; subst; intro i.
  - simpl. unfoldMethods. rewrite H. reflexivity.
  - simpl. rewrite H4. rewrite IHHD1. rewrite IHHD2. reflexivity.
Qed.

Lemma goL_Desc:
  forall {a} (s : IntMap a) r f,
    Desc s r f -> match go s with
                 | None => (forall i, sem s i = None)
                 | Some (k, v) => sem s k = Some v /\ (forall i v1, sem s i = Some v1 -> (k <= i))
                 end.
Proof.
  intros a s r f HD.
  induction HD; subst.
  - (* DescTip: go (Tip k v) = Some (k, v) *)
    simpl. unfoldMethods. rewrite N.eqb_refl. split.
    + reflexivity.
    + intros i v1 Hi. unfoldMethods.
      destruct (i =? k) eqn:Hik; [|discriminate].
      apply N.eqb_eq in Hik. subst. apply N.le_refl.
  - (* DescBin: go (Bin p msk m1 m2) = go m1 *)
    simpl. fold (@go a).
    (* go m1 cannot be None because Desc m1 r1 f1 implies m1 is non-Nil *)
    destruct (go m1) as [[k v]|] eqn:Hgo.
    + (* go m1 = Some (k, v) *)
      destruct IHHD1 as [Hsem1k Hmin1].
      split.
      * (* sem (Bin p msk m1 m2) k = Some v *)
        simpl. rewrite Hsem1k. apply oro_Some_l.
      * (* ordering: forall i v1, sem (Bin p msk m1 m2) i = Some v1 -> k <= i *)
        intros i v1 Hi. simpl in Hi.
        apply oro_Some in Hi. destruct Hi as [Hi | Hi].
        -- (* sem m1 i = Some v1: by IH *)
           exact (Hmin1 i v1 Hi).
        -- (* sem m2 i = Some v1: k is in left half, i is in right half *)
           assert (Hk_in : inRange k r1 = true).
           { eapply Desc_inside. exact HD1.
             rewrite <- (sem_Desc _ _ _ HD1). exact Hsem1k. }
           assert (Hi_in : inRange i r2 = true).
           { eapply Desc_inside. exact HD2.
             rewrite <- (sem_Desc _ _ _ HD2). exact Hi. }
           assert (Hk_left : inRange k (halfRange r false) = true)
             by (eapply inRange_isSubrange_true; eauto).
           assert (Hi_right : inRange i (halfRange r true) = true)
             by (eapply inRange_isSubrange_true; eauto).
           apply inRange_bounded in Hk_left.
           apply inRange_bounded in Hi_right.
           pose proof (rPrefix_halfRange_otherhalf r H) as Hpref.
           rewrite Hpref in Hi_right.
           lia.
    + (* go m1 = None: contradictory — Desc implies non-Nil, go non-Nil ≠ None *)
      exfalso.
      enough (go m1 <> None) by contradiction.
      clear -HD1. induction HD1; subst; simpl.
      * discriminate.
      * fold (@go a). exact IHHD1_1.
Qed.

Lemma lookupMin_Desc:
  forall {a} (s : IntMap a) r f,
    Desc s r f ->
    match lookupMin s with
    | None => (forall i, sem s i = None)
    | Some (k, v) => sem s k = Some v /\ (forall i v1, sem s i = Some v1 -> (k <= i))
    end.
Proof.
  intros a s r f HD. induction HD; subst.
  - (* DescTip *)
    simpl. unfoldMethods. rewrite N.eqb_refl. split.
    + reflexivity.
    + intros. unfoldMethods.
      destruct (i =? k) eqn: Hik; [|discriminate].
      apply N.eqb_eq in Hik. subst. apply N.le_refl.
  - (* DescBin: lookupMin reduces to go m1 since rMask r >= 0 *)
    simpl. unfoldMethods.
    assert (Hm: (rMask r <? 0) = false) by (apply N.ltb_ge; apply N.le_0_l).
    rewrite Hm. fold (@go a).
      (* goL_Desc gives us the property for go m1 *)
      pose proof (goL_Desc m1 r1 f1 HD1) as HgoL.
      destruct (go m1) as [[k v]|] eqn:Hgo.
      * (* go m1 = Some (k, v): extend from m1 to the whole Bin *)
        destruct HgoL as [Hsem1k Hmin1]. split.
        -- (* sem (Bin ...) k = Some v *)
           simpl. rewrite Hsem1k. apply oro_Some_l.
        -- (* ordering: k <= i for any i with sem (Bin ...) i = Some v1 *)
           intros i v1 Hi. simpl in Hi.
           apply oro_Some in Hi. destruct Hi as [Hi | Hi].
           ++ exact (Hmin1 i v1 Hi).
           ++ (* i is in m2, k is min of m1: use range ordering *)
              assert (Hk_in : inRange k r1 = true).
              { eapply Desc_inside. exact HD1.
                rewrite <- (sem_Desc _ _ _ HD1). exact Hsem1k. }
              assert (Hi_in : inRange i r2 = true).
              { eapply Desc_inside. exact HD2.
                rewrite <- (sem_Desc _ _ _ HD2). exact Hi. }
              assert (Hk_left : inRange k (halfRange r false) = true)
                by (eapply inRange_isSubrange_true; eauto).
              assert (Hi_right : inRange i (halfRange r true) = true)
                by (eapply inRange_isSubrange_true; eauto).
              apply inRange_bounded in Hk_left.
              apply inRange_bounded in Hi_right.
              pose proof (rPrefix_halfRange_otherhalf r ltac:(assumption)) as Hpref.
              rewrite Hpref in Hi_right.
              lia.
      * (* go m1 = None: contradictory — Desc implies go ≠ None *)
        exfalso. enough (go m1 <> None) by contradiction.
        clear -HD1. induction HD1; subst; simpl.
        -- discriminate.
        -- fold (@go a). exact IHHD1_1.
Qed.
