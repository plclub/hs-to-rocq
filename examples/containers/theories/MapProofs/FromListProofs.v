Require Import MapProofs.Common.
Set Bullet Behavior "Strict Subproofs".
Require Import MapProofs.Bounds.
Require Import MapProofs.Tactics.
Require Import MapProofs.InsertProofs.
Require Import MapProofs.ToListProofs.
Require Import MapProofs.UnionIntersectDifferenceProofs.
Require Import Coq.Sorting.Sorted.
Require Import SortedUtil.
Require Import Coq.Program.Tactics.
Require Import HsToRocq.DeferredFix.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.ZArith.Zcomplements.
Require Proofs.Data.Foldable.


Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Verification of [fromDistinctAscList] *)

(** *** Helper lemmas shared with [fromList] *)

Lemma Z_shiftr_pos:
  forall x, (1 < x -> 1 <= Z.shiftr x 1)%Z.
Proof.
  intros.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2^1)%Z with 2%Z by reflexivity.
  assert (2 <= x)%Z by lia. clear H.
  apply Z.div_le_mono with (c := 2%Z) in H0.
  apply H0.
  lia.
Qed.

Lemma Z_shiftl_pos:
  forall x, (1 <= x -> 1 <= Z.shiftl x 1)%Z.
Proof.
  intros.
  rewrite Z.shiftl_mul_pow2 by lia.
  lia.
Qed.

Lemma Z_shiftr_lt:
  forall x, (1 <= x -> Z.shiftr x 1 < x)%Z.
Proof.
  intros.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2^1)%Z with 2%Z by reflexivity.
  apply Z.div_lt; lia.
Qed.

Lemma mul_pow_sub:
  forall sz, (0 < sz)%Z -> (2 * 2 ^ (sz - 1) = 2^sz)%Z.
Proof.
  intros.
  rewrite <- Z.pow_succ_r by lia.
  f_equal.
  lia.
Qed.

(*Maps are sorted only by keys*)
Local Definition lt : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in ( _GHC.Base.<_ e1 e2) = true.

(*The analogue of [sem] for lists - returns the first value associated with
a given key, or None if no such key exists. We will use this to
specify several lemmas in [fromList] rather than List.elem*)
Fixpoint sem_for_lists (l : list (e * a)) (i : e) :=
  match l with
  | nil => None
  | (x,y) :: t => if i == x then Some y else sem_for_lists t i
  end.

Lemma sem_list_app: forall i xs ys,
  sem_for_lists (xs ++ ys) i = sem_for_lists xs i ||| sem_for_lists ys i.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. destruct (i == e0) eqn : ?. reflexivity.
    apply IHxs.
Qed.

Lemma toList_sem'':
  forall s lb ub, Bounded s lb ub ->
  forall i, sem s i = sem_for_lists (toList s) i.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. rewrite IHBounded1. rewrite IHBounded2. rewrite toList_Bin.
    rewrite sem_list_app. rewrite app_comm_cons. rewrite sem_list_app.
    simpl. unfold SomeIf. rewrite oro_assoc. reflexivity.
Qed.

Definition safeHd {a} : list (e * a) -> option e := fun xs =>
  match xs with nil => None | ((x, y)::_) => Some x end.

(** *** Semantic functions for Stack and State *)

Fixpoint stack_sem (stk : Stack e a) (i : e) : option a :=
  match stk with
  | Nada => None
  | Push x v t stk' => SomeIf (i == x) v ||| sem t i ||| stack_sem stk' i
  end.

(** [stack_sem_rev] puts entries in reversed order: older (deeper) entries first.
    This matches the order in which [foldl'Stack] processes ascending entries,
    so [|||] associativity alone suffices — no commutativity needed. *)
Fixpoint stack_sem_rev (stk : Stack e a) (i : e) : option a :=
  match stk with
  | Nada => None
  | Push x v t stk' => stack_sem_rev stk' i ||| sem t i ||| SomeIf (i == x) v
  end.

Fixpoint stack_size (stk : Stack e a) : Z :=
  match stk with
  | Nada => 0
  | Push _ _ t stk' => 1 + size t + stack_size stk'
  end.

Definition state_sem (st : FromDistinctMonoState e a) (i : e) : option a :=
  match st with
  | State0 stk => stack_sem stk i
  | State1 t stk => sem t i ||| stack_sem stk i
  end.

(** [state_sem_asc] uses [stack_sem_rev] — for ascending construction only. *)
Definition state_sem_asc (st : FromDistinctMonoState e a) (i : e) : option a :=
  match st with
  | State0 stk => stack_sem_rev stk i
  | State1 t stk => stack_sem_rev stk i ||| sem t i
  end.

Definition state_size (st : FromDistinctMonoState e a) : Z :=
  match st with
  | State0 stk => stack_size stk
  | State1 t stk => size t + stack_size stk
  end.

(** *** Well-formedness of Stack for ascending lists *)

Definition stack_ub (stk : Stack e a) : bound :=
  match stk with
  | Nada => None
  | Push x _ _ _ => Some x
  end.

Inductive WF_Stack_Asc : Stack e a -> bound -> Prop :=
  | WF_Nada_Asc : forall ub,
      WF_Stack_Asc Nada ub
  | WF_Push_Asc : forall x v t stk ub,
      Bounded t (stack_ub stk) (Some x) ->
      isUB ub x = true ->
      WF_Stack_Asc stk (Some x) ->
      WF_Stack_Asc (Push x v t stk) ub.

Lemma WF_Stack_Asc_relax_ub :
  forall stk ub1 ub2,
  WF_Stack_Asc stk ub1 ->
  (forall x, isUB ub1 x = true -> isUB ub2 x = true) ->
  WF_Stack_Asc stk ub2.
Proof.
  intros stk ub1 ub2 HWF Hweaken.
  inversion HWF as [| ? ? ? ? ? HBt Hub HWFstk']; subst.
  - constructor.
  - apply WF_Push_Asc; [assumption | apply Hweaken; assumption | assumption].
Qed.

Lemma WF_Stack_Asc_isLB_bound :
  forall stk x,
  WF_Stack_Asc stk (Some x) ->
  isLB (stack_ub stk) x = true.
Proof.
  intros stk x HWF.
  inversion HWF as [| ? ? ? ? ? _ Hub_x _]; subst.
  - simpl. reflexivity.
  - simpl stack_ub. simpl isLB. simpl isUB in Hub_x. exact Hub_x.
Qed.

(** *** Helper lemmas for [bin] *)

Lemma bin_Bounded :
  forall x v (l r : Map e a) lb ub,
  Bounded l lb (Some x) ->
  Bounded r (Some x) ub ->
  isLB lb x = true ->
  isUB ub x = true ->
  size l = size r ->
  Bounded (bin x v l r) lb ub.
Proof.
  intros x v l r lb ub HBl HBr Hlb Hub Hszeq.
  unfold bin. simpl.
  eapply BoundedBin; try eassumption.
  - rewrite !size_size. lia.
  - unfold balance_prop, delta, fromInteger, Num_Int__, Num_Integer__. rewrite Hszeq. lia.
Qed.

Lemma bin_size :
  forall x v (l r : Map e a),
  size (bin x v l r) = (1 + size l + size r)%Z.
Proof.
  intros. unfold bin. cbn [size]. rewrite !size_size.
  unfold op_zp__, Num_Int__, fromInteger, Num_Integer__. lia.
Qed.

Lemma bin_sem :
  forall x v (l r : Map e a) i,
  sem (bin x v l r) i = sem l i ||| SomeIf (i == x) v ||| sem r i.
Proof.
  intros. unfold bin. simpl. reflexivity.
Qed.

(** *** Size correctness of [fromDistinctAscList_linkTop] *)

Lemma linkTop_asc_size :
  forall r stk,
  state_size (fromDistinctAscList_linkTop r stk) = state_size (State1 r stk).
Proof.
  intros r stk. revert r.
  induction stk as [kx vx s stk IHstk | ]; intros r.
  - (* Push *)
    simpl fromDistinctAscList_linkTop.
    destruct r as [rsz rv rvv rl rr | ].
    + destruct s as [lsz lv lvv ll lr | ].
      * unfold op_zeze__, Eq_Integer___, op_zeze____.
        destruct (Z.eqb_spec rsz lsz).
        -- rewrite IHstk. cbn [state_size stack_size].
           rewrite bin_size. lia.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
  - (* Nada *) destruct r; reflexivity.
Qed.

(** *** Correctness of [next] (ascending) — size only *)

Definition next_asc (st : FromDistinctMonoState e a) (kx : e) (vx : a) : FromDistinctMonoState e a :=
  match st with
  | State0 stk => fromDistinctAscList_linkTop (Bin #1 kx vx Tip Tip) stk
  | State1 l stk => State0 (Push kx vx l stk)
  end.

Lemma next_asc_size :
  forall st kx vx,
  state_size (next_asc st kx vx) = (1 + state_size st)%Z.
Proof.
  intros. destruct st.
  - unfold next_asc. rewrite linkTop_asc_size.
    cbn [state_size size stack_size].
    unfold op_zp__, Num_Int__, fromInteger, Num_Integer__. lia.
  - cbn [next_asc state_size stack_size]. lia.
Qed.

Lemma foldl'_next_asc_size :
  forall xs st,
  state_size (Data.Foldable.foldl' (fun st p => let '(kx, vx) := p in next_asc st kx vx) st xs) =
  (Z.of_nat (length xs) + state_size st)%Z.
Proof.
  induction xs as [| p xs]; intros.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_nil. simpl. lia.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_cons. destruct p as [kx vx].
    rewrite IHxs. rewrite next_asc_size. simpl length. lia.
Qed.

(** *** Bounded validity of [foldl'Stack] with [link] (ascending) *)

Lemma foldl'Stack_link_asc_valid :
  forall stk (acc : Map e a) lb,
  WF_Stack_Asc stk lb ->
  Bounded acc (stack_ub stk) None ->
  Bounded (foldl'Stack (fun r kx x l => link kx x l r) acc stk) None None /\
  size (foldl'Stack (fun r kx x l => link kx x l r) acc stk) = size acc + stack_size stk /\
  (forall i, sem (foldl'Stack (fun r kx x l => link kx x l r) acc stk) i =
             stack_sem_rev stk i ||| sem acc i).
Proof.
  induction stk as [kx vx s stk IHstk | ]; intros acc lb HWF HBacc.
  - (* Push *)
    inversion HWF as [| ? ? ? ? ? HBt Hub HWFstk]; subst; clear HWF.
    simpl foldl'Stack.
    assert (Hlb_kx : isLB (stack_ub stk) kx = true). {
      inversion HWFstk; subst; simpl; try reflexivity.
      assumption.
    }
    assert (HBlink : Desc (link kx vx s acc) (stack_ub stk) None
                       (1 + size s + size acc)
                       (fun i => sem s i ||| SomeIf (i == kx) vx ||| sem acc i)).
    { applyDesc e (@link_Desc e a). solve_Desc e. }
    set (la := link kx vx s acc) in *.
    assert (HB_la : Bounded la (stack_ub stk) None). {
      apply HBlink. intros; assumption.
    }
    assert (Hsz_la : size la = #1 + size s + size acc). {
      apply HBlink. intros; assumption.
    }
    assert (Hsem_la : forall i, sem la i = sem s i ||| SomeIf (i == kx) vx ||| sem acc i). {
      apply HBlink. intros ? ? ? HH. exact HH.
    }
    specialize (IHstk la (Some kx) HWFstk HB_la).
    destruct IHstk as [IH1 [IH2 IH3]].
    split; [| split].
    + assumption.
    + cbn [stack_size]. rewrite IH2. rewrite Hsz_la.
      unfold op_zp__, Num_Int__, Num_Integer__, fromInteger. lia.
    + intros i. rewrite IH3. rewrite Hsem_la.
      simpl stack_sem_rev. rewrite !oro_assoc. reflexivity.
  - (* Nada *)
    simpl. split; [| split].
    + solve_Bounded e.
    + lia.
    + intros. reflexivity.
Qed.

(** *** WF state invariant for ascending construction *)

Inductive WF_State_Asc2 : FromDistinctMonoState e a -> bound -> Prop :=
  | WFSA_State0 : forall stk ub,
      WF_Stack_Asc stk ub ->
      WF_State_Asc2 (State0 stk) ub
  | WFSA_State1 : forall t stk ub,
      Bounded t (stack_ub stk) ub ->
      WF_Stack_Asc stk ub ->
      WF_State_Asc2 (State1 t stk) ub.

Lemma linkTop_asc_WF2 :
  forall r stk ub,
  Bounded r (stack_ub stk) ub ->
  WF_Stack_Asc stk ub ->
  WF_State_Asc2 (fromDistinctAscList_linkTop r stk) ub.
Proof.
  intros r stk. revert r.
  induction stk as [kx vx s stk IHstk | ]; intros r ub HBr HWF.
  - (* Push *)
    simpl fromDistinctAscList_linkTop.
    inversion HWF as [| ? ? ? ? ? HBs Hub HWFstk]; subst; clear HWF.
    destruct r as [rsz rv rvv rl rr | ].
    + destruct s as [lsz lv lvv ll lr | ].
      * unfold op_zeze__, Eq_Integer___, op_zeze____.
        destruct (Z.eqb_spec rsz lsz).
        -- (* sizes match: recurse *)
           apply IHstk.
           ++ apply bin_Bounded; try assumption.
              ** (* isLB (stack_ub stk) kx *)
                 assert (HlbLv : isLB (stack_ub stk) lv = true) by
                   (inversion HBs; assumption).
                 assert (HubLv : lv < kx = true) by
                   (inversion HBs; simpl isUB in *; assumption).
                 eapply isLB_lt; eassumption.
              ** (* size s = size r *) simpl. lia.
           ++ eapply WF_Stack_Asc_relax_ub. exact HWFstk.
              intros y Hy. simpl isUB in *.
              destruct ub; simpl in *; [order e | reflexivity].
        -- constructor; [assumption | apply WF_Push_Asc; assumption].
      * constructor; [assumption | apply WF_Push_Asc; assumption].
    + constructor; [assumption | apply WF_Push_Asc; assumption].
  - (* Nada *) simpl. destruct r; constructor; assumption.
Qed.

Lemma next_asc_WF2 :
  forall st kx vx ub,
  WF_State_Asc2 st (Some kx) ->
  isUB ub kx = true ->
  WF_State_Asc2 (next_asc st kx vx) ub.
Proof.
  intros st kx vx ub HWF Hub.
  destruct st as [stk | t stk].
  - (* State0: singleton then linkTop *)
    inversion HWF as [? ? HWFstk |]; subst. simpl next_asc.
    apply linkTop_asc_WF2.
    + apply BoundedBin with (sz := 1%Z).
      * apply BoundedTip.
      * apply BoundedTip.
      * (* isLB (stack_ub stk) kx *)
        apply WF_Stack_Asc_isLB_bound. assumption.
      * assumption.
      * simpl. lia.
      * unfold balance_prop, delta, fromInteger, Num_Int__, Num_Integer__. lia.
    + eapply WF_Stack_Asc_relax_ub. exact HWFstk.
      intros y Hy. simpl isUB in *.
      destruct ub; simpl in *; [order e | reflexivity].
  - (* State1: push onto stack *)
    inversion HWF as [| ? ? ? HBt HWFstk]; subst. simpl next_asc.
    constructor. apply WF_Push_Asc; assumption.
Qed.

(** *** [linkAll] on a WF state produces a valid tree *)

Lemma linkAll_asc_Bounded :
  forall st ub,
  WF_State_Asc2 st ub ->
  Bounded (fromDistinctAscList_linkAll st) None None.
Proof.
  intros st ub HWF.
  unfold fromDistinctAscList_linkAll.
  destruct st; inversion HWF; subst.
  - eapply (fun H1 H2 => proj1 (foldl'Stack_link_asc_valid _ _ _ H1 H2)).
    + eassumption.
    + apply BoundedTip.
  - eapply (fun H1 H2 => proj1 (foldl'Stack_link_asc_valid _ _ _ H1 H2)).
    + eassumption.
    + eapply Bounded_relax_ub_None. eassumption.
Qed.

(** *** Tracking WF through the [foldl'] loop *)

Lemma foldl'_next_asc_WF :
  forall xs st ub,
  WF_State_Asc2 st (safeHd xs) ->
  (xs = nil -> WF_State_Asc2 st ub) ->
  StronglySorted lt xs ->
  (forall x, sem_for_lists xs x <> None -> isUB ub x = true) ->
  WF_State_Asc2 (Data.Foldable.foldl' (fun st p => let '(kx, vx) := p in next_asc st kx vx) st xs) ub.
Proof.
  induction xs; intros st ub HWF0 HWFnil HSorted Hub.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_nil. apply HWFnil. reflexivity.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_cons. destruct a0 as [ka va].
    apply IHxs.
    + (* WF after processing (ka,va) *)
      destruct xs.
      * simpl safeHd.
        apply next_asc_WF2 with (ub := None).
        -- simpl safeHd in HWF0. assumption.
        -- simpl. reflexivity.
      * simpl safeHd. destruct p as [k2 v2].
        apply next_asc_WF2 with (ub := Some k2).
        -- simpl safeHd in HWF0. assumption.
        -- inversion HSorted as [| ? ? HSorted' HForall]; subst.
           inversion HForall as [| ? ? Ha_lt _]; subst.
           unfold lt in Ha_lt. destruct (ka, va). simpl in Ha_lt.
           simpl isUB. assumption.
    + intros Hnil. subst.
      apply next_asc_WF2 with (ub := ub).
      * simpl safeHd in HWF0. assumption.
      * apply Hub. simpl. rewrite Eq_refl. intro. discriminate.
    + inversion HSorted; subst. assumption.
    + intros x Helem. apply Hub. simpl. destruct (x == ka) eqn:?.
      * intro. discriminate.
      * assumption.
Qed.

(** *** Semantic correctness (ascending) using [state_sem_asc] *)

(** [linkTop] preserves [state_sem_asc]. *)
Lemma linkTop_asc_sem :
  forall r stk i,
  state_sem_asc (fromDistinctAscList_linkTop r stk) i = state_sem_asc (State1 r stk) i.
Proof.
  intros r stk. revert r.
  induction stk as [kx vx s stk IHstk | ]; intros r i.
  - (* Push *)
    simpl fromDistinctAscList_linkTop.
    destruct r as [rsz rv rvv rl rr | ].
    + destruct s as [lsz lv lvv ll lr | ].
      * unfold op_zeze__, Eq_Integer___, op_zeze____.
        destruct (Z.eqb_spec rsz lsz).
        -- rewrite IHstk. cbn [state_sem_asc stack_sem_rev].
           rewrite bin_sem. rewrite !oro_assoc. reflexivity.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
  - (* Nada *) destruct r; reflexivity.
Qed.

(** [next_asc] appends [SomeIf] to [state_sem_asc] on the right. *)
Lemma next_asc_sem :
  forall st kx vx i,
  state_sem_asc (next_asc st kx vx) i = state_sem_asc st i ||| SomeIf (i == kx) vx.
Proof.
  intros. destruct st.
  - unfold next_asc. rewrite linkTop_asc_sem.
    cbn [state_sem_asc].
    assert (sem (Bin #1 kx vx Tip Tip) i = SomeIf (i == kx) vx) as ->
      by (simpl; rewrite oro_None_r; reflexivity).
    reflexivity.
  - cbn [next_asc state_sem_asc stack_sem_rev].
    rewrite !oro_assoc. reflexivity.
Qed.

(** Tracking [state_sem_asc] through the [foldl'] loop. *)
Lemma foldl'_next_asc_sem :
  forall xs st i,
  state_sem_asc (Data.Foldable.foldl' (fun st p => let '(kx, vx) := p in next_asc st kx vx) st xs) i =
  state_sem_asc st i ||| sem_for_lists xs i.
Proof.
  induction xs as [| [kx vx] xs IHxs]; intros.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_nil. simpl. rewrite oro_None_r. reflexivity.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_cons.
    rewrite IHxs. rewrite next_asc_sem.
    simpl sem_for_lists. unfold SomeIf.
    destruct (i == kx); rewrite !oro_assoc; simpl oro; reflexivity.
Qed.

(** [linkAll] recovers [state_sem_asc] from the tree. *)
Lemma linkAll_asc_sem :
  forall st ub,
  WF_State_Asc2 st ub ->
  forall i, sem (fromDistinctAscList_linkAll st) i = state_sem_asc st i.
Proof.
  intros st ub HWF i.
  unfold fromDistinctAscList_linkAll.
  destruct st as [stk | t stk]; inversion HWF; subst.
  - (* State0 *)
    pose proof (foldl'Stack_link_asc_valid stk Tip ub) as HV.
    destruct HV as [_ [_ HVsem]]; [assumption | apply BoundedTip |].
    rewrite HVsem. simpl. rewrite oro_None_r. reflexivity.
  - (* State1 *)
    pose proof (foldl'Stack_link_asc_valid stk t ub) as HV.
    destruct HV as [_ [_ HVsem]]; [assumption | eapply Bounded_relax_ub_None; eassumption |].
    rewrite HVsem. reflexivity.
Qed.

(** *** Assembling [fromDistinctAscList_Desc] *)

Lemma fromDistinctAscList_Desc:
  forall xs,
  StronglySorted lt xs ->
  Desc (fromDistinctAscList xs) None None (List.length xs) (fun i => sem_for_lists xs i).
Proof.
  intros xs HSorted.
  unfold fromDistinctAscList, op_z2218U__.
  set (next := fun (arg_0__ : FromDistinctMonoState e a) (arg_1__ : (e * a)%type) =>
    match arg_0__, arg_1__ with
    | State0 stk, pair kx x => fromDistinctAscList_linkTop (Bin #1 kx x Tip Tip) stk
    | State1 l stk, pair kx x => State0 (Push kx x l stk)
    end).
  assert (Hnext_eq : forall st p, next st p = let '(kx, vx) := p in next_asc st kx vx). {
    intros. destruct st; destruct p; reflexivity.
  }
  set (final_state := Data.Foldable.foldl' next (State0 Nada) xs).
  assert (Hfinal_eq : final_state = Data.Foldable.foldl' (fun st p => let '(kx, vx) := p in next_asc st kx vx) (State0 Nada) xs). {
    unfold final_state. f_equal.
    extensionality st0. extensionality p0. apply Hnext_eq.
  }
  (* 1. Semantic correctness via state_sem_asc *)
  assert (Hsem_state : forall i, state_sem_asc final_state i = sem_for_lists xs i). {
    intros i. rewrite Hfinal_eq.
    rewrite foldl'_next_asc_sem. simpl. reflexivity.
  }
  (* 2. Size correctness *)
  assert (Hsize_state : state_size final_state = Z.of_nat (length xs)). {
    rewrite Hfinal_eq.
    rewrite foldl'_next_asc_size. simpl. lia.
  }
  (* 3. WF of final state *)
  assert (HWF : exists ub, WF_State_Asc2 final_state ub). {
    rewrite Hfinal_eq.
    destruct xs.
    - exists None. simpl.
      rewrite Proofs.Data.Foldable.Foldable_foldl'_nil.
      constructor. constructor.
    - exists None.
      apply foldl'_next_asc_WF with (ub := None).
      + simpl safeHd. constructor. constructor.
      + intros Hnil. discriminate.
      + assumption.
      + intros. simpl. reflexivity.
  }
  destruct HWF as [ub HWF_final].
  (* 4. linkAll produces valid Bounded tree *)
  assert (HBounded : Bounded (fromDistinctAscList_linkAll final_state) None None). {
    eapply linkAll_asc_Bounded. eassumption.
  }
  (* 5. linkAll preserves semantics via linkAll_asc_sem *)
  assert (Hsem_out : forall i, sem (fromDistinctAscList_linkAll final_state) i =
                                sem_for_lists xs i). {
    intro i. rewrite (linkAll_asc_sem _ ub HWF_final). apply Hsem_state.
  }
  (* 6. linkAll preserves size *)
  assert (Hsize_out : size (fromDistinctAscList_linkAll final_state) =
                      Z.of_nat (length xs)). {
    unfold fromDistinctAscList_linkAll.
    destruct final_state as [stk_f | t_f stk_f] eqn:Hfs.
    - inversion HWF_final; subst.
      pose proof (foldl'Stack_link_asc_valid stk_f Tip ub) as HV.
      destruct HV as [_ [HVsz _]]; [assumption | apply BoundedTip |].
      rewrite HVsz. simpl.
      rewrite <- Hsize_state. simpl. lia.
    - inversion HWF_final; subst.
      pose proof (foldl'Stack_link_asc_valid stk_f t_f ub) as HV.
      destruct HV as [_ [HVsz _]]; [assumption | eapply Bounded_relax_ub_None; eassumption |].
      rewrite HVsz. rewrite <- Hsize_state. simpl. lia.
  }
  (* Assemble *)
  apply showDesc. split; [| split].
  - assumption.
  - rewrite Hsize_out. rewrite List.hs_coq_list_length.
    rewrite Zlength_correct. reflexivity.
  - intros i. apply Hsem_out.
Qed.

(** ** Verification of [fromDistinctDescList] *)

(** *** Well-formedness of Stack for descending lists *)

Local Definition gt : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 > e2) = true.

Inductive WF_Stack_Desc : Stack e a -> bound -> Prop :=
  | WF_Nada_Desc : forall lb,
      WF_Stack_Desc Nada lb
  | WF_Push_Desc : forall x v t stk lb,
      Bounded t (Some x) (stack_ub stk) ->
      isLB lb x = true ->
      WF_Stack_Desc stk (Some x) ->
      WF_Stack_Desc (Push x v t stk) lb.

Lemma WF_Stack_Desc_relax_lb :
  forall stk lb1 lb2,
  WF_Stack_Desc stk lb1 ->
  (forall x, isLB lb1 x = true -> isLB lb2 x = true) ->
  WF_Stack_Desc stk lb2.
Proof.
  intros stk lb1 lb2 HWF Hweaken.
  inversion HWF as [| ? ? ? ? ? HBt Hlb HWFstk']; subst.
  - constructor.
  - apply WF_Push_Desc; [assumption | apply Hweaken; assumption | assumption].
Qed.

Lemma WF_Stack_Desc_isUB_bound :
  forall stk x,
  WF_Stack_Desc stk (Some x) ->
  isUB (stack_ub stk) x = true.
Proof.
  intros stk x HWF.
  inversion HWF as [| ? ? ? ? ? _ Hlb_x _]; subst.
  - simpl. reflexivity.
  - simpl stack_ub. simpl isUB. simpl isLB in Hlb_x. exact Hlb_x.
Qed.

(** *** Bounded validity of [foldl'Stack] with [link] (descending) *)

Lemma foldl'Stack_link_desc_valid :
  forall stk (acc : Map e a) lb,
  WF_Stack_Desc stk lb ->
  Bounded acc None (stack_ub stk) ->
  Bounded (foldl'Stack (fun l kx x r => link kx x l r) acc stk) None None /\
  size (foldl'Stack (fun l kx x r => link kx x l r) acc stk) = size acc + stack_size stk /\
  (forall i, sem (foldl'Stack (fun l kx x r => link kx x l r) acc stk) i =
             sem acc i ||| stack_sem stk i).
Proof.
  induction stk as [kx vx s stk IHstk | ]; intros acc lb HWF HBacc.
  - (* Push *)
    inversion HWF as [| ? ? ? ? ? HBt Hub HWFstk]; subst; clear HWF.
    simpl foldl'Stack. simpl stack_ub in HBacc.
    assert (Hlb_kx : isUB (stack_ub stk) kx = true). {
      inversion HWFstk; subst; simpl; try reflexivity.
      assumption.
    }
    assert (HBlink : Desc (link kx vx acc s) None (stack_ub stk)
                       (1 + size acc + size s)
                       (fun i => sem acc i ||| SomeIf (i == kx) vx ||| sem s i)).
    { applyDesc e (@link_Desc e a). solve_Desc e. }
    set (la := link kx vx acc s) in *.
    assert (HB_la : Bounded la None (stack_ub stk)). {
      apply HBlink. intros; assumption.
    }
    assert (Hsz_la : size la = #1 + size acc + size s). {
      apply HBlink. intros; assumption.
    }
    assert (Hsem_la : forall i, sem la i = sem acc i ||| SomeIf (i == kx) vx ||| sem s i). {
      apply HBlink. intros ? ? ? HH. exact HH.
    }
    specialize (IHstk la (Some kx) HWFstk HB_la).
    destruct IHstk as [IH1 [IH2 IH3]].
    split; [| split].
    + assumption.
    + cbn [stack_size]. rewrite IH2. rewrite Hsz_la.
      unfold op_zp__, Num_Int__, Num_Integer__, fromInteger. lia.
    + intros i. rewrite IH3. rewrite Hsem_la.
      simpl stack_sem. rewrite !oro_assoc. reflexivity.
  - (* Nada *)
    simpl. simpl stack_ub in HBacc. split; [| split].
    + solve_Bounded e.
    + lia.
    + intros. rewrite oro_None_r. reflexivity.
Qed.

(** *** Correctness of [fromDistinctDescList_linkTop] *)

Lemma linkTop_desc_sem :
  forall l stk i,
  state_sem (fromDistinctDescList_linkTop l stk) i = state_sem (State1 l stk) i.
Proof.
  intros l stk. revert l.
  induction stk as [kx vx s stk IHstk | ]; intros l i.
  - (* Push *)
    simpl fromDistinctDescList_linkTop.
    destruct l as [lsz lv lvv ll lr | ].
    + destruct s as [rsz rv rvv rl rr | ].
      * unfold op_zeze__, Eq_Integer___, op_zeze____.
        destruct (Z.eqb_spec lsz rsz).
        -- rewrite IHstk. cbn [state_sem stack_sem].
           rewrite bin_sem. rewrite !oro_assoc. reflexivity.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
  - (* Nada *) destruct l; reflexivity.
Qed.

Lemma linkTop_desc_size :
  forall l stk,
  state_size (fromDistinctDescList_linkTop l stk) = state_size (State1 l stk).
Proof.
  intros l stk. revert l.
  induction stk as [kx vx s stk IHstk | ]; intros l.
  - (* Push *)
    simpl fromDistinctDescList_linkTop.
    destruct l as [lsz lv lvv ll lr | ].
    + destruct s as [rsz rv rvv rl rr | ].
      * unfold op_zeze__, Eq_Integer___, op_zeze____.
        destruct (Z.eqb_spec lsz rsz).
        -- rewrite IHstk. cbn [state_size stack_size].
           rewrite bin_size. lia.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
  - (* Nada *) destruct l; reflexivity.
Qed.

(** *** Correctness of [next] (descending) *)

Definition next_desc (st : FromDistinctMonoState e a) (kx : e) (vx : a) : FromDistinctMonoState e a :=
  match st with
  | State0 stk => fromDistinctDescList_linkTop (Bin #1 kx vx Tip Tip) stk
  | State1 r stk => State0 (Push kx vx r stk)
  end.

Lemma next_desc_sem :
  forall st kx vx i,
  state_sem (next_desc st kx vx) i = SomeIf (i == kx) vx ||| state_sem st i.
Proof.
  intros. destruct st.
  - unfold next_desc. rewrite linkTop_desc_sem.
    cbn [state_sem].
    assert (sem (Bin #1 kx vx Tip Tip) i = SomeIf (i == kx) vx) as ->
      by (simpl; rewrite oro_None_r; reflexivity).
    reflexivity.
  - cbn [next_desc state_sem stack_sem].
    rewrite !oro_assoc. reflexivity.
Qed.

Lemma next_desc_size :
  forall st kx vx,
  state_size (next_desc st kx vx) = (1 + state_size st)%Z.
Proof.
  intros. destruct st.
  - unfold next_desc. rewrite linkTop_desc_size.
    cbn [state_size size stack_size].
    unfold op_zp__, Num_Int__, fromInteger, Num_Integer__. lia.
  - cbn [next_desc state_size stack_size]. lia.
Qed.

(** *** Semantic correctness of [foldl'] over [next_desc] *)

(** Note: the fold accumulates entries in reverse order compared to the input list,
    so we track [sem_for_lists (rev xs)] here. The final theorem converts back using
    the sortedness condition. *)
Lemma foldl'_next_desc_sem :
  forall xs st i,
  state_sem (Data.Foldable.foldl' (fun st p => let '(kx, vx) := p in next_desc st kx vx) st xs) i =
  sem_for_lists (rev xs) i ||| state_sem st i.
Proof.
  induction xs as [| p xs IHxs]; intros.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_nil. simpl. reflexivity.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_cons.
    destruct p as [kx vx].
    rewrite IHxs. rewrite next_desc_sem.
    simpl rev. rewrite sem_list_app. simpl sem_for_lists.
    rewrite !oro_assoc. reflexivity.
Qed.

Lemma foldl'_next_desc_size :
  forall xs st,
  state_size (Data.Foldable.foldl' (fun st p => let '(kx, vx) := p in next_desc st kx vx) st xs) =
  (Z.of_nat (length xs) + state_size st)%Z.
Proof.
  induction xs as [| p xs]; intros.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_nil. simpl. lia.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_cons. destruct p as [kx vx].
    rewrite IHxs. rewrite next_desc_size. simpl length. lia.
Qed.

(** *** WF state invariant for descending construction *)

Inductive WF_State_Desc2 : FromDistinctMonoState e a -> bound -> Prop :=
  | WFSD_State0 : forall stk lb,
      WF_Stack_Desc stk lb ->
      WF_State_Desc2 (State0 stk) lb
  | WFSD_State1 : forall t stk lb,
      Bounded t lb (stack_ub stk) ->
      WF_Stack_Desc stk lb ->
      WF_State_Desc2 (State1 t stk) lb.

Lemma linkTop_desc_WF2 :
  forall l stk lb,
  Bounded l lb (stack_ub stk) ->
  WF_Stack_Desc stk lb ->
  WF_State_Desc2 (fromDistinctDescList_linkTop l stk) lb.
Proof.
  intros l stk. revert l.
  induction stk as [kx vx s stk IHstk | ]; intros l lb HBl HWF.
  - (* Push *)
    simpl fromDistinctDescList_linkTop.
    inversion HWF as [| ? ? ? ? ? HBs Hlb HWFstk]; subst; clear HWF.
    destruct l as [lsz lv lvv ll lr | ].
    + destruct s as [rsz rv rvv rl rr | ].
      * unfold op_zeze__, Eq_Integer___, op_zeze____.
        destruct (Z.eqb_spec lsz rsz).
        -- (* sizes match: recurse *)
           apply IHstk.
           ++ apply bin_Bounded; try assumption.
              ** (* isUB (stack_ub stk) kx *)
                 assert (Hub_rv : isUB (stack_ub stk) rv = true) by
                   (inversion HBs; assumption).
                 assert (Hkx_lt_rv : kx < rv = true) by
                   (inversion HBs; simpl isLB in *; assumption).
                 eapply isUB_lt; eassumption.
           ++ eapply WF_Stack_Desc_relax_lb. exact HWFstk.
              intros y Hy. simpl isLB in *.
              destruct lb; simpl in *; [order e | reflexivity].
        -- constructor; [assumption | apply WF_Push_Desc; assumption].
      * constructor; [assumption | apply WF_Push_Desc; assumption].
    + constructor; [assumption | apply WF_Push_Desc; assumption].
  - (* Nada *) simpl. destruct l; constructor; assumption.
Qed.

Lemma next_desc_WF2 :
  forall st kx vx lb,
  WF_State_Desc2 st (Some kx) ->
  isLB lb kx = true ->
  WF_State_Desc2 (next_desc st kx vx) lb.
Proof.
  intros st kx vx lb HWF Hlb.
  destruct st as [stk | t stk].
  - (* State0: singleton then linkTop *)
    inversion HWF as [? ? HWFstk |]; subst. simpl next_desc.
    apply linkTop_desc_WF2.
    + apply BoundedBin with (sz := 1%Z).
      * apply BoundedTip.
      * apply BoundedTip.
      * assumption.
      * (* isUB (stack_ub stk) kx *)
        apply WF_Stack_Desc_isUB_bound. assumption.
      * simpl. lia.
      * unfold balance_prop, delta, fromInteger, Num_Int__, Num_Integer__. lia.
    + eapply WF_Stack_Desc_relax_lb. exact HWFstk.
      intros y Hy. simpl isLB in *.
      destruct lb; simpl in *; [order e | reflexivity].
  - (* State1: push onto stack *)
    inversion HWF as [| ? ? ? HBt HWFstk]; subst. simpl next_desc.
    constructor. apply WF_Push_Desc; assumption.
Qed.

(** *** Tracking WF through the [foldl'] loop (descending) *)

Lemma foldl'_next_desc_WF :
  forall xs st lb,
  WF_State_Desc2 st (safeHd xs) ->
  (xs = nil -> WF_State_Desc2 st lb) ->
  StronglySorted gt xs ->
  (forall x, sem_for_lists xs x <> None -> isLB lb x = true) ->
  WF_State_Desc2 (Data.Foldable.foldl' (fun st p => let '(kx, vx) := p in next_desc st kx vx) st xs) lb.
Proof.
  induction xs; intros st lb HWF0 HWFnil HSorted Hlb.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_nil. apply HWFnil. reflexivity.
  - rewrite Proofs.Data.Foldable.Foldable_foldl'_cons. destruct a0 as [ka va].
    apply IHxs.
    + destruct xs.
      * simpl safeHd.
        apply next_desc_WF2 with (lb := None).
        -- simpl safeHd in HWF0. assumption.
        -- simpl. reflexivity.
      * simpl safeHd. destruct p as [k2 v2].
        apply next_desc_WF2 with (lb := Some k2).
        -- simpl safeHd in HWF0. assumption.
        -- inversion HSorted as [| ? ? HSorted' HForall]; subst.
           inversion HForall as [| ? ? Ha_gt _]; subst.
           unfold gt in Ha_gt. destruct (ka, va). simpl in Ha_gt.
           simpl isLB. order e.
    + intros Hnil. subst.
      apply next_desc_WF2 with (lb := lb).
      * simpl safeHd in HWF0. assumption.
      * apply Hlb. simpl. rewrite Eq_refl. intro. discriminate.
    + inversion HSorted; subst. assumption.
    + intros x Helem. apply Hlb. simpl. destruct (x == ka) eqn:?.
      * intro. discriminate.
      * assumption.
Qed.

(** *** [linkAll] on a WF descending state produces a valid tree *)

Lemma linkAll_desc_Bounded :
  forall st lb,
  WF_State_Desc2 st lb ->
  Bounded (fromDistinctDescList_linkAll st) None None.
Proof.
  intros st lb HWF.
  unfold fromDistinctDescList_linkAll.
  destruct st as [stk | t stk]; inversion HWF; subst.
  - eapply (fun H1 H2 => proj1 (foldl'Stack_link_desc_valid _ _ _ H1 H2)).
    + eassumption.
    + apply BoundedTip.
  - eapply (fun H1 H2 => proj1 (foldl'Stack_link_desc_valid _ _ _ H1 H2)).
    + eassumption.
    + eapply Bounded_relax_lb_None. eassumption.
Qed.

(** [linkAll] recovers [state_sem] from the tree (descending). *)
Lemma linkAll_desc_sem :
  forall st lb,
  WF_State_Desc2 st lb ->
  forall i, sem (fromDistinctDescList_linkAll st) i = state_sem st i.
Proof.
  intros st lb HWF i.
  unfold fromDistinctDescList_linkAll.
  destruct st as [stk | t stk]; inversion HWF; subst.
  - (* State0 *)
    pose proof (foldl'Stack_link_desc_valid stk Tip lb) as HV.
    destruct HV as [_ [_ HVsem]]; [assumption | apply BoundedTip |].
    rewrite HVsem. simpl. reflexivity.
  - (* State1 *)
    pose proof (foldl'Stack_link_desc_valid stk t lb) as HV.
    destruct HV as [_ [_ HVsem]]; [assumption | eapply Bounded_relax_lb_None; eassumption |].
    rewrite HVsem. reflexivity.
Qed.

(** For strictly descending lists with distinct keys, [sem_for_lists (rev xs)] = [sem_for_lists xs]. *)
Lemma sem_for_lists_rev_gt :
  forall xs i,
  StronglySorted gt xs ->
  sem_for_lists (rev xs) i = sem_for_lists xs i.
Proof.
  intros xs i HSorted.
  induction HSorted as [| [kx vx] xs HSorted IH HForall].
  - simpl. reflexivity.
  - simpl rev. rewrite sem_list_app. simpl sem_for_lists. rewrite IH.
    (* Need: sem_for_lists xs i ||| SomeIf (i == kx) vx = SomeIf (i == kx) vx ||| sem_for_lists xs i *)
    unfold SomeIf. destruct (i == kx) eqn:Heq.
    + (* i == kx: show sem_for_lists xs i = None since kx > all keys in xs *)
      assert (Hxs_none : sem_for_lists xs i = None). {
        clear -HForall Heq HEqLaws HOrdLaws.
        induction xs as [| [k' v'] xs IHxs].
        - reflexivity.
        - simpl. inversion HForall as [| ? ? Hgt_head Hforall_tail]; subst.
          assert (i == k' = false). {
            unfold gt in Hgt_head. order e.
          }
          rewrite H. apply IHxs. assumption.
      }
      rewrite Hxs_none. simpl. reflexivity.
    + (* i /= kx: trivial since SomeIf = None *)
      simpl. rewrite oro_None_r. reflexivity.
Qed.

(** *** Assembling [fromDistinctDescList_Desc] *)

(*If we look for an element in a map's list, it is the same as looking in the reverse of that list.
This is euivalent to saying that the first key, value pair that matches a given key is the same
as the last pair*)
Lemma sem_list_rev:
  forall m lb ub x,
  Bounded m lb ub ->
  sem_for_lists (toList m) x = sem_for_lists (rev (toList m)) x.
Proof.
  intros. generalize dependent x. induction H; intros.
  - simpl. reflexivity.
  - rewrite toList_Bin. rewrite rev_app_distr.
 simpl. rewrite <- app_assoc. simpl.
    rewrite sem_list_app. rewrite sem_list_app. rewrite <- IHBounded2.
    assert (forall {a} (x : a) l, x :: l = (x :: nil) ++ l). { intros.
    simpl. reflexivity. } rewrite H5. rewrite sem_list_app.
    rewrite (H5 _ _ (rev (toList s1))). rewrite sem_list_app.
    rewrite <- IHBounded1. repeat(erewrite <- toList_sem'').
    destruct (sem s1 x0) eqn : ?. simpl.
    assert (sem s2 x0 = None). { eapply sem_outside_below. apply H0. solve_Bounds e. }
    rewrite H6. simpl. assert (x0 == x = false) by solve_Bounds e. rewrite H7; reflexivity.
    simpl. destruct (x0 == x) eqn : ?. assert (sem s2 x0 = None). { eapply sem_outside_below.
    apply H0. solve_Bounds e. } rewrite H6. reflexivity. simpl. rewrite oro_None_r. reflexivity.
    apply H0. apply H.
Qed.

Lemma fromDistinctDescList_Desc:
  forall xs,
  StronglySorted gt xs ->
  Desc (fromDistinctDescList xs) None None (List.length xs) (fun i => sem_for_lists xs i).
Proof.
  intros xs HSorted.
  unfold fromDistinctDescList, op_z2218U__.
  set (next := fun (arg_0__ : FromDistinctMonoState e a) (arg_1__ : (e * a)%type) =>
    match arg_0__, arg_1__ with
    | State0 stk, pair kx x => fromDistinctDescList_linkTop (Bin #1 kx x Tip Tip) stk
    | State1 r stk, pair kx x => State0 (Push kx x r stk)
    end).
  assert (Hnext_eq : forall st p, next st p = let '(kx, vx) := p in next_desc st kx vx). {
    intros. destruct st; destruct p; reflexivity.
  }
  set (final_state := Data.Foldable.foldl' next (State0 Nada) xs).
  assert (Hfinal_eq : final_state = Data.Foldable.foldl' (fun st p => let '(kx, vx) := p in next_desc st kx vx) (State0 Nada) xs). {
    unfold final_state. f_equal.
    extensionality st0. extensionality p0. apply Hnext_eq.
  }
  (* 1. Semantic correctness: state_sem tracks sem_for_lists (rev xs) *)
  assert (Hsem_state : forall i, state_sem final_state i = sem_for_lists (rev xs) i). {
    intros i. rewrite Hfinal_eq.
    rewrite foldl'_next_desc_sem. simpl. rewrite oro_None_r. reflexivity.
  }
  (* 2. Size correctness *)
  assert (Hsize_state : state_size final_state = Z.of_nat (length xs)). {
    rewrite Hfinal_eq.
    rewrite foldl'_next_desc_size. simpl. lia.
  }
  (* 3. WF *)
  assert (HWF : exists lb, WF_State_Desc2 final_state lb). {
    rewrite Hfinal_eq.
    destruct xs.
    - exists None. simpl.
      rewrite Proofs.Data.Foldable.Foldable_foldl'_nil.
      constructor. constructor.
    - exists None.
      apply foldl'_next_desc_WF with (lb := None).
      + simpl safeHd. constructor. constructor.
      + intros Hnil. discriminate.
      + assumption.
      + intros. simpl. reflexivity.
  }
  destruct HWF as [lb HWF_final].
  assert (HBounded : Bounded (fromDistinctDescList_linkAll final_state) None None). {
    eapply linkAll_desc_Bounded. eassumption.
  }
  (* Semantics through linkAll — use linkAll_desc_sem then convert rev xs to xs *)
  assert (Hsem_out : forall i, sem (fromDistinctDescList_linkAll final_state) i =
                                sem_for_lists xs i). {
    intro i.
    rewrite (linkAll_desc_sem _ lb HWF_final).
    rewrite Hsem_state.
    apply sem_for_lists_rev_gt. assumption.
  }
  (* Size through linkAll *)
  assert (Hsize_out : size (fromDistinctDescList_linkAll final_state) =
                      Z.of_nat (length xs)). {
    unfold fromDistinctDescList_linkAll.
    destruct final_state as [stk_f | t_f stk_f] eqn:Hfs.
    - inversion HWF_final; subst.
      pose proof (foldl'Stack_link_desc_valid stk_f Tip lb) as HV.
      destruct HV as [_ [HVsz _]]; [assumption | apply BoundedTip |].
      rewrite HVsz. rewrite <- Hsize_state. simpl. lia.
    - inversion HWF_final; subst.
      pose proof (foldl'Stack_link_desc_valid stk_f t_f lb) as HV.
      destruct HV as [_ [HVsz _]]; [assumption | eapply Bounded_relax_lb_None; eassumption |].
      rewrite HVsz. rewrite <- Hsize_state. simpl. lia.
  }
  apply showDesc. split; [| split].
  - assumption.
  - rewrite Hsize_out. rewrite List.hs_coq_list_length.
    rewrite Zlength_correct. reflexivity.
  - intros i. apply Hsem_out.
Qed.

(** ** Verification of [combineEq] *)

(*Since [combineEq'] and [combineEq] are defined inside [fromAscList] (unlike in Data.Set), we define them here
and then prove equivalence*)

Fixpoint combineEq' {e} {a} `{EqLaws e} (x : e * a) (l : list (e * a) ) :=
  match x, l with
  |z, nil => z :: nil
  |(a, b), (c, d) :: t => if a == c then combineEq' (c, d) t else (a,b) :: combineEq' (c,d) t
  end.

(*The combineEq' from Data.Map (defined here to make combineEq'_equiv nicer*)
Definition old_combineEq' :=(fix combineEq' (arg_0__ : e * a) (arg_1__ : list (e * a)) {struct arg_1__} : list (e * a) :=
   let (kz, _) := arg_0__ in
   match arg_1__ with
   | nil => arg_0__ :: nil
   | (kx, xx) as x :: xs' => if _GHC.Base.==_ kx kz then combineEq' (kx, xx) xs' else arg_0__ :: combineEq' x xs'
   end).

Definition combineEq {e} {a} `{EqLaws e} (l : list (e * a)) :=
  match l with
  | nil => nil
  | x :: nil => x :: nil
  | x :: t => combineEq' x t
  end.

Lemma combineEq'_equiv:
  forall l x, combineEq' x l = old_combineEq' x l.
Proof.
  intros. revert x. induction l; intros.
  - simpl. destruct x. reflexivity.
  - simpl. destruct x. destruct a0. destruct (e0 == e1) eqn : ?.
    assert (e1 == e0 = true) by (order e). rewrite H. apply IHl.
    assert (e1 == e0 = false) by (order e). rewrite H. rewrite IHl.
    reflexivity.
Qed.


Definition fromAscList' (l : list (e * a)) :=
  fromDistinctAscList (combineEq l).


Lemma fromAscList_equiv: forall (l : list (e * a)),
  fromAscList' l = fromAscList l.
Proof.
  intros l. unfold fromAscList', fromAscList. destruct l.
  - simpl. reflexivity.
  -  unfold combineEq. rewrite combineEq'_equiv. unfold old_combineEq'.
     reflexivity.
Qed.

Definition fromDescList' (l : list (e * a)) :=
  fromDistinctDescList (combineEq l).

Lemma fromDescList_equiv: forall (l : list (e * a)),
  fromDescList' l = fromDescList l.
Proof.
  intros l. unfold fromDescList', fromDescList. destruct l.
  - simpl. reflexivity.
  -  unfold combineEq. rewrite combineEq'_equiv. unfold old_combineEq'.
     reflexivity.
Qed.

Definition combineEqGo : (e * a) -> list (e * a) -> list (e * a).
Proof.
  intros.
 apply (@combineEq' e a HEq HEqLaws). apply X.  apply X0.
Defined.

(* Too much duplication here *)

(*See if a key is a (key, value) list*)
Fixpoint key_elem (l : list (e * a)) i :=
  match l with
  | nil => false
  | (x, y) :: t => (x == i) || key_elem t i
  end.

(*This finds the last value associated with a key in a list*)
Fixpoint last_value (l : list (e * a)) i:=
  match l with
  | nil => None
  | (x, y) :: t => if (x == i) then match last_value t i with
                               | None => Some y
                               | Some z => Some z
                               end else last_value t i
  end.

(*This proves that the last_value does in fact find the last value, since it finds
the first value in the reversed list. It also justifies using either
[sem_for_lists (rev l)] or [last_value l] based on which is more convienent. For
[combineEq] and [fromDescList] (and similar), I use [last_value l], and in
from_list, I use [sem_for_lists (rev l)]*)
Lemma last_sem_equiv: forall l x,
  sem_for_lists (rev l) x = last_value l x.
Proof.
  intros. revert x; induction l; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. rewrite sem_list_app. rewrite IHl.
    simpl. destruct (e0 == x) eqn : ?. assert (x == e0 = true) by (order e).
    rewrite H. destruct (last_value l x) eqn : ?. simpl. reflexivity. simpl. reflexivity.
    assert (x == e0 = false) by (order e). rewrite H. rewrite oro_None_r. reflexivity.
Qed.

(*An element has a last occurrence iff it is in the list*)
Lemma last_iff_elem: forall l i,
  (exists v, last_value l i = Some v) <-> key_elem l i = true.
Proof.
  intros. revert  i. induction l; split; intros.
  - simpl in H. inversion H. inversion H0.
  - simpl in H. inversion H.
  - simpl. destruct a0.  simpl in H. destruct (e0 == i) eqn : ?.
    simpl. reflexivity. simpl. eapply IHl. apply H.
  - simpl. destruct a0. simpl in H. destruct (e0  == i) eqn : ?.
    destruct (last_value l i) eqn : ?. exists a1. reflexivity.
    exists a0. reflexivity. simpl in H. apply IHl. apply H.
Qed.

Local Definition le : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 <= e2) = true.

Lemma Forall_le_elem:
  forall x x0 xs,
  Forall (fun y => le (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x <= i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0.
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold le in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold le. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_le_last:
  forall x x0 xs,
  Forall (fun y => le (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x <= i = true).
Proof.
  intros.
  rewrite Forall_le_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed.


Local Definition ge : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 >= e2) = true.

Lemma Forall_ge_elem:
  forall x x0 xs,
  Forall (fun y => ge (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x >= i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0.
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold ge in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold ge. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_ge_last:
  forall x x0 xs,
  Forall (fun y => ge (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x >= i = true).
Proof.
  intros.
  rewrite Forall_ge_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed.

Lemma Forall_lt_elem:
  forall x x0 xs,
  Forall (fun y => lt (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x < i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0.
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold lt in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold lt. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_lt_last:
  forall x x0 xs,
  Forall (fun y => lt (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x < i = true).
Proof.
  intros.
  rewrite Forall_lt_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed.


Lemma Forall_gt_elem:
  forall x x0 xs,
  Forall (fun y => gt (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x > i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0.
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold gt in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold gt. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_gt_last:
  forall x x0 xs,
  Forall (fun y => gt (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x > i = true).
Proof.
  intros.
  rewrite Forall_gt_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed.


(*Note: This is significatly different than SetProofs. It is not enough that the keys are preserved,
we must show that each key is matched with its last value in the list*)
Lemma combineEqGo_spec:
  forall x xs,
  StronglySorted (fun x y => le x y) (x :: xs) ->
  forall P : list (e * a) -> Prop,
  (forall (ys: list (e * a)),
     StronglySorted (fun x y => lt x y) ys ->
     (forall i, last_value ys i = last_value (x :: xs) i) ->
     P ys) ->
  P (combineEqGo x xs).
Proof.
  intros x xs Hsorted.
  inversion Hsorted; subst; clear Hsorted.
  revert x H2.
  induction H1; intros x Hlt.
  * intros X HX; apply HX; clear X HX.
    + unfold lt. unfold le in Hlt. unfold combineEqGo. simpl. destruct x.
      constructor; constructor.
    + intro. unfold combineEqGo. simpl. destruct x. simpl. reflexivity.
  * inversion Hlt; subst; clear Hlt.
    simpl. unfold combineEqGo in *. simpl in *. destruct a0. destruct x.
    destruct_match.
    + eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - assumption.
      - intro i. rewrite Hiys. simpl.
        destruct (e0 == i) eqn:?, (e1 == i) eqn:?. destruct (last_value l i) eqn : ?.
        reflexivity. reflexivity. reflexivity. order e. reflexivity.
    + assert (Hlt : e1 < e0 = true) by (unfold le in H3; order e). clear H3 Heq.
      eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - constructor.
        ** eapply StronglySorted_R_ext; only 2: apply Hsortedys.
           intros. simpl. order e.
        ** apply Forall_lt_last.
           rewrite Forall_le_last in H.
           intros i v Hi. rewrite Hiys in Hi.  simpl in Hi. unfold lt.
           destruct (e0 == i) eqn : ?. order e. apply H in Hi. unfold le in Hi. order e.
      - intro i. simpl. rewrite Hiys. simpl. reflexivity.
Qed.

Lemma combineEqGo_spec2:
  forall x xs,
  StronglySorted (fun x y => ge x y) (x :: xs) ->
  forall P : list (e * a) -> Prop,
  (forall (ys: list (e * a)),
     StronglySorted (fun x y => gt x y) ys ->
     (forall i, last_value ys i = last_value (x :: xs) i) ->
     P ys) ->
  P (combineEqGo x xs).
Proof.
  intros x xs Hsorted.
  inversion Hsorted; subst; clear Hsorted.
  revert x H2.
  induction H1; intros x Hlt.
  * intros X HX; apply HX; clear X HX.
    + unfold lt. unfold ge in Hlt. unfold combineEqGo. simpl. destruct x.
      constructor; constructor.
    + intro. unfold combineEqGo. simpl. destruct x.  simpl. reflexivity.
  * inversion Hlt; subst; clear Hlt.
    simpl. unfold combineEqGo in *. simpl in *. destruct a0. destruct x.
    destruct_match.
    + eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - assumption.
      - intro i. rewrite Hiys. simpl.
        destruct (e0 == i) eqn:?, (e1 == i) eqn:?. destruct (last_value l i) eqn : ?.
        reflexivity. reflexivity. reflexivity. order e. reflexivity.
    + assert (Hlt : e1 > e0 = true) by (unfold ge in H3; order e). clear H3 Heq.
      eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - constructor.
        ** eapply StronglySorted_R_ext; only 2: apply Hsortedys.
           intros. simpl. order e.
        ** apply Forall_gt_last.
           rewrite Forall_ge_last in H.
           intros i v Hi. rewrite Hiys in Hi.  simpl in Hi. unfold lt.
           destruct (e0 == i) eqn : ?. order e. apply H in Hi. unfold ge in Hi. order e.
      - intro i. simpl. rewrite Hiys. simpl. reflexivity.
Qed.

Lemma combineEq_spec:
  forall xs,
  StronglySorted (fun x y => le x  y) xs ->
  forall P : list (e * a) -> Prop,
  (forall ys,
     StronglySorted (fun x y => lt x y) ys ->
     (forall i, last_value ys i = last_value xs i) ->
     P ys) ->
  P (combineEq xs).
Proof.
  intros xs Hsorted.
  inversion Hsorted.
  * intros X HX. apply HX. clear X HX.
    - constructor.
    - intro. reflexivity.
  * rewrite <- H1 in Hsorted. clear xs H0 H1.
    assert (combineEq (a0 :: l) = combineEqGo a0 l). {
    unfold combineEqGo. simpl. destruct l. simpl. destruct a0. reflexivity.
    reflexivity. } rewrite H0.
    apply combineEqGo_spec. assumption.
Qed.

Lemma combineEq_spec2:
  forall xs,
  StronglySorted (fun x y => ge x  y) xs ->
  forall P : list (e * a) -> Prop,
  (forall ys,
     StronglySorted (fun x y => gt x y) ys ->
     (forall i, last_value ys i = last_value xs i) ->
     P ys) ->
  P (combineEq xs).
Proof.
  intros xs Hsorted.
  inversion Hsorted.
  * intros X HX. apply HX. clear X HX.
    - constructor.
    - intro. reflexivity.
  * rewrite <- H1 in Hsorted. clear xs H0 H1.
    assert (combineEq (a0 :: l) = combineEqGo a0 l). {
    unfold combineEqGo. simpl. destruct l. simpl. destruct a0. reflexivity.
    reflexivity. } rewrite H0.
    apply combineEqGo_spec2. assumption.
Qed.


(** ** Verification of [fromAscList] *)

(*See whether a key, value pair is in a list, comparing the keys with Haskell equality
and the values with Coq equality. This will be used in place of List.In in the following
analogues of [Forall_forall]*)
Fixpoint weak_In (l : list (e * a)) (x : e * a) :=
  match l with
  | nil => False
  | (a,b) :: t => let (x0, y0) := x in (a == x0 = true) /\ b = y0 \/ weak_In t x
  end.

Lemma Forall_forall_lt:
  forall  (l : list (e * a)) t, Forall (lt t) l <-> (forall x, weak_In l x -> lt t x).
Proof.
  intros. split; intros; induction l; intros.
  - simpl in H0. destruct H0.
  - simpl in H0. destruct a0. destruct x. destruct H0. inversion H; subst.
    destruct H0. subst. destruct t. unfold lt in *. order e.
  - apply IHl. inversion H; subst. assumption. apply H0.
  - apply Forall_nil.
  - apply Forall_cons. simpl in H. destruct a0. apply H. left.
    split. apply Eq_Reflexive. reflexivity. simpl in H.
    destruct a0. apply IHl. intros. apply H. destruct x. right. assumption.
Qed.

Lemma Forall_forall_gt:
  forall  (l : list (e * a)) t, Forall (gt t) l <-> (forall x, weak_In l x -> gt t x).
Proof.
  intros. split; intros; induction l; intros.
  - simpl in H0. destruct H0.
  - simpl in H0. destruct a0. destruct x. destruct H0. inversion H; subst.
    destruct H0. subst. destruct t. unfold gt in *. order e.
  - apply IHl. inversion H; subst. assumption. apply H0.
  - apply Forall_nil.
  - apply Forall_cons. simpl in H. destruct a0. apply H. left.
    split. apply Eq_Reflexive. reflexivity. simpl in H.
    destruct a0. apply IHl. intros. apply H. destruct x. right. assumption.
Qed.

Lemma strongly_sorted_in_sem_lt: forall l x v,
  StronglySorted lt l ->
  sem_for_lists l x = Some v <-> weak_In l (x,v).
Proof.
  intros; revert x v; induction l; intros; split; intros.
  - inversion H0.
  - destruct H0.
  - simpl. simpl in H0. destruct a0. destruct (x == e0) eqn : ?.
    left. split. order e. inversion H0; subst; reflexivity.
    right. apply IHl. inversion H; subst; assumption. apply H0.
  - simpl in H0. simpl. destruct a0.
    destruct H0. destruct H0. subst. assert (x == e0 = true) by (order e).
    rewrite H1. reflexivity. inversion H; subst.
    rewrite Forall_forall_lt in H4. assert (A:=H0). apply H4 in H0. unfold lt in H0.
    assert (x == e0 = false) by (order e). rewrite H1. apply IHl. apply H3. apply A.
Qed.

Lemma strongly_sorted_in_sem_gt: forall l x v,
  StronglySorted gt l ->
  sem_for_lists l x = Some v <-> weak_In l (x,v).
Proof.
  intros; revert x v; induction l; intros; split; intros.
  - inversion H0.
  - destruct H0.
  - simpl. simpl in H0. destruct a0. destruct (x == e0) eqn : ?.
    left. split. order e. inversion H0; subst; reflexivity.
    right. apply IHl. inversion H; subst; assumption. apply H0.
  - simpl in H0. simpl. destruct a0.
    destruct H0. destruct H0. subst. assert (x == e0 = true) by (order e).
    rewrite H1. reflexivity. inversion H; subst.
    rewrite Forall_forall_gt in H4. assert (A:=H0). apply H4 in H0. unfold gt in H0.
    assert (x == e0 = false) by (order e). rewrite H1. apply IHl. apply H3. apply A.
Qed.

Lemma strongly_sorted_last_lt:
  forall l x,
  StronglySorted lt l ->
  last_value l x = sem_for_lists l x.
Proof.
  intros. revert x. induction H; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. destruct (x == e0) eqn : ?.
    rewrite Forall_forall_lt in H0.
    rewrite IHStronglySorted.
    destruct (sem_for_lists l x) eqn : ?.
    + rewrite strongly_sorted_in_sem_lt in Heqo. apply H0 in Heqo.
      unfold lt in Heqo. order e. apply H. destruct (e0 == x) eqn : ?. reflexivity.
    order e. assert (e0 == x = false) by (order e). rewrite H1. apply IHStronglySorted.
Qed.

Lemma strongly_sorted_last_gt:
  forall l x,
  StronglySorted gt l ->
  last_value l x = sem_for_lists l x.
Proof.
  intros. revert x. induction H; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. destruct (x == e0) eqn : ?.
    rewrite Forall_forall_gt in H0.
    rewrite IHStronglySorted.
    destruct (sem_for_lists l x) eqn : ?.
    + rewrite strongly_sorted_in_sem_gt in Heqo. apply H0 in Heqo.
      unfold gt in Heqo. order e. apply H. destruct (e0 == x) eqn : ?. reflexivity.
    order e. assert (e0 == x = false) by (order e). rewrite H1. apply IHStronglySorted.
Qed.


Lemma fromAscList_Desc:
  forall xs,
  StronglySorted (fun x y => le x y) xs ->
  Desc' (fromAscList xs) None None (fun i => last_value xs i).
Proof.
  intros. rewrite <- fromAscList_equiv. unfold fromAscList'.
  eapply combineEq_spec; only 1: assumption; intros ys HSorted Helem.
  apply fromDistinctAscList_Desc; only 1: assumption.
  intros s HB Hsz Hf.
  solve_Desc e. intros. rewrite <- Helem. rewrite strongly_sorted_last_lt.
  apply Hf. apply HSorted.
Qed.

(** ** Verification of [fromDescList] *)

Lemma fromDescList_Desc:
  forall xs,
  StronglySorted (fun x y => ge x y) xs ->
  Desc' (fromDescList xs) None None (fun i => last_value xs i).
Proof.
  intros. rewrite <- fromDescList_equiv. unfold fromDescList'.
  unfold fromDescList.
  eapply combineEq_spec2;  only 1: assumption; intros ys HSorted Helem.
  apply fromDistinctDescList_Desc; only 1: assumption.
  intros s HB Hsz Hf.
  solve_Desc e. intros. rewrite <- Helem. rewrite strongly_sorted_last_gt.
  apply Hf. apply HSorted.
Qed.

(** ** Verification of [fromList] *)

(** The verification of [fromList] should be similar to that of [fromDistinctAscList], only
that the condition is checked and -- if it fails -- we resort to a backup implementation. *)

(* The following definitions are copied from the local definitions of [fromList];
   my ltac foo failed to do that automatic.
*)

Definition fromList' :=
          fun (t0: Map e a) (xs: list (e * a)) =>
            let ins :=
              fun arg_2__ arg_3__ =>
                match arg_2__, arg_3__ with
                | t, pair k x => insert k x t
                end in
            Data.Foldable.foldl' ins t0 xs.

Definition not_ordered :=
          fun (arg_7__ : e) (arg_8__: list (e * a)) =>
            match arg_7__, arg_8__ with
            | _, nil => false
            | kx, cons (pair ky _) _ => kx GHC.Base.>= ky
            end .

Definition fromList_create_f : (Int -> list (e * a) -> Map e a * list (e * a) * list (e * a)) ->
(Int -> list (e * a) -> Map e a * list (e * a)  * list (e * a))
  := (fun create arg_11__ arg_12__ =>
      match arg_11__, arg_12__ with
      | _, nil => pair (pair Tip nil) nil
      | s, (cons xp xss as xs) =>
       if s GHC.Base.== #1 : bool
       then let 'pair kx x := xp in
         if not_ordered kx xss : bool
         then pair (pair (Bin #1 kx x Tip Tip) nil) xss else
         pair (pair (Bin #1 kx x Tip Tip) xss) nil else
         match create (Data.Bits.shiftR s #1) xs with
         | (pair (pair _ nil) _ as res) => res
         | pair (pair l (cons (pair ky y) nil)) zs =>
              pair (pair (insertMax ky y l) nil) zs
         | pair (pair l (cons (pair ky y) yss as ys)) _ =>
             if not_ordered ky yss : bool then pair (pair l nil) ys else
             let 'pair (pair r zs) ws := create (Data.Bits.shiftR s #1) yss in
                       pair (pair (link ky y l r) zs) ws
         end
       end).

Definition fromList_create : Int -> list (e * a) -> Map e a * list (e * a) * list (e * a)
  := deferredFix2 (fromList_create_f).

Definition fromList_go_f :=
  (fun (go: Int -> Map e a -> list (e * a) -> Map e a) (arg_28__ : Int)
   (arg_29__ : Map e a) (arg_30__: list (e * a)) =>
    match arg_28__, arg_29__, arg_30__ with
    | _, t, nil => t
    | _, t, cons (pair kx x) nil => insertMax kx x t
    | s, l, (cons (pair kx x) xss as xs) =>
          if not_ordered kx xss : bool then fromList' l xs else
          match fromList_create s xss with
          | pair (pair r ys) nil => go (Data.Bits.shiftL s #1) (link kx x l r) ys
          | pair (pair r _) ys => fromList' (link kx x l r) ys
          end
   end).

Definition fromList_go := deferredFix3 (fromList_go_f).

(** zeta-reduces exactly one (the outermost) [let] *)
Ltac zeta_one :=
  lazymatch goal with |- context A [let x := ?rhs in @?body x] =>
     let e' := eval cbv beta in (body rhs) in
     let e'' := context A [e'] in
     change e''
  end.

(* Identical to [fromDistinctAscList_create_eq] *)
Lemma fromList_create_eq:
  forall i xs, (1 <= i)%Z ->
  fromList_create i xs = fromList_create_f fromList_create i xs.
Proof.
  intros.
  change (uncurry fromList_create (i, xs) = uncurry (fromList_create_f fromList_create) (i, xs)).
  apply deferredFix_eq_on with
    (f := fun g => uncurry (fromList_create_f (curry g)))
    (P := fun p => (1 <= fst p)%Z)
    (R := fun x y => (1 <= fst x < fst y)%Z).
  * eapply wf_inverse_image with (R := fun x y => (1 <= x < y)%Z).
    apply Z.lt_wf with (z := 1%Z).
  * clear i xs H.
    intros g h x Px Heq.
    destruct x as [i xs]. simpl in *.
    unfold fromList_create_f.
    destruct_match; try reflexivity.
    repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1); try reflexivity.
    unfold curry.
    assert (1 < i)%Z by lia.
    assert (1 <= Z.shiftr i 1)%Z by (apply Z_shiftr_pos; lia).
    assert (Z.shiftr i 1 < i)%Z by (apply Z_shiftr_lt; lia).
    repeat expand_pairs. simpl.
    rewrite Heq by eauto.
    destruct_match; try reflexivity.
    rewrite Heq by eauto.
    reflexivity.
  * simpl; lia.
Qed.

(* We need to know that [create] returns no longer list than it receives.
   Like [fromDistinctAscList_create_preserves_length], just a few more cases.
 *)
Program Fixpoint fromList_create_preserves_length
  i xs {measure (Z.to_nat i)} :
  (1 <= i)%Z ->
  forall (P : Map e a * list (e * a) * list (e * a) -> Prop),
  ( forall s ys zs ,
    (length ys <= length xs)%nat ->
    P (s, ys, zs)
  ) ->
  P (fromList_create i xs) := _.
Next Obligation.
  intros.
  rename fromList_create_preserves_length into IH.
  rewrite fromList_create_eq by assumption.
  unfold fromList_create_f.
  destruct xs.
  * apply H0. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1).
    + destruct p. destruct_match.
      - apply H0. simpl. lia.
      - apply H0. simpl. lia.
    + assert (Z.to_nat (Bits.shiftR i #1) < Z.to_nat i)%nat. {
        apply Z2Nat.inj_lt.
        apply Z.shiftr_nonneg. lia.
        lia.
        apply Z_shiftr_lt; lia.
      }
      apply IH.
      - assumption.
      - apply Z_shiftr_pos; lia.
      - intros.
        destruct_match.
        ** apply H0. simpl in *. lia.
        ** apply IH.
           -- assumption.
           -- apply Z_shiftr_pos; lia.
           -- intros.
              repeat destruct_match.
              ++ apply H0. simpl in *. lia.
              ++ apply H0. simpl in *. lia.
              ++ apply H0. simpl in *. lia.
Qed.

Lemma fromList_go_eq:
  forall i s xs, (0 < i)%Z ->
  fromList_go i s xs = fromList_go_f fromList_go i s xs.
Proof.
  intros.
  change (deferredFix (fun g => uncurry (uncurry (fromList_go_f (curry (curry g))))) (i, s, xs) =
    uncurry (uncurry (fromList_go_f fromList_go)) (i, s, xs)).
  rewrite deferredFix_eq_on with
    (P := fun p => (1 <= fst (fst p))%Z)
    (R := fun x y => (length (snd x) < length (snd y))%nat); only 1: reflexivity.
  * apply well_founded_ltof with (f := fun x => length (snd x)).
  * intros g h p Px Heq.
    destruct p as [[x y] z].
    simpl in *.
    unfold fromList_go_f.
    destruct_match; try reflexivity.
    eapply fromList_create_preserves_length; try lia.
    intros s' ys zs Hlength.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    apply Heq.
    + apply Z_shiftl_pos.
      lia.
    + simpl. simpl in *. lia.
  * simpl. lia.
Qed.

Program Fixpoint fromList_create_Desc
  sz lb xs {measure (Z.to_nat sz)} :
  (0 <= sz)%Z ->
  not_ordered lb xs = false ->
(*   StronglySorted (fun x y => x < y = true) (lb :: xs) -> *)
  forall (P : Map e a * list (e * a) * list (e * a) -> Prop),
  ( forall s ys zs,
    Bounded s (Some lb) (safeHd ys) ->
    isUB (safeHd ys) lb = true ->
    xs = toList s ++ ys ++ zs->
    ys = nil \/ (size s = (2*2^sz-1)%Z /\ zs = nil) ->
    P (s, ys, zs)
  ) ->
  P (fromList_create (2^sz)%Z xs) := _.
Next Obligation.
  (* Coq 8.20 pre-introduces all obligation variables (sz, lb, xs, H, H0, P, H1).
     Revert the CPS continuation to recover the original proof structure. *)
  rename fromList_create_Desc into IH.
  rename H into Hnonneg. rename H0 into HheadOrdered.
  revert dependent P.
  rewrite fromList_create_eq
    by (enough (0 < 2^sz)%Z by lia; apply Z.pow_pos_nonneg; lia).
  unfold fromList_create_f.
  destruct xs.
  * intros X HX. apply HX. clear HX.
    - solve_Bounded e.
    - reflexivity.
    - reflexivity.
    - left. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    simpl in HheadOrdered.
    destruct (Z.eqb_spec (2^sz) 1) as [Heq_pow | Hneq_pow].
    + destruct p as [kx vx].
      destruct (not_ordered kx xs) eqn:Hord.
      - intros X HX. apply HX; clear HX.
        ++ solve_Bounded e.
        ++ reflexivity.
        ++ rewrite toList_Bin, toList_Tip, app_nil_r. reflexivity.
        ++ left. reflexivity.
      - intros X HX. apply HX; clear HX.
        ++ destruct xs as [|[ky vy] xs']; simpl in Hord; solve_Bounded e.
        ++ destruct xs as [|[ky vy] xs']; simpl in *; solve_Bounds e.
        ++ rewrite toList_Bin, toList_Tip, !app_nil_r, !app_nil_l. reflexivity.
        ++ right. split. rewrite size_Bin. rewrite Heq_pow. lia. reflexivity.
    + assert (~ (sz = 0))%Z by (intro; subst; simpl in Hneq_pow; congruence).
      assert (sz > 0)%Z by lia.
      replace ((Bits.shiftR (2 ^ sz)%Z 1%Z)) with (2^(sz - 1))%Z.
      Focus 2.
        unfold Bits.shiftR, Bits.instance_Bits_Int.
        rewrite Z.shiftr_div_pow2 by lia.
        rewrite Z.pow_sub_r by lia.
        reflexivity.
      assert (Z.to_nat (sz - 1) < Z.to_nat sz)%nat.
      { rewrite Z2Nat.inj_sub by lia.
        apply Nat.sub_lt.
        apply Z2Nat.inj_le.
        lia.
        lia.
        lia.
        replace (Z.to_nat 1) with 1 by reflexivity.
        lia.
      }
      eapply IH.
      ++ assumption.
      ++ lia.
      ++ eassumption.
      ++ intros l ys zs HBounded_l HisUB_l Hlist_l Hsize_l.
         destruct ys.
         + intros X HX. apply HX. clear HX.
           ** solve_Bounded e.
           ** assumption.
           ** assumption.
           ** left; reflexivity.
         + simpl in HBounded_l.
           destruct Hsize_l as [Hys_nil | [Hsize_l_eq Hzs_nil]]; try congruence.
           subst. rewrite app_nil_r in Hlist_l.
           destruct p0 as [ky vy].
           assert (isLB (Some lb) ky = true) by solve_Bounds e.
           destruct ys as [| [kz vz] ys'].
           -- intros X HX. apply HX; clear HX.
              ** assert (isUB None ky = true) by reflexivity.
                 applyDesc e (@insertMax_Desc e a).
              ** reflexivity.
              ** erewrite toList_insertMax by eassumption.
                 rewrite app_nil_l, <- app_assoc.
                 assumption.
              ** left; reflexivity.
           -- destruct (not_ordered ky ((kz, vz) :: ys')) eqn:Hord2.
              ++ intros X HX. apply HX; clear HX.
                 ** solve_Bounded e.
                 ** reflexivity.
                 ** rewrite app_nil_l. simpl in Hlist_l.
                    assumption.
                 ** left; reflexivity.
              ++ eapply IH; clear IH.
                 ** assumption.
                 ** lia.
                 ** eassumption.
                 ** simpl in Hord2.
                    intros r zs' zs'' HBounded_r HisUB_r Hlist_r Hsize_r.
                    intros X HX. apply HX. clear HX.
                    --- applyDesc e (@link_Desc e a).
                    --- solve_Bounds e.
                    --- erewrite toList_link by eassumption.
                        rewrite Hlist_l. rewrite Hlist_r.
                        rewrite <- !app_assoc.  reflexivity.
                    --- destruct Hsize_r as [?|[Hsize_r_eq Hzs'_nil]]; [left; assumption| right].
                        subst.
                        split; only 2: reflexivity.
                        applyDesc e (@link_Desc e a).
                        change (match 2 ^ (sz - 1) with
                                | 0 => 0 | Z.pos p => Z.pos p~0
                                | Z.neg p => Z.neg p~0 end)%Z
                          with (2 * 2 ^ (sz - 1))%Z in *.
                        change (match 2 ^ sz with
                                | 0 => 0 | Z.pos p => Z.pos p~0
                                | Z.neg p => Z.neg p~0 end)%Z
                          with (2 * 2 ^ sz)%Z in *.
                        rewrite mul_pow_sub in * by lia.
                        lia.
Qed.

Lemma foldl_foldl' : forall {b} f (x : b) (l: list (e * a)),
  Foldable.foldl f x l = Foldable.foldl' f x l.
Proof.
  intros. unfold Foldable.foldl'. reflexivity.
Qed.

Definition fromList'' :=
          fun (t0: Map e a) (xs: list (e * a)) =>
            let ins :=
              fun arg_2__ arg_3__ =>
                match arg_2__, arg_3__ with
                | t, pair k x => insert k x t
                end in
            Data.Foldable.foldl ins t0 xs.


Lemma fromList'_fromList'': forall m l,
  fromList' m l = fromList'' m l.
Proof.
  intros. unfold fromList'. unfold fromList''. rewrite <- (foldl_foldl' _ m l). reflexivity.
Qed.

Lemma fromList'_Desc:
  forall s l,
  Bounded s None None ->
  Desc' (fromList' s l) None None (fun i => sem_for_lists (rev l) i ||| sem s i).
Proof.
  intros. rewrite fromList'_fromList''.
  unfold fromList''.
  rewrite Foldable.hs_coq_foldl_list.
  revert s H.
  induction l.
  * intros.
    simpl.
    solve_Desc e. reflexivity.
  * intros.
    simpl. destruct a0.
    applyDesc e (@insert_Desc e a).
    applyDesc e IHl.
    solve_Desc e. f_solver e; rewrite sem_list_app in Heqo0.
    + rewrite Heqo1 in Heqo0. inversion Heqo0. reflexivity.
    + rewrite Heqo1 in Heqo0. inversion Heqo0. reflexivity.
    + rewrite Heqo1 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. rewrite Hsem in Hsem0.
      rewrite Hsem0 in Heqo0. assumption.
    + rewrite Heqo1 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
    + rewrite Heqo1 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
Qed.

(*In a well formed map, we can only find each key once in the list, so it doesn't matter
if we look in the list or the reverse list*)
Lemma sem_toList_reverse: forall m lb ub i,
  Bounded m lb ub ->
  sem_for_lists (rev (toList m)) i = sem_for_lists (toList m) i.
Proof.
  intros. revert i. induction H; intros.
  - simpl. reflexivity.
  - rewrite toList_Bin. rewrite rev_app_distr. rewrite sem_list_app.
    rewrite sem_list_app. simpl. rewrite sem_list_app.
    rewrite IHBounded2. simpl. rewrite IHBounded1. repeat (erewrite <- toList_sem'').
    destruct (sem s2 i) eqn : ?. assert (sem s1 i = None). { eapply sem_outside_above.
    apply H. unfold isUB. apply (sem_inside H0) in Heqo. destruct Heqo. order_Bounds e. }
    rewrite H5. simpl. assert (i == x = false) by solve_Bounds e. rewrite H6. reflexivity.
    simpl. destruct (i == x) eqn : ?. assert (sem s1 i = None). { eapply sem_outside_above.
    apply H. unfold isUB. order_Bounds e. } rewrite H5. simpl. reflexivity. simpl.
    rewrite oro_None_r. reflexivity. apply H. apply H0.
Qed.


Program Fixpoint fromList_go_Desc
  sz s xs {measure (length xs)} :
  (0 <= sz)%Z ->
  Bounded s None (safeHd xs) ->
  xs = nil \/ size s = (2*2^sz-1)%Z ->
  Desc' (fromList_go (2^sz)%Z s xs) None None
    (fun i => sem_for_lists (rev xs) i ||| sem s i) := _.
Next Obligation.
  (* Coq 8.20 pre-introduces sz, s, xs, H:(0<=sz), H0:Bounded, H1:disjunction.
     Desc' return type is NOT unfolded (no P pre-introduction). *)
  rename fromList_go_Desc into IH.
  rewrite fromList_go_eq by (apply Z.pow_pos_nonneg; lia).
  unfold fromList_go_f.
  destruct xs as [| [kx vx] [| [ky vy] xss]].
  * (* nil case *)
    solve_Desc e. reflexivity.
  * (* singleton case *)
    destruct H1; try congruence.
    simpl safeHd in *.
    assert (isUB None kx = true) by reflexivity.
    applyDesc e (@insertMax_Desc e a).
    solve_Desc e.
    intro i. rewrite Hsem. simpl.
    destruct (i == kx) eqn:Hieq; simpl.
    + assert (sem s i = None)
        by (eapply sem_outside_above; [eassumption | unfold isUB; order e]).
      rewrite H3. reflexivity.
    + rewrite oro_None_r. reflexivity.
  * (* 2+ case *)
    destruct H1; try congruence.
    repeat replace (#1) with 1%Z by reflexivity.
    replace ((Bits.shiftL (2 ^ sz)%Z 1))%Z with (2 ^ (1 + sz))%Z.
    Focus 2.
      unfold Bits.shiftL, Bits.instance_Bits_Int.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      lia.
    destruct (not_ordered kx ((ky,vy) :: xss)) eqn:Hord.
    -- (* not_ordered = true: use fromList' *)
       apply Bounded_relax_ub_None in H0.
       applyDesc e (@fromList'_Desc).
       solve_Desc e.
       intro i. rewrite Hsem. reflexivity.
    -- (* not_ordered = false: use fromList_create + recursive call *)
       pose proof (fromList_create_Desc sz kx ((ky,vy)::xss) H Hord) as Hcreate.
       apply Hcreate. clear Hcreate.
       intros l' ys zs HBounded_l' HisUB_l' Hlist_l' Hsize_l'.
       subst.
       simpl safeHd in *.
       applyDesc e (@link_Desc e a).
       destruct zs.
       ++ (* zs = nil: recursive IH call *)
          rewrite app_nil_r in Hlist_l'.
          assert (HIH : Desc' (fromList_go (2 ^ (1 + sz))%Z s0 ys) None None
                    (fun i => sem_for_lists (rev ys) i ||| sem s0 i)).
          { eapply IH.
            - rewrite Hlist_l'. simpl. rewrite length_app. lia.
            - lia.
            - assumption.
            - destruct Hsize_l' as [?|[Hsize_l'_eq ?]]; [left; assumption | right].
              subst. rewrite Hsz.
              change (match 2 ^ sz with
                      | 0 => 0 | Z.pos p => Z.pos p~0
                      | Z.neg p => Z.neg p~0 end)%Z
                with (2 * 2 ^ sz)%Z in *.
              change (match 2 ^ (1 + sz) with
                      | 0 => 0 | Z.pos p => Z.pos p~0
                      | Z.neg p => Z.neg p~0 end)%Z
                with (2 * 2 ^ (1 + sz))%Z in *.
              assert (Hpow_add: (2 ^ (1 + sz) = 2 * 2 ^ sz)%Z)
                by (rewrite Z.pow_add_r by lia; lia).
              lia. }
          eapply HIH. intros s_go HB_go _ Hsem_go.
          apply showDesc'. split; [assumption|].
          intro i.
            rewrite Hsem_go. rewrite Hlist_l'.
            simpl rev. rewrite rev_app_distr.
            rewrite !sem_list_app. simpl sem_for_lists. simpl_options.
            erewrite sem_toList_reverse by (try eassumption; eapply HBounded_l').
            erewrite <- toList_sem'' by (try eassumption; eapply HBounded_l').
            (* Replace sem s0 i with its definition to enable reflexivity *)
            try (match goal with H : forall i0, sem s0 i0 = _ |- _ => rewrite H end).
            destruct (sem s i) eqn:Hs_i; destruct (i == kx) eqn:Hieq;
              destruct (sem l' i) eqn:Hl'_i;
              simpl; simpl_options;
              try reflexivity;
              try (exfalso; inside_bounds; simpl isLB in *; simpl isUB in *;
                try order e;
                try (assert (kx <= i = true) by (rewrite (Eq_le_r i kx kx Hieq); order e); order e);
                (assert (isUB (Some kx) i = true) by (eapply sem_inside; eassumption);
                 assert (isLB (Some kx) i = true) by (eapply sem_inside; eassumption);
                 simpl isLB in *; simpl isUB in *; order e)).
       ++ (* zs <> nil: fromList' fallback with ys=nil *)
          destruct Hsize_l' as [Hys_nil | [? Habsurd]]; try congruence.
          rewrite Hys_nil in Hlist_l'. rewrite app_nil_l in Hlist_l'.
          rewrite Hlist_l'.
          apply Bounded_relax_ub_None in HB.
          (* Use fromList'_Desc via CPS to preserve outer Desc' structure *)
          eapply (@fromList'_Desc). exact HB.
          intros s_fl HB_fl _ Hsem_fl.
          apply showDesc'. split; [assumption|].
          (* Manual semantic proof — same pattern as zs=nil case *)
          intro i.
            rewrite Hsem_fl.
            simpl rev. rewrite !rev_app_distr.
            rewrite !sem_list_app. simpl sem_for_lists. simpl_options.
            erewrite sem_toList_reverse by eassumption.
            erewrite <- toList_sem'' by eassumption.
            (* Replace sem s0 i with its link definition and unfold SomeIf *)
            rewrite Hsem. unfold SomeIf.
            destruct (sem s i) eqn:Hs_i; destruct (i == kx) eqn:Hieq;
              destruct (sem l' i) eqn:Hl'_i;
              simpl; simpl_options;
              try reflexivity;
              try (exfalso; inside_bounds; simpl isLB in *; simpl isUB in *;
                try order e;
                try (assert (kx <= i = true) by (rewrite (Eq_le_r i kx kx Hieq); order e); order e);
                (assert (isUB (Some kx) i = true) by (eapply sem_inside; eassumption);
                 assert (isLB (Some kx) i = true) by (eapply sem_inside; eassumption);
                 simpl isLB in *; simpl isUB in *; order e)).
          (* Handle remaining goals: reflexivity for reducible cases,
             exfalso for impossible cases *)
          all: try solve [unfold SomeIf; simpl; simpl_options; reflexivity].
          all: try solve [unfold SomeIf, oro, "|||"; simpl; reflexivity].
          all: try solve [cbv [SomeIf oro]; simpl; reflexivity].
          all: try solve [exfalso; inside_bounds; simpl isLB in *; simpl isUB in *; order e].
          all: try solve [exfalso; inside_bounds; simpl isLB in *; simpl isUB in *;
            match goal with Heq : (_ == _) = true |- _ =>
              assert (kx <= i = true) by (rewrite (Eq_le_r _ _ _ Heq); order e) end; order e].
          all: try solve [exfalso;
            assert (isUB (Some kx) i = true) by (eapply sem_inside; eassumption);
            assert (isLB (Some kx) i = true) by (eapply sem_inside; eassumption);
            simpl isLB in *; simpl isUB in *; order e].
          all: rewrite sem_list_app; simpl sem_for_lists; destruct p; simpl; simpl_options; reflexivity.
Qed.

Lemma fromList_Desc:
  forall xs,
  Desc' (fromList xs) None None (fun i => sem_for_lists (rev xs) i).
Proof.
  intros.
  cbv beta delta [fromList].
  destruct xs as [ | ? [|??] ].
  * solve_Desc e. reflexivity.
  * destruct p. solve_Desc e. intros. simpl. destruct (i == e0); reflexivity.
  * fold fromList'. destruct p.
    zeta_one.
    fold not_ordered.
    zeta_one.
    fold fromList_create_f.
    fold fromList_create.
    zeta_one.
    fold fromList_go_f.
    fold fromList_go.
    zeta_one.
    destruct_match.
    - applyDesc e fromList'_Desc.
      solve_Desc e. simpl. setoid_rewrite sem_list_app. setoid_rewrite sem_list_app.
       simpl. destruct p0. simpl in Hsem. setoid_rewrite sem_list_app in Hsem. simpl in Hsem.
      (*setoid_rewrite elem_cons.*)
      f_solver e.
    - repeat replace (#1) with (2^0)%Z by reflexivity.
      eapply fromList_go_Desc.
      + lia.
      + destruct p0. simpl in Heq.
        solve_Bounded e.
      + right. reflexivity.
      + intros.
        solve_Desc e. simpl. setoid_rewrite sem_list_app. setoid_rewrite sem_list_app.
        simpl. simpl in H1. setoid_rewrite sem_list_app in H1. simpl in H1.
        f_solver e.
Qed.

End WF.
