(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import GHC.Base.
Import GHC.Base.ManualNotations.
Require Import Core.
Require UniqFM.


Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.

Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.Equalities.

Require Coq.FSets.FSetDecide.
Require Coq.FSets.FSetProperties.
Require Coq.FSets.FSetEqProperties.

(* base-thy *)
Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

(* containers theory *)
Require Import IntSetProofs.

(* ghc theory (incl. some that should move above. *)
Require Import Proofs.Base.
Require Import Proofs.Axioms.
Require Import Proofs.ContainerProofs.
Require Import Proofs.GhcTactics.
Require Import Proofs.Unique.
Require Import Proofs.Var.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".


(** ** [VarSet as FSet] *)

(* This part creates an instance of the FSetInterface for VarSets.

   This allows us to experiment with some of the metalib automation
   for reasoning about sets of variable names.

   This file use the FSet instance to define modules of facts about VarSets
   including:

     VarSetFacts
     VarSetProperties
     VarSetDecide     [fsetdec tactic]
     VarSetNotin      [destruct_notin and solve_notin tactics]


   *)

(** Note: This module is actually *more* than what we need for fsetdec.  Maybe
    we want to redesign fsetdec to state only the properties and operations
    that it uses?

    Also the fsetdec reasoning uses "Prop" based statement of facts instead of
    operational "bool" based reasoning. This interface captures the
    relationship between those two statements, but it still can be tricky.
    Regardless, we are using the "weak" signature for this module as it
    doesn't require an ordering on elements.  *)

Module VarSetFSet <: WSfun(Var_as_DT) <: WS.

  Module E := Var_as_DT.

  Definition elt := Var.

  Definition t   := VarSet.

  (* These are specified exactly by the signature. *)
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

   (* available but unused. *)

  Definition fold (A : Type) (f : elt -> A -> A) (ws : VarSet) (x : A) : A.
    destruct ws.
    apply (@UniqFM.nonDetFoldUFM elt A elt); eauto.
  Defined.

  Definition for_all := allVarSet.

  Definition filter  := filterVarSet.

  Definition cardinal := sizeVarSet.

  Definition inter := intersectVarSet.


  (* PROOFS *)

  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.

  Lemma In_1 :
    forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s.
  Proof.
    unfold E.eq, E.eqb, In.
    move => [u].
    move: u => [i].
    move=> x y Eq.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    erewrite member_eq with (k' := (Unique.getWordKey (Unique.getUnique y))). auto.
    rewrite -> eq_unique in Eq.
    rewrite Eq.
    reflexivity.
  Qed.

  Lemma eq_refl : forall s : t, eq s s.
  Proof. destruct s. unfold eq. unfold Equal. intro. reflexivity. Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. destruct s; destruct s';
    unfold eq, Equal in *. intros. rewrite H. intuition. Qed.

  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    destruct s; destruct s'; destruct s''; simpl.
    unfold eq, Equal. intros ???. rewrite H. rewrite H0. reflexivity.
  Qed.

  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true.
  Proof.
    unfold Subset, In, subset.
    move => [[m1]] [[m2]] Hsub.
    unfold subVarSet, isEmptyVarSet, UniqSet.isEmptyUniqSet, UniqFM.isNullUFM.
    unfold minusVarSet, UniqSet.minusUniqSet, UniqFM.minusUFM.
    apply (proj2 (@null_member _ (Data.IntMap.Internal.difference m1 m2)
      (IntMapProofs.All_IntMaps_WF _ (Data.IntMap.Internal.difference m1 m2)))).
    intros k.
    rewrite member_difference.
    destruct (Data.IntMap.Internal.member k m1) eqn:Hm1; [|reflexivity].
    simpl.
    (* member k m1 = true, need member k m2 = true *)
    have [v Hv] : exists v, Data.IntMap.Internal.lookup k m1 = Some v.
    { apply member_lookup_some. exact Hm1. }
    pose proof (StrongValidVarSet_Axiom (UniqSet.Mk_UniqSet (UniqFM.UFM m1))) as Hstrong.
    simpl in Hstrong. specialize (Hstrong k v Hv).
    have Hin : elemVarSet v (UniqSet.Mk_UniqSet (UniqFM.UFM m1)) = true.
    { unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
      rewrite Hstrong. exact Hm1. }
    have Hin' := Hsub v Hin.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM in Hin'.
    rewrite Hstrong in Hin'. rewrite Hin'. reflexivity.
  Qed.

  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof.
    unfold Subset, In, subset.
    move => [[m1]] [[m2]].
    unfold subVarSet, isEmptyVarSet, UniqSet.isEmptyUniqSet, UniqFM.isNullUFM.
    unfold minusVarSet, UniqSet.minusUniqSet, UniqFM.minusUFM.
    move => Hnull a.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    move => Hin.
    have Hk : Data.IntMap.Internal.member (Unique.getWordKey (Unique.getUnique a))
              (Data.IntMap.Internal.difference m1 m2) = false.
    { exact (proj1 (@null_member _ (Data.IntMap.Internal.difference m1 m2)
        (IntMapProofs.All_IntMaps_WF _ (Data.IntMap.Internal.difference m1 m2))) Hnull _). }
    rewrite member_difference in Hk.
    rewrite Hin in Hk. simpl in Hk.
    (* Hk : negb (member ... m2) = false *)
    destruct (Data.IntMap.Internal.member (Unique.getWordKey (Unique.getUnique a)) m2) eqn:E;
      [exact E | discriminate Hk].
  Qed.

  Lemma empty_1 : Empty empty.
  Proof. unfold Empty; intros a H. inversion H. Qed.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    unfold Empty, In, is_empty.
    move => [[m]] Hempty.
    unfold isEmptyVarSet, UniqSet.isEmptyUniqSet, UniqFM.isNullUFM.
    apply (proj2 (@null_member _ m (IntMapProofs.All_IntMaps_WF _ m))).
    intros k.
    destruct (Data.IntMap.Internal.member k m) eqn:Hmem; [|reflexivity].
    exfalso.
    have [v Hv] : exists v, Data.IntMap.Internal.lookup k m = Some v.
    { apply member_lookup_some. exact Hmem. }
    pose proof (StrongValidVarSet_Axiom (UniqSet.Mk_UniqSet (UniqFM.UFM m))) as Hstrong.
    simpl in Hstrong. specialize (Hstrong k v Hv).
    apply (Hempty v).
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    rewrite Hstrong. exact Hmem.
  Qed.

  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof.
    unfold Empty, In, is_empty.
    move => [[m]].
    unfold isEmptyVarSet, UniqSet.isEmptyUniqSet, UniqFM.isNullUFM.
    move => Hnull a.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    have Hk : Data.IntMap.Internal.member (Unique.getWordKey (Unique.getUnique a)) m = false.
    { exact (proj1 (@null_member _ m (IntMapProofs.All_IntMaps_WF _ m)) Hnull _). }
    rewrite Hk. discriminate.
  Qed.

  Lemma add_1 :
    forall (s : t) (x y : elt), E.eq x y -> In y (add x s).
  Proof.
    unfold E.eq, E.eqb, In, add.
    move => [[m]] x y Eq.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold extendVarSet, UniqSet.addOneToUniqSet, UniqFM.addToUFM.
    rewrite (@member_insert _ _ _ _ m (IntMapProofs.All_IntMaps_WF _ m)).
    rewrite -> eq_unique in Eq.
    rewrite Eq. rewrite Eq_refl. reflexivity.
  Qed.

  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s).
  Proof.
    unfold In, add.
    move => [[m]] x y.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold extendVarSet, UniqSet.addOneToUniqSet, UniqFM.addToUFM.
    move => H.
    rewrite (@member_insert _ _ _ _ m (IntMapProofs.All_IntMaps_WF _ m)).
    rewrite H orbT. reflexivity.
  Qed.

  Lemma add_3 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y (add x s) -> In y s.
  Proof.
    unfold E.eq, E.eqb, In, add.
    move => [[m]] x y NEq.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold extendVarSet, UniqSet.addOneToUniqSet, UniqFM.addToUFM.
    rewrite (@member_insert _ _ _ _ m (IntMapProofs.All_IntMaps_WF _ m)).
    have Hneq: (Unique.getWordKey (Unique.getUnique y) ==
                Unique.getWordKey (Unique.getUnique x)) = false.
    { apply /Eq_eq. move => h. apply NEq. apply eq_unique. symmetry. exact h. }
    rewrite Hneq. simpl. auto.
  Qed.

  Lemma remove_1 :
    forall (s : t) (x y : elt), E.eq x y -> ~ In y (remove x s).
  Proof.
    unfold E.eq, E.eqb, In, remove.
    move => [[m]] x y Eq.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold delVarSet, UniqSet.delOneFromUniqSet, UniqFM.delFromUFM.
    rewrite member_delete.
    rewrite -> eq_unique in Eq.
    rewrite Eq. rewrite Eq_refl. simpl. discriminate.
  Qed.

  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y s -> In y (remove x s).
  Proof.
    unfold E.eq, E.eqb, In, remove.
    move => [[m]] x y NEq.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold delVarSet, UniqSet.delOneFromUniqSet, UniqFM.delFromUFM.
    rewrite member_delete.
    move => H.
    have Hneq: (Unique.getWordKey (Unique.getUnique y) ==
                Unique.getWordKey (Unique.getUnique x)) = false.
    { apply /Eq_eq. move => h. apply NEq. apply eq_unique. symmetry. exact h. }
    rewrite Hneq. simpl. exact H.
  Qed.

  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s.
  Proof.
    unfold In, remove.
    move => [[m]] x y.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold delVarSet, UniqSet.delOneFromUniqSet, UniqFM.delFromUFM.
    rewrite member_delete.
    move /andP => [_ H]. exact H.
  Qed.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> E.eq x y.
  Proof.
    unfold E.eq, E.eqb, In, singleton.
    move => x y.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold unitVarSet, UniqSet.unitUniqSet, UniqFM.unitUFM.
    rewrite member_singleton.
    move /Eq_eq => H. apply eq_unique. symmetry. exact H.
  Qed.

  Lemma singleton_2 :
    forall x y : elt, E.eq x y -> In y (singleton x).
  Proof.
    unfold E.eq, E.eqb, In, singleton.
    move => x y.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold unitVarSet, UniqSet.unitUniqSet, UniqFM.unitUFM.
    rewrite member_singleton.
    move => Eq. rewrite -> eq_unique in Eq. rewrite Eq. rewrite Eq_refl.
    reflexivity.
  Qed.

  Lemma union_1 :
    forall (s s' : t) (x : elt), In x (union s s') -> In x s \/ In x s'.
  Proof.
    unfold In, union.
    move => [[m1]] [[m2]] x.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold unionVarSet, UniqSet.unionUniqSets, UniqFM.plusUFM.
    rewrite member_union.
    (* plusUFM swaps: union m2 m1, so member_union gives member k m1 || member k m2 *)
    move /orP => [H | H].
    - left. exact H.
    - right. exact H.
  Qed.

  Lemma union_2 :
    forall (s s' : t) (x : elt), In x s -> In x (union s s').
  Proof.
    unfold In, union.
    move => [[m1]] [[m2]] x.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold unionVarSet, UniqSet.unionUniqSets, UniqFM.plusUFM.
    rewrite member_union.
    move => H. apply /orP. left. exact H.
  Qed.

  Lemma union_3 :
    forall (s s' : t) (x : elt), In x s' -> In x (union s s').
  Proof.
    unfold In, union.
    move => [[m1]] [[m2]] x.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold unionVarSet, UniqSet.unionUniqSets, UniqFM.plusUFM.
    rewrite member_union.
    move => H. apply /orP. right. exact H.
  Qed.

  Lemma inter_1 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s.
  Proof.
    unfold In, inter.
    move => [[m1]] [[m2]] x.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold intersectVarSet, UniqSet.intersectUniqSets, UniqFM.intersectUFM.
    rewrite member_intersection.
    move /andP => [H _]. exact H.
  Qed.

  Lemma inter_2 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s'.
  Proof.
    unfold In, inter.
    move => [[m1]] [[m2]] x.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold intersectVarSet, UniqSet.intersectUniqSets, UniqFM.intersectUFM.
    rewrite member_intersection.
    move /andP => [_ H]. exact H.
  Qed.

  Lemma inter_3 :
    forall (s s' : t) (x : elt), In x s -> In x s' -> In x (inter s s').
  Proof.
    unfold In, inter.
    move => [[m1]] [[m2]] x.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold intersectVarSet, UniqSet.intersectUniqSets, UniqFM.intersectUFM.
    rewrite member_intersection.
    move => H1 H2. apply /andP. split; assumption.
  Qed.

  Lemma diff_1 :
    forall (s s' : t) (x : elt), In x (diff s s') -> In x s.
  Proof.
    unfold In, diff.
    move => [[m1]] [[m2]] x.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold minusVarSet, UniqSet.minusUniqSet, UniqFM.minusUFM.
    rewrite member_difference.
    move /andP => [H _]. exact H.
  Qed.

  Lemma diff_2 :
    forall (s s' : t) (x : elt), In x (diff s s') -> ~ In x s'.
  Proof.
    unfold In, diff.
    move => [[m1]] [[m2]] x.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold minusVarSet, UniqSet.minusUniqSet, UniqFM.minusUFM.
    rewrite member_difference.
    move /andP => [_ H] Hcontra.
    move: H. rewrite Hcontra. done.
  Qed.

  Lemma diff_3 :
    forall (s s' : t) (x : elt), In x s -> ~ In x s' -> In x (diff s s').
  Proof.
    unfold In, diff.
    move => [[m1]] [[m2]] x.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    unfold minusVarSet, UniqSet.minusUniqSet, UniqFM.minusUFM.
    rewrite member_difference.
    move => H1 H2. apply /andP. split.
    - exact H1.
    - apply /negP. exact H2.
  Qed.

  Lemma fold_left_map:
    forall {a b c} f (g : a -> b) (x : c) xs,
    fold_left (fun a e => f a e) (List.map g xs) x
      = fold_left (fun a e => f a (g e)) xs x.
  Proof.
    intros.
    revert x.
    induction xs; intros.
    * reflexivity.
    * simpl. rewrite IHxs. reflexivity.
  Qed.


  Lemma filter_1 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x (filter f s) -> In x s.
  Proof.
    intros s x f _ Hin.
    destruct s as [[m]].
    unfold In, filter, filterVarSet, UniqSet.filterUniqSet, UniqFM.filterUFM in *.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM in *.
    set (key := Unique.getWordKey (Unique.getUnique x)) in *.
    apply member_lookup_some in Hin. destruct Hin as [val Hval].
    (* filter is filterWithKey, so lookup_filterWithKey applies *)
    unfold Data.IntMap.Internal.filter in Hval.
    apply lookup_filterWithKey in Hval.
    apply (proj2 (@member_lookup _ key m (IntMapProofs.All_IntMaps_WF _ m))).
    exists val. exact Hval.
  Qed.

  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x (filter f s) -> f x = true.
  Proof.
    intros s x f Hcompat Hin.
    destruct s as [[m]].
    unfold In, filter, filterVarSet, UniqSet.filterUniqSet, UniqFM.filterUFM in *.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM in *.
    set (key := Unique.getWordKey (Unique.getUnique x)) in *.
    apply member_lookup_some in Hin. destruct Hin as [val Hval].
    apply lookup_filter_Some in Hval. destruct Hval as [Hpval Hlookup].
    (* val is the Var stored at key in the original map.
       ValidVarSet_Axiom: lookupVarSet s x = Some val -> x == val.
       compat_bool: E.eq x val -> f x = f val. *)
    assert (Heq : Var_as_DT.eq x val).
    { unfold Var_as_DT.eq, Var_as_DT.eqb.
      assert (Hlook : lookupVarSet (UniqSet.Mk_UniqSet (UniqFM.UFM m)) x = Some val)
        by exact Hlookup.
      apply ValidVarSet_Axiom in Hlook. exact Hlook. }
    rewrite (Hcompat x val Heq). exact Hpval.
  Qed.

  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).
  Proof.
    intros s x f Hcompat Hin Hfx.
    destruct s as [[m]].
    unfold In, filter, filterVarSet, UniqSet.filterUniqSet, UniqFM.filterUFM in *.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM in *.
    set (key := Unique.getWordKey (Unique.getUnique x)) in *.
    (* Get val from member *)
    apply member_lookup_some in Hin. destruct Hin as [val Hval].
    (* ValidVarSet gives x == val *)
    assert (Heq : Var_as_DT.eq x val).
    { unfold Var_as_DT.eq, Var_as_DT.eqb.
      assert (Hlook : lookupVarSet (UniqSet.Mk_UniqSet (UniqFM.UFM m)) x = Some val)
        by exact Hval.
      apply ValidVarSet_Axiom in Hlook. exact Hlook. }
    (* f val = f x = true *)
    assert (Hfval : f val = true) by (rewrite <- (Hcompat x val Heq); exact Hfx).
    (* Use member_filter from ContainerProofs *)
    exact (member_filter _ f key val m Hval Hfval).
  Qed.

  (* ---- Helper definitions for foldr-based proofs ---- *)

  (* Structural version of IntMap.foldr's inner go function *)
  Fixpoint intmap_foldr_go {a b} (ff : a -> b -> b) (z : b) (m : Data.IntMap.Internal.IntMap a) : b :=
    match m with
    | Data.IntMap.Internal.Nil => z
    | Data.IntMap.Internal.Tip _ v => ff v z
    | Data.IntMap.Internal.Bin _ _ l r => intmap_foldr_go ff (intmap_foldr_go ff z r) l
    end.

  (* Forward: foldr_go (andb . f) z m = true implies every lookup passes f *)
  Lemma intmap_foldr_go_andb_true :
    forall (f : elt -> bool) z (m : Data.IntMap.Internal.IntMap elt),
    intmap_foldr_go (fun v acc => f v && acc) z m = true ->
    (forall k v, Data.IntMap.Internal.lookup k m = Some v -> f v = true) /\ z = true.
  Proof.
    intros f z m. revert z.
    induction m as [p msk l IHl r IHr | k' v' | ]; intros z; simpl; intro H.
    - apply IHl in H. destruct H as [Hl Hz'].
      apply IHr in Hz'. destruct Hz' as [Hr Hz].
      split; [|exact Hz].
      intros k v Hlu.
      destruct (Data.IntSet.Internal.zero k msk); [exact (Hl k v Hlu) | exact (Hr k v Hlu)].
    - apply andb_true_iff in H. destruct H as [Hf Hz]. split; [|exact Hz].
      intros k v Hlu. destruct (GHC.Base.op_zeze__ k k') eqn:Hkk; [|discriminate].
      inversion Hlu; subst. exact Hf.
    - split; [intros k v Hlu; discriminate | exact H].
  Qed.

  (* Factoring: foldr_go (andb . f) z m = (foldr_go (andb . f) true m) && z *)
  Lemma intmap_foldr_go_andb_factor :
    forall (f : elt -> bool) z (m : Data.IntMap.Internal.IntMap elt),
    intmap_foldr_go (fun v acc => f v && acc) z m =
    (intmap_foldr_go (fun v acc => f v && acc) true m) && z.
  Proof.
    intros f z m. revert z.
    induction m as [p msk l IHl r IHr | k' v' | ]; intros z; simpl.
    - rewrite IHl IHr (IHl (intmap_foldr_go _ true r)). rewrite Bool.andb_assoc. reflexivity.
    - rewrite Bool.andb_true_r. reflexivity.
    - symmetry. apply Bool.andb_true_l.
  Qed.

  (* Backward: all structural values pass f => foldr_go returns true *)
  Lemma intmap_foldr_go_andb_all_true :
    forall (f : elt -> bool) (m : Data.IntMap.Internal.IntMap elt),
    (forall k v, tree_elem_kv k v m -> f v = true) ->
    intmap_foldr_go (fun v acc => f v && acc) true m = true.
  Proof.
    intros f m.
    induction m as [p msk l IHl r IHr | k' v' | ]; simpl; intro Hall.
    - rewrite intmap_foldr_go_andb_factor. rewrite IHr.
      + rewrite Bool.andb_true_r. apply IHl.
        intros k v Hkv. exact (Hall k v (or_introl Hkv)).
      + intros k v Hkv. exact (Hall k v (or_intror Hkv)).
    - rewrite (Hall k' v' (conj (@Logic.eq_refl _ k') (@Logic.eq_refl _ v'))). reflexivity.
    - reflexivity.
  Qed.

  (* Orb factoring *)
  Lemma intmap_foldr_go_orb_factor :
    forall (f : elt -> bool) z (m : Data.IntMap.Internal.IntMap elt),
    intmap_foldr_go (fun v acc => f v || acc) z m =
    (intmap_foldr_go (fun v acc => f v || acc) false m) || z.
  Proof.
    intros f z m. revert z.
    induction m as [p msk l IHl r IHr | k' v' | ]; intros z; simpl.
    - rewrite IHl IHr (IHl (intmap_foldr_go _ false r)).
      rewrite Bool.orb_assoc. reflexivity.
    - rewrite Bool.orb_false_r. reflexivity.
    - symmetry. apply Bool.orb_false_l.
  Qed.

  (* Witness extraction from orb fold *)
  Lemma intmap_foldr_go_orb_witness :
    forall (f : elt -> bool) (m : Data.IntMap.Internal.IntMap elt),
    intmap_foldr_go (fun v acc => f v || acc) false m = true ->
    exists k v, tree_elem_kv k v m /\ f v = true.
  Proof.
    intros f m.
    induction m as [p msk l IHl r IHr | k' v' | ]; simpl; intro H.
    - rewrite intmap_foldr_go_orb_factor in H.
      apply orb_true_iff in H. destruct H as [Hl | Hr].
      + destruct (IHl Hl) as [k [v [Hkv Hfv]]].
        exists k, v. split; [left; exact Hkv | exact Hfv].
      + destruct (IHr Hr) as [k [v [Hkv Hfv]]].
        exists k, v. split; [right; exact Hkv | exact Hfv].
    - rewrite Bool.orb_false_r in H.
      exists k', v'. split; [exact (conj (@Logic.eq_refl _ k') (@Logic.eq_refl _ v')) | exact H].
    - discriminate.
  Qed.

  (* Backward for orb: structural witness => fold returns true *)
  Lemma intmap_foldr_go_orb_some_true :
    forall (f : elt -> bool) k (v : elt) (m : Data.IntMap.Internal.IntMap elt),
    tree_elem_kv k v m -> f v = true ->
    intmap_foldr_go (fun v0 acc => f v0 || acc) false m = true.
  Proof.
    intros f k v m.
    induction m as [p msk l IHl r IHr | k' v' | ]; simpl; intros Helem Hf.
    - rewrite intmap_foldr_go_orb_factor. destruct Helem as [Hl | Hr].
      + rewrite (IHl Hl Hf). reflexivity.
      + rewrite (IHr Hr Hf). apply Bool.orb_true_r.
    - destruct Helem as [_ Hv]; subst. rewrite Hf. reflexivity.
    - contradiction.
  Qed.

  (* Connect foldr's inner go to the structural fold. *)
  Local Lemma intmap_foldr_inner_eq_go :
    forall (a b : Type) (f : a -> b -> b) z (m : Data.IntMap.Internal.IntMap a),
    (fix go z' t' := match t' with
     | Data.IntMap.Internal.Nil => z'
     | Data.IntMap.Internal.Tip _ v => f v z'
     | Data.IntMap.Internal.Bin _ _ l r => go (go z' r) l
     end) z m = intmap_foldr_go f z m.
  Proof.
    intros a b f z m; revert z.
    induction m as [p mask l IHl r IHr | k v | ]; intro z;
      cbn [intmap_foldr_go]; [rewrite IHl IHr | | ]; reflexivity.
  Qed.

  (* Factoring makes the top-level dispatch harmless for andb. *)
  Lemma foldr_andb_eq_go :
    forall (f : elt -> bool) (m : Data.IntMap.Internal.IntMap elt),
    Data.IntMap.Internal.foldr (fun v acc => f v && acc) true m =
    intmap_foldr_go (fun v acc => f v && acc) true m.
  Proof.
    intros f m.
    destruct m as [p mask l r | k v | ]; unfold Data.IntMap.Internal.foldr.
    - rewrite !intmap_foldr_inner_eq_go.
      cbn [intmap_foldr_go].
      destruct (mask GHC.Base.< GHC.Num.fromInteger 0); [|reflexivity].
      rewrite (intmap_foldr_go_andb_factor f
                 (intmap_foldr_go (fun v acc => f v && acc) true l) r).
      rewrite (intmap_foldr_go_andb_factor f
                 (intmap_foldr_go (fun v acc => f v && acc) true r) l).
      apply Bool.andb_comm.
    - reflexivity.
    - reflexivity.
  Qed.

  (* The same argument for orb. *)
  Lemma foldr_orb_eq_go :
    forall (f : elt -> bool) (m : Data.IntMap.Internal.IntMap elt),
    Data.IntMap.Internal.foldr (fun v acc => f v || acc) false m =
    intmap_foldr_go (fun v acc => f v || acc) false m.
  Proof.
    intros f m.
    destruct m as [p mask l r | k v | ]; unfold Data.IntMap.Internal.foldr.
    - rewrite !intmap_foldr_inner_eq_go.
      cbn [intmap_foldr_go].
      destruct (mask GHC.Base.< GHC.Num.fromInteger 0); [|reflexivity].
      rewrite (intmap_foldr_go_orb_factor f
                 (intmap_foldr_go (fun v acc => f v || acc) false l) r).
      rewrite (intmap_foldr_go_orb_factor f
                 (intmap_foldr_go (fun v acc => f v || acc) false r) l).
      apply Bool.orb_comm.
    - reflexivity.
    - reflexivity.
  Qed.

  (* ---- End of foldr helpers ---- *)

  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    For_all (fun x : elt => f x = true) s -> for_all f s = true.
  Proof.
    unfold For_all, In, for_all.
    move => [[m]] f Hcompat Hall.
    unfold allVarSet, UniqSet.uniqSetAll, UniqFM.allUFM.
    change (GHC.Base.op_z2218U__ andb f) with (fun v acc => f v && acc).
    rewrite foldr_andb_eq_go.
    apply intmap_foldr_go_andb_all_true.
    intros k v Helem.
    (* v is structurally at key k in m. Use tree_elem_kv_lookup to get lookup. *)
    have HWF := IntMapProofs.All_IntMaps_WF _ m.
    have Hlookup := @tree_elem_kv_lookup _ _ _ m HWF Helem.
    (* By StrongValidVarSet, getWordKey (getUnique v) = k *)
    pose proof (StrongValidVarSet_Axiom (UniqSet.Mk_UniqSet (UniqFM.UFM m))) as Hstrong.
    simpl in Hstrong. specialize (Hstrong k v Hlookup).
    (* So elemVarSet v s = member k m = true *)
    have Hin : elemVarSet v (UniqSet.Mk_UniqSet (UniqFM.UFM m)) = true.
    { unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
      rewrite Hstrong. apply (proj2 (@member_lookup _ _ m HWF)).
      exists v. exact Hlookup. }
    exact (Hall v Hin).
  Qed.

  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    for_all f s = true -> For_all (fun x : elt => f x = true) s.
  Proof.
    unfold For_all, In, for_all.
    move => [[m]] f Hcompat Hforall x Hin.
    unfold allVarSet, UniqSet.uniqSetAll, UniqFM.allUFM in Hforall.
    change (GHC.Base.op_z2218U__ andb f) with (fun v acc => f v && acc) in Hforall.
    rewrite foldr_andb_eq_go in Hforall.
    (* Extract: every lookup value passes f *)
    have [Hlookup _] := intmap_foldr_go_andb_true _ _ _ Hforall.
    (* x is In s, so lookup at its key returns some value *)
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM in Hin.
    apply member_lookup_some in Hin. destruct Hin as [val Hval].
    (* By the foldr spec, f val = true *)
    have Hfval := Hlookup _ _ Hval.
    (* By ValidVarSet, x == val, so by compat_bool, f x = f val *)
    have Heq : Var_as_DT.eq x val.
    { unfold Var_as_DT.eq, Var_as_DT.eqb.
      assert (Hlook : lookupVarSet (UniqSet.Mk_UniqSet (UniqFM.UFM m)) x = Some val)
        by exact Hval.
      apply ValidVarSet_Axiom in Hlook. exact Hlook. }
    rewrite (Hcompat x val Heq). exact Hfval.
  Qed.

  Lemma exists_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    Exists (fun x : elt => f x = true) s -> exists_ f s = true.
  Proof.
    unfold Exists, In, exists_.
    move => [[m]] f Hcompat [x [Hin Hfx]].
    unfold anyVarSet, UniqSet.uniqSetAny, UniqFM.anyUFM.
    change (GHC.Base.op_z2218U__ orb f) with (fun v acc => f v || acc).
    rewrite foldr_orb_eq_go.
    (* x is In s, so lookup returns some value *)
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM in Hin.
    apply member_lookup_some in Hin. destruct Hin as [val Hval].
    (* By ValidVarSet, x == val, so by compat_bool, f val = f x = true *)
    have Heq : Var_as_DT.eq x val.
    { unfold Var_as_DT.eq, Var_as_DT.eqb.
      assert (Hlook : lookupVarSet (UniqSet.Mk_UniqSet (UniqFM.UFM m)) x = Some val)
        by exact Hval.
      apply ValidVarSet_Axiom in Hlook. exact Hlook. }
    have Hfval : f val = true by rewrite <- (Hcompat x val Heq).
    have Helem : tree_elem_kv (Unique.getWordKey (Unique.getUnique x)) val m
      by exact (lookup_tree_elem_kv _ _ _ _ Hval).
    exact (intmap_foldr_go_orb_some_true _ _ _ _ Helem Hfval).
  Qed.

  Lemma exists_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    exists_ f s = true -> Exists (fun x : elt => f x = true) s.
  Proof.
    unfold Exists, In, exists_.
    move => [[m]] f Hcompat Hexists.
    unfold anyVarSet, UniqSet.uniqSetAny, UniqFM.anyUFM in Hexists.
    change (GHC.Base.op_z2218U__ orb f) with (fun v acc => f v || acc) in Hexists.
    rewrite foldr_orb_eq_go in Hexists.
    (* Extract witness from the fold *)
    destruct (intmap_foldr_go_orb_witness _ _ Hexists) as [k [v [Helem Hfv]]].
    (* v is structurally in the tree; use tree_elem_kv_lookup to get lookup *)
    have HWF := IntMapProofs.All_IntMaps_WF _ m.
    have Hlookup := @tree_elem_kv_lookup _ _ _ m HWF Helem.
    (* By StrongValidVarSet, getWordKey (getUnique v) = k *)
    pose proof (StrongValidVarSet_Axiom (UniqSet.Mk_UniqSet (UniqFM.UFM m))) as Hstrong.
    simpl in Hstrong. specialize (Hstrong k v Hlookup).
    (* So elemVarSet v s = member k m = true *)
    exists v. split.
    - unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
      rewrite Hstrong. apply (proj2 (@member_lookup _ _ m HWF)).
      exists v. exact Hlookup.
    - exact Hfv.
  Qed.

  (* Not needed after this line ---------------------- *)

  (* Everything else comes from our particular implementation *)

  Definition lt (s s' : Var) := GHC.Base.compare s s' = Lt.

  (* Equality must be decidable, but doesn't necessarily need to be Coq
     equality. For VarSets, in fact, that is not the case.

     However, GHC does not include an equality instance for VarSets,
     so we don't actually need to define this.
   *)

  Definition equal  : t -> t -> bool :=
    fun x y : t =>
      match x with
      | UniqSet.Mk_UniqSet u =>
        match y with
        | UniqSet.Mk_UniqSet u0 =>
          match u with
          | UniqFM.UFM i =>
            match u0 with
            | UniqFM.UFM i0 => _GHC.Base.==_ i i0
            end
          end
        end
      end.

  (* These operations are part of the FSet interface but are not
     supported by GHC VarSets. *)

  Definition min_elt : t -> option elt := HsToRocq.Err.default.
  Definition max_elt : t -> option elt := HsToRocq.Err.default.


  Definition partition : (elt -> bool) -> t -> t * t := HsToRocq.Err.default.

  Definition elements : t -> list elt := HsToRocq.Err.default.

  Definition choose : t -> option elt := HsToRocq.Err.default.



  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true.
  Proof.
    intros [[m1]] [[m2]] HEqual.
    unfold equal.
    have Hmem : forall v, elemVarSet v (UniqSet.Mk_UniqSet (UniqFM.UFM m1)) =
                          elemVarSet v (UniqSet.Mk_UniqSet (UniqFM.UFM m2)).
    { intro v. specialize (HEqual v). unfold In in HEqual.
      destruct (elemVarSet v (UniqSet.Mk_UniqSet (UniqFM.UFM m1)));
      destruct (elemVarSet v (UniqSet.Mk_UniqSet (UniqFM.UFM m2)));
      try reflexivity; exfalso;
      [exact (diff_false_true (proj1 HEqual (@Logic.eq_refl _ true)))
      |exact (diff_false_true (proj2 HEqual (@Logic.eq_refl _ true)))]. }
    have Hresult := @VarSet_extensional_equal
                      (UniqSet.Mk_UniqSet (UniqFM.UFM m1))
                      (UniqSet.Mk_UniqSet (UniqFM.UFM m2))
                      (IntMapProofs.All_IntMaps_WF _ m1)
                      (IntMapProofs.All_IntMaps_WF _ m2)
                      (@ValidVarSet_Axiom _) (@ValidVarSet_Axiom _) Hmem.
    simpl VarSet_IntMap in Hresult. exact Hresult.
  Qed.


  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof.
    intros s s' Heq a.
    destruct s as [[i]], s' as [[i0]].
    unfold equal in Heq. simpl in Heq.
    unfold In, elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    rewrite (Eq_membership Var _ EqLaws_Var _ _ Heq). tauto.
  Qed.

  Definition eq_dec : forall s s' : t,  {eq s s'} + {~ eq s s'}.
  Proof.
    intros s s'.
    destruct (equal s s') eqn:Heq.
    - left. exact (equal_2 s s' Heq).
    - right. intro H. apply equal_1 in H. rewrite H in Heq. discriminate.
  Defined.

  (* BLOCKER (fold_1): `fold` is defined as nonDetFoldUFM (a real fold over
     the IntMap), but `elements` is HsToRocq.Err.default = fun _ => nil.
     So the RHS reduces to fold_left _ nil i = i, but the LHS is a real
     fold over the map contents. Unprovable for nonempty sets.
     FIX: implement `elements` as a real function (e.g., via nonDetFoldUFM
     cons nil), then prove the connection to fold. *)
  Lemma fold_1 :
    forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
    fold A f s i =
    fold_left (fun (a : A) (e : elt) => f e a) (elements s) i.
  Proof.
    intros.
    simpl.
  Admitted.

  (* BLOCKER (cardinal_1): `cardinal` is sizeVarSet (returns actual size),
     but `elements` is HsToRocq.Err.default = fun _ => nil, so length = 0.
     Unprovable for nonempty sets. FIX: implement `elements` properly. *)
  Lemma cardinal_1 : forall s : t, cardinal s = length (elements s).
  Proof.
    intros.
  Admitted.

  (* BLOCKER (partition_1): `partition` is HsToRocq.Err.default (returns a
     pair of empty sets), but `filter` is the real filterVarSet. The
     equality fails for any set with elements passing f.
     FIX: implement `partition` using filterVarSet for both halves. *)
  Lemma partition_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof.
    intros.
    destruct s.
    unfold Equal, partition; simpl.
  Admitted.

  (* BLOCKER (partition_2): Same as partition_1 — dummy partition vs real
     filter. FIX: implement `partition` properly. *)
  Lemma partition_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s).
  Proof.
    intros.
    destruct s.
    unfold Equal, partition; simpl.
  Admitted.

  (* BLOCKER (elements_1): `elements` is HsToRocq.Err.default = fun _ => nil.
     The goal becomes In x s -> InA E.eq x nil, which is impossible for
     nonempty sets. FIX: implement `elements` properly (e.g., via
     nonDetFoldUFM cons nil) and prove membership correspondence. *)
  Lemma elements_1 :
    forall (s : t) (x : elt), In x s -> InA E.eq x (elements s).
  Proof.
    intros.
  Admitted.

  (* PROVED: elements is HsToRocq.Err.default = fun _ => nil, so
     InA E.eq x nil is always False — the premise is vacuously false. *)
  Lemma elements_2 :
    forall (s : t) (x : elt), InA E.eq x (elements s) -> In x s.
  Proof.
    intros s x H.
    unfold elements in H. simpl in H. inversion H.
  Qed.

  (* PROVED: choose is HsToRocq.Err.default = fun _ => None, so the
     premise choose s = Some x is always False — vacuously true. *)
  Lemma choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s.
  Proof.
    intros s x H.
    unfold choose in H. simpl in H. discriminate.
  Qed.

  (* BLOCKER (choose_2): choose is HsToRocq.Err.default = fun _ => None,
     so the premise is always true, but Empty s is false for nonempty sets.
     Would require all sets to be empty. Unprovable.
     FIX: implement `choose` properly (e.g., head of elements). *)
  Lemma choose_2 : forall s : t, choose s = None -> Empty s.
  Proof.
  Admitted.

  (* PROVED: choose always returns None, so both premises
     choose s1 = Some x1 and choose s2 = Some x2 are False. *)
  Lemma choose_3 (s1 s2 : t) (x1 x2 : elt) :
    choose s1 = Some x1 ->
    choose s2 = Some x2 ->
    Equal s1 s2         ->
    E.eq  x1 x2.
  Proof.
    intros H1 H2 _.
    unfold choose in H1. simpl in H1. discriminate.
  Qed.

  (* PROVED: elements is HsToRocq.Err.default = fun _ => nil, so
     NoDupA E.eq nil holds trivially. *)
  Lemma elements_3w (s : t) : NoDupA E.eq (elements s).
  Proof.
    unfold elements. simpl. constructor.
  Qed.


End VarSetFSet.
Export VarSetFSet.

(* *********************************************************************** *)

(** These two modules provide additional reasoning principles, proved in terms
    of the basic signature. *)

(** This functor derives additional facts from the interface. These facts are
    mainly the specifications of FSetInterface.S written using different styles:
    equivalence and boolean equalities.

    Notably, see tactic [set_iff].
*)

Module VarSetFacts        := FSetFacts.WFacts_fun Var_as_DT VarSetFSet.
Export VarSetFacts.

(** This functor gives us properties about the boolean function specification
    of sets.

    It adds some of these lemmas to a hint database called 'sets'.

*)

Module VarSetEqProperties := FSetEqProperties.WEqProperties_fun Var_as_DT VarSetFSet.
Export VarSetEqProperties.

(** This functor gives us properties about the "prop" specification of
    sets. *)

Module VarSetProperties   := FSetProperties.WProperties_fun Var_as_DT VarSetFSet.
Export VarSetProperties.

(** The [VarSetDecide] module provides the [fsetdec] tactic for
    solving facts about finite sets of vars. *)

Module VarSetDecide      := FSets.FSetDecide.WDecide_fun Var_as_DT VarSetFSet.
Export VarSetDecide.


(* *********************************************************************** *)
(* The next part is taken from Metalib/FSetWeakNotin.v

   SCW note: I didn't want to draw in a dependency on Metalib before determining
   whether the tactics are useful in this development.

   Furthermore, metalib assumes that Atom equality is =. But we need more
   flexibility for GHC. I had to edit some of the lemmas and proofs below
   because of that.
*)
(* *********************************************************************** *)
(** * Implementation *)


Module Notin.

Module E := Var_as_DT.


(* *********************************************************************** *)
(** * Facts about set non-membership *)

Section Lemmas.

Variables x y  : elt.
Variable  s s' : VarSet.

Lemma notin_empty_1 :
  ~ In x empty.
Proof. fsetdec. Qed.

Lemma notin_add_1 :
  ~ In y (add x s) ->
  ~ E.eq x y.
Proof. fsetdec. Qed.

Lemma notin_add_1' :
  ~ In y (add x s) ->
  ~ (E.eq x y).
Proof. fsetdec. Qed.

Lemma notin_add_2 :
  ~ In y (add x s) ->
  ~ In y s.
Proof. fsetdec. Qed.

Lemma notin_add_3 :
  ~ E.eq x y ->
  ~ In y s ->
  ~ In y (add x s).
Proof.
  set_iff. tauto. Qed.

Lemma notin_singleton_1 :
  ~ In y (singleton x) ->
  ~ E.eq x y.
Proof. fsetdec. Qed.

Lemma notin_singleton_1' :
  ~ In y (singleton x) ->
  ~ (E.eq x y).
Proof. fsetdec. Qed.

Lemma notin_singleton_2 :
  ~ E.eq x y ->
  ~ In y (singleton x).
Proof. set_iff. auto. Qed.

Lemma notin_remove_1 :
  ~ In y (remove x s) ->
  E.eq x y \/ ~ In y s.
Proof. fsetdec. Qed.

Lemma notin_remove_2 :
  ~ In y s ->
  ~ In y (remove x s).
Proof. fsetdec. Qed.

Lemma notin_remove_3 :
  E.eq x y ->
  ~ In y (remove x s).
Proof.
  set_iff. tauto.
 Qed.

Lemma notin_remove_3' :
  x = y ->
  ~ In y (remove x s).
Proof. fsetdec. Qed.

Lemma notin_union_1 :
  ~ In x (union s s') ->
  ~ In x s.
Proof. fsetdec. Qed.

Lemma notin_union_2 :
  ~ In x (union s s') ->
  ~ In x s'.
Proof. fsetdec. Qed.

Lemma notin_union_3 :
  ~ In x s ->
  ~ In x s' ->
  ~ In x (union s s').
Proof. fsetdec. Qed.

Lemma notin_inter_1 :
  ~ In x (inter s s') ->
  ~ In x s \/ ~ In x s'.
Proof. fsetdec. Qed.

Lemma notin_inter_2 :
  ~ In x s ->
  ~ In x (inter s s').
Proof. fsetdec. Qed.

Lemma notin_inter_3 :
  ~ In x s' ->
  ~ In x (inter s s').
Proof. fsetdec. Qed.

Lemma notin_diff_1 :
  ~ In x (diff s s') ->
  ~ In x s \/ In x s'.
Proof. fsetdec. Qed.

Lemma notin_diff_2 :
  ~ In x s ->
  ~ In x (diff s s').
Proof. fsetdec. Qed.

Lemma notin_diff_3 :
  In x s' ->
  ~ In x (diff s s').
Proof. fsetdec. Qed.

End Lemmas.


(* *********************************************************************** *)
(** * Hints *)

#[export] Hint Resolve
  @notin_empty_1 @notin_add_3 @notin_singleton_2 @notin_remove_2
  @notin_remove_3 @notin_remove_3' @notin_union_3 @notin_inter_2
  @notin_inter_3 @notin_diff_2 @notin_diff_3 : core.


(* *********************************************************************** *)
(** * Tactics for non-membership *)

(** [destruct_notin] decomposes all hypotheses of the form [~ In x s]. *)

Ltac destruct_notin :=
  match goal with
    | H : In ?x ?s -> False |- _ =>
      change (~ In x s) in H;
      destruct_notin
    | |- In ?x ?s -> False =>
      change (~ In x s);
      destruct_notin
    | H : ~ In _ empty |- _ =>
      clear H;
      destruct_notin
    | H : ~ In ?y (add ?x ?s) |- _ =>
      let J1 := fresh "NotInTac" in
      let J2 := fresh "NotInTac" in
      pose proof H as J1;
      pose proof H as J2;
      apply notin_add_1 in H;
      apply notin_add_1' in J1;
      apply notin_add_2 in J2;
      destruct_notin
    | H : ~ In ?y (singleton ?x) |- _ =>
      let J := fresh "NotInTac" in
      pose proof H as J;
      apply notin_singleton_1 in H;
      apply notin_singleton_1' in J;
      destruct_notin
    | H : ~ In ?y (remove ?x ?s) |- _ =>
      let J := fresh "NotInTac" in
      apply notin_remove_1 in H;
      destruct H as [J | J];
      destruct_notin
    | H : ~ In ?x (union ?s ?s') |- _ =>
      let J := fresh "NotInTac" in
      pose proof H as J;
      apply notin_union_1 in H;
      apply notin_union_2 in J;
      destruct_notin
    | H : ~ In ?x (inter ?s ?s') |- _ =>
      let J := fresh "NotInTac" in
      apply notin_inter_1 in H;
      destruct H as [J | J];
      destruct_notin
    | H : ~ In ?x (diff ?s ?s') |- _ =>
      let J := fresh "NotInTac" in
      apply notin_diff_1 in H;
      destruct H as [J | J];
      destruct_notin
    | _ =>
      idtac
  end.

(** [solve_notin] decomposes hypotheses of the form [~ In x s] and
    then tries some simple heuristics for solving the resulting
    goals. *)

Ltac solve_notin :=
  intros;
  destruct_notin;
  repeat first [ apply notin_union_3
               | apply notin_add_3
               | apply notin_singleton_2
               | apply notin_empty_1
               ];
  auto;
  try tauto;
  fail "Not solvable by [solve_notin]; try [destruct_notin]".

End Notin.

(* --------------------------------------------------------- *)

(* Do we actually need this ??? It is never used in the code.  Why not the
   more extensional definition of equality between VarSets? *)

(*
Instance Eq_VarSet : Eq_ VarSet :=
  fun _ k => k {|
              op_zeze____ := VarSetFSet.eq_dec;
              op_zsze____ := fun x y => negb (VarSetFSet.eq_dec x y);
            |}.

Instance EqLaws_VarSet : EqLaws VarSet.
Proof.
  constructor.
  - red. intros. cbn. destruct (VarSetFSet.eq_dec x x); try reflexivity.
    exfalso. apply n. reflexivity.
  - red. cbn. intros.
    destruct (VarSetFSet.eq_dec x y);
      destruct (VarSetFSet.eq_dec y x); try reflexivity.
    + exfalso. apply VarSetFSet.eq_sym in e. contradiction.
    + exfalso. apply VarSetFSet.eq_sym in e. contradiction.
  - red. cbn. intros.
    destruct (VarSetFSet.eq_dec x y); try discriminate.
    destruct (VarSetFSet.eq_dec y z); try discriminate.
    destruct (VarSetFSet.eq_dec x z); try reflexivity.
    clear H. clear H0. apply (VarSetFSet.eq_trans _ _ _ e) in e0.
    contradiction.
  - intros. cbn. destruct (VarSetFSet.eq_dec x y); reflexivity.
Qed.
*)


(* -------------------------------------------------------- *)

(* Bridge definitions *)

Lemma InE : forall (s : t) (x : elt), elemVarSet x s <-> In x s.
Proof. intros. unfold is_true. rewrite <- mem_iff. reflexivity. Qed.


Lemma SubsetE : forall (s s' : t), subVarSet s s' <->  s [<=] s'.
Proof. intros. unfold is_true. rewrite <- subset_iff. reflexivity. Qed.

Lemma EmptyE: forall s, isEmptyVarSet s <-> Empty s.
Proof. intros. unfold is_true. split.
       apply is_empty_2. apply is_empty_1. Qed.

(* Note: ForallE and ExistsE require a condition on the predicate *)

(* These lemmas relate the GHC VarSet operations to more general
   operations on finite sets. *)

Lemma emptyVarSet_empty : emptyVarSet = empty.
  reflexivity. Qed.

(* need to swap argument order (should we use flip instead ??) *)
Lemma delVarSet_remove : forall x s, delVarSet s x = remove x s.
  reflexivity. Qed.

Lemma extendVarSet_add : forall x s, extendVarSet s x = add x s.
  reflexivity. Qed.

Lemma unitVarSet_singleton : unitVarSet = singleton.
  reflexivity. Qed.

Lemma unionVarSet_union : unionVarSet = union.
  reflexivity. Qed.

Lemma minusVarSet_diff : minusVarSet = diff.
  reflexivity. Qed.

Lemma filterVarSet_filter : filterVarSet = filter.
  reflexivity. Qed.

(* This tactic rewrites the boolean functions into the
   set properties to make them suitable for fsetdec. *)

Ltac set_b_iff :=
  repeat
   progress

    rewrite <- not_mem_iff in *
  || rewrite <- mem_iff in *
  || rewrite <- subset_iff in *
  || rewrite <- is_empty_iff in *

  || rewrite -> InE in *
  || rewrite -> SubsetE in *
  || rewrite -> EmptyE in *

  || rewrite -> emptyVarSet_empty in *
  || rewrite -> delVarSet_remove in *
  || rewrite -> extendVarSet_add in *
  || rewrite -> unionVarSet_union in *
  || rewrite -> minusVarSet_diff in *
  || rewrite -> filterVarSet_filter in *
  || rewrite -> unitVarSet_singleton in *.

(** ** VarSet operations from FSetInterface are Proper *)

(* Restating these instances helps type class resolution during rewriting.  *)


Instance delVarSet_m :
  Proper (Equal ==> (fun x y => x == y) ==> Equal) delVarSet.
Proof.
  move => x1 y1 Eq1 x2 y2 Eq2.
  set_b_iff.
  eapply remove_m; eauto.
Qed.

Instance extendVarSet_m :
  Proper (Equal ==> (fun x y => x == y) ==> Equal) extendVarSet.
Proof.
  move => x1 y1 Eq1 x2 y2 Eq2.
  set_b_iff.
  eapply add_m; eauto.
Qed.

Instance unionVarSet_m :
  Proper (Equal ==> Equal ==> Equal) unionVarSet.
Proof.
  move => x1 y1 Eq1 x2 y2 Eq2.
  set_b_iff.
  eapply union_m; eauto.
Qed.

Instance minusVarSet_m :
  Proper (Equal ==> Equal ==> Equal) minusVarSet.
Proof.
  move => x1 y1 Eq1 x2 y2 Eq2.
  set_b_iff.
  eapply diff_m; eauto.
Qed.
