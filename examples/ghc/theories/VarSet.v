(* Premise-aware VarSet facts.  The carrier and the membership/equality
   predicates remain raw; every structural operation law carries its WF
   hypotheses explicitly. *)
Set Warnings "-notation-overridden".
From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Coq.Lists.List Coq.Classes.Morphisms Coq.Classes.RelationClasses.
Require Import Coq.Lists.SetoidList.
Require Import GHC.Base Core.
Require Import Proofs.GHC.Base Proofs.GHC.List Proofs.Data.Foldable.
Require Import Proofs.Axioms Proofs.Unique Proofs.Var.
Require Export Proofs.VarSetFSet.
Import GHC.Base.ManualNotations ListNotations.

Lemma fold_is_true b : b = true <-> b. Proof. reflexivity. Qed.
Lemma false_is_not_true b : b = false <-> b <> true.
Proof. destruct b; intuition discriminate. Qed.
Lemma eqE (a b : bool) : a = b <-> (a <-> b).
Proof. destruct a, b; unfold is_true; intuition discriminate. Qed.
Lemma andE a b : a && b <-> a /\ b.
Proof. apply Bool.andb_true_iff. Qed.
Lemma orE a b : a || b <-> a \/ b.
Proof. apply Bool.orb_true_iff. Qed.
Lemma notE a : ~~ a <-> ~ a.
Proof. destruct a; unfold is_true; intuition discriminate. Qed.

Lemma elemVarSet_eq v1 v2 vs : v1 == v2 ->
  elemVarSet v1 vs = elemVarSet v2 vs.
Proof.
  intro E. rewrite eq_unique in E. destruct vs as [[m]].
  unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM. now rewrite E.
Qed.
Lemma lookupVarSet_eq v1 v2 vs : v1 == v2 ->
  lookupVarSet vs v1 = lookupVarSet vs v2.
Proof. intro E. rewrite eq_unique in E. rewrite -> !lookupVarSet_IntMap, E. reflexivity. Qed.
Lemma delVarSet_eq x y vs : x == y -> delVarSet vs x = delVarSet vs y.
Proof.
  intro E. rewrite eq_unique in E. destruct vs as [[m]].
  unfold delVarSet, UniqSet.delOneFromUniqSet, UniqFM.delFromUFM. now rewrite E.
Qed.
Lemma extendVarSet_eq x y vs : WF vs -> x == y ->
  extendVarSet vs x [=] extendVarSet vs y.
Proof. intros W E. apply extendVarSet_m; auto; reflexivity. Qed.

Lemma lookupVarSet_In vs v : WF vs ->
  ((exists v', lookupVarSet vs v = Some v') <-> In v vs).
Proof.
  intro W. unfold In. split.
  - intros [w L]. eapply lookupVarSet_member; eauto.
  - apply elemVarSet_lookup_some; exact W.
Qed.
Lemma lookupVarSet_elemVarSet v1 v2 vs : WF vs ->
  lookupVarSet vs v1 = Some v2 -> elemVarSet v1 vs.
Proof. apply lookupVarSet_member. Qed.
Lemma lookupVarSet_None_elemVarSet v vs : WF vs ->
  (lookupVarSet vs v = None <-> elemVarSet v vs = false).
Proof.
  intro W. rewrite (elemVarSet_lookup vs v W).
  destruct (lookupVarSet vs v); intuition discriminate.
Qed.
Lemma lookupVarSet_Equal s t : WF s -> WF t ->
  (forall v, lookupVarSet s v = lookupVarSet t v) -> s [=] t.
Proof.
  intros W T E x. unfold In.
  rewrite -> (elemVarSet_lookup s x W), (elemVarSet_lookup t x T), E. reflexivity.
Qed.
(* This direction really is raw-true: member follows the lookup path. *)
Lemma elemVarSet_lookupVarSet v vs :
  elemVarSet v vs -> exists w, lookupVarSet vs v = Some w.
Proof.
  destruct vs as [[m]]. unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
  rewrite lookupVarSet_IntMap. simpl VarSet_IntMap.
  apply Proofs.ContainerProofs.member_lookup_some.
Qed.

(* Not a Proper instance on unrestricted Equal. *)
Lemma lookupVarSet_m s t x y : WF s -> WF t ->
  ValidVarSet s -> ValidVarSet t -> s [=] t -> x == y ->
  lookupVarSet s x == lookupVarSet t y.
Proof.
  intros W T V U E H. rewrite <- (lookupVarSet_eq x y t H).
  destruct (lookupVarSet s x) as [v|] eqn:L;
    destruct (lookupVarSet t x) as [w|] eqn:K.
  - change (v == w). eapply Eq_trans; [|exact (U x w K)].
    rewrite Eq_sym. exact (V x v L).
  - exfalso. apply (lookupVarSet_member s x v W) in L.
    apply (proj1 (E x)) in L. unfold In in L.
    rewrite -> (elemVarSet_lookup t x T), K in L. discriminate.
  - exfalso. apply (lookupVarSet_member t x w T) in K.
    apply (proj2 (E x)) in K. unfold In in K.
    rewrite -> (elemVarSet_lookup s x W), L in K. discriminate.
  - change (true = true). reflexivity.
Qed.

Lemma lookupVarSet_extendVarSet_self v vs : WF vs ->
  lookupVarSet (extendVarSet vs v) v = Some v.
Proof. apply lookupVarSet_extend_same. Qed.
Lemma lookupVarSet_extendVarSet_eq v1 v2 vs : WF vs -> v1 == v2 ->
  lookupVarSet (extendVarSet vs v1) v2 = Some v1.
Proof.
  intros W E. rewrite <- (lookupVarSet_eq v1 v2 _ E).
  apply lookupVarSet_extend_same; exact W.
Qed.
Lemma lookupVarSet_extendVarSet_neq v1 v2 vs : WF vs -> ~ (v1 == v2) ->
  lookupVarSet (extendVarSet vs v1) v2 = lookupVarSet vs v2.
Proof.
  intros W E. apply lookupVarSet_extend_neq; [exact W|].
  rewrite Eq_sym. apply Bool.not_true_is_false. exact E.
Qed.

Lemma mkVarSet_extendVarSetList xs : mkVarSet xs = extendVarSetList emptyVarSet xs.
Proof. reflexivity. Qed.
Lemma extendVarSetList_singleton vs v : extendVarSetList vs [v] = extendVarSet vs v.
Proof. reflexivity. Qed.
Lemma extendVarSetList_append s vs1 vs2 :
  extendVarSetList s (vs1 ++ vs2) = extendVarSetList (extendVarSetList s vs1) vs2.
Proof.
  revert s; induction vs1 as [|v vs IH]; intro s; simpl List.app; [reflexivity|].
  rewrite !extendVarSetList_cons. apply IH.
Qed.
Lemma delVarSetList_single e a : delVarSetList e [a] = delVarSet e a.
Proof. rewrite -> delVarSetList_cons, delVarSetList_nil. reflexivity. Qed.
Lemma delVarSetList_app s vs1 vs2 :
  delVarSetList s (vs1 ++ vs2) = delVarSetList (delVarSetList s vs1) vs2.
Proof.
  revert s; induction vs1 as [|v vs IH]; intro s; simpl List.app.
  - rewrite !delVarSetList_nil. reflexivity.
  - rewrite !delVarSetList_cons. apply IH.
Qed.

Lemma elemVarSet_emptyVarSet v : elemVarSet v emptyVarSet = false.
Proof. reflexivity. Qed.
Lemma elemVarSet_extendVarSet v vs v' : WF vs ->
  elemVarSet v (extendVarSet vs v') = (v' == v) || elemVarSet v vs.
Proof. intro W. rewrite -> (elemVarSet_extend_eq vs v' v W), Eq_sym. reflexivity. Qed.
Lemma elemVarSet_delVarSet v1 vs v2 : WF vs ->
  elemVarSet v1 (delVarSet vs v2) = negb (v2 == v1) && elemVarSet v1 vs.
Proof. intro W. rewrite -> (elemVarSet_del vs v2 v1 W). rewrite <- Var_eq_key. rewrite Eq_sym. reflexivity. Qed.
Lemma elemVarSet_extendVarSetList v vs vs' : WF vs ->
  elemVarSet v (extendVarSetList vs vs') = Foldable.elem v vs' || elemVarSet v vs.
Proof.
  revert vs. induction vs' as [|x xs IH]; intros vs W.
  - rewrite -> extendVarSetList_nil, elem_nil. reflexivity.
  - rewrite -> extendVarSetList_cons, IH by (apply extendVarSet_WF; exact W).
    rewrite -> elemVarSet_extendVarSet by exact W. rewrite elem_cons.
    rewrite Eq_sym. destruct (v == x), (Foldable.elem v xs), (elemVarSet v vs); reflexivity.
Qed.
Lemma extendVarSetList_iff l x vs : WF vs ->
  (In x (extendVarSetList vs l) <-> In x vs \/ Foldable.elem x l).
Proof.
  intro W. unfold In. rewrite -> elemVarSet_extendVarSetList by exact W.
  rewrite Bool.orb_true_iff. tauto.
Qed.
Lemma delVarSetList_iff l x vs : WF vs ->
  (In x (delVarSetList vs l) <-> In x vs /\ ~ Foldable.elem x l).
Proof.
  revert vs; induction l as [|v vs IH]; intros s W.
  - rewrite -> delVarSetList_nil, elem_nil. unfold is_true; intuition discriminate.
  - rewrite -> delVarSetList_cons, IH by (apply delVarSet_WF; exact W).
    rewrite -> delVarSet_remove, remove_iff by exact W.
    rewrite elem_cons. unfold is_true. rewrite Bool.orb_true_iff. unfold E.eq, E.eqb, E.t.
    rewrite Eq_sym. tauto.
Qed.

Lemma extendVarSet_elemVarSet_true s v : WF s -> elemVarSet v s ->
  extendVarSet s v [=] s.
Proof. apply add_equal. Qed.
Lemma delVarSet_elemVarSet_false v s : WF s -> elemVarSet v s = false ->
  delVarSet s v [=] s.
Proof. intros W H. apply remove_equal; [exact W|]. unfold In; rewrite H; discriminate. Qed.
Lemma extendVarSet_commute x y s : WF s ->
  extendVarSet (extendVarSet s y) x [=] extendVarSet (extendVarSet s x) y.
Proof.
  intros W a. rewrite -> !extendVarSet_add, !add_iff by solve_varset_inv. tauto.
Qed.
Lemma delVarSet_commute x y s : WF s ->
  delVarSet (delVarSet s x) y [=] delVarSet (delVarSet s y) x.
Proof. intros W; fsetdec. Qed.
Lemma delVarSet_emptyVarSet x : delVarSet emptyVarSet x = emptyVarSet.
Proof. reflexivity. Qed.
Lemma delVarSet_extendVarSet s v : WF s -> elemVarSet v s = false ->
  delVarSet (extendVarSet s v) v [=] s.
Proof.
  intros W H x. rewrite -> delVarSet_remove, remove_iff by solve_varset_inv.
  rewrite -> extendVarSet_add, add_iff by exact W.
  split; [tauto|]. intro K; split; [auto|]. intro E.
  assert (L : In v s) by (eapply In_1; [symmetry; exact E|exact K]).
  unfold In in L; rewrite H in L; discriminate.
Qed.
Lemma elemVarSet_delVarSet_eq x y s : WF s -> x == y ->
  elemVarSet x (delVarSet s y) = false.
Proof. intros W E. rewrite -> elemVarSet_delVarSet by exact W. rewrite -> Eq_sym, E. reflexivity. Qed.
Lemma lookupVarSet_delVarSet_neq v1 v2 s : WF s -> ~ (v1 == v2) ->
  lookupVarSet (delVarSet s v1) v2 = lookupVarSet s v2.
Proof.
  intros W E. rewrite -> (lookupVarSet_del s v1 v2 W). rewrite <- Var_eq_key. rewrite Eq_sym.
  destruct (v1 == v2) eqn:K; [exfalso; apply E; reflexivity|reflexivity].
Qed.

Lemma extendVarSetList_m s t xs ys : WF s -> WF t ->
  s [=] t -> eqlistA (fun x y => x == y) xs ys ->
  extendVarSetList s xs [=] extendVarSetList t ys.
Proof.
  intros W T E L. revert s t W T E. induction L; intros s t W T E.
  - exact E.
  - rewrite !extendVarSetList_cons. apply IHL;
      try (apply extendVarSet_WF; assumption).
    apply extendVarSet_m; assumption.
Qed.
Lemma delVarSetList_m s t xs ys : WF s -> WF t ->
  s [=] t -> eqlistA (fun x y => x == y) xs ys ->
  delVarSetList s xs [=] delVarSetList t ys.
Proof.
  intros W T E L. revert s t W T E. induction L; intros s t W T E.
  - rewrite !delVarSetList_nil. exact E.
  - rewrite !delVarSetList_cons. apply IHL;
      try (apply delVarSet_WF; assumption).
    apply delVarSet_m; assumption.
Qed.
Lemma extendVarSetList_extendVarSet_iff l x s : WF s ->
  extendVarSetList (extendVarSet s x) l [=] extendVarSet (extendVarSetList s l) x.
Proof.
  intros W y. rewrite -> !extendVarSet_add, add_iff by solve_varset_inv.
  rewrite -> !extendVarSetList_iff by solve_varset_inv.
  rewrite -> add_iff by exact W. tauto.
Qed.
Lemma elemVarSet_extend_add v s vs a : WF s ->
  elemVarSet v (extendVarSetList s vs) -> elemVarSet v (extendVarSetList (add a s) vs).
Proof.
  intros W. rewrite -> !InE, !extendVarSetList_iff by solve_varset_inv.
  rewrite -> add_iff by exact W. tauto.
Qed.
Lemma elemVarSet_extendVarSetList_r v s vs : WF s ->
  elemVarSet v (mkVarSet vs) -> elemVarSet v (extendVarSetList s vs).
Proof.
  intros W. rewrite -> mkVarSet_extendVarSetList, !InE,
    !extendVarSetList_iff by solve_varset_inv.
  rewrite -> emptyVarSet_empty, empty_iff. tauto.
Qed.
Lemma elemVarSet_mkVarSet_cons v v' vs :
  elemVarSet v (mkVarSet (v' :: vs)) = false <->
  (v' == v) = false /\ elemVarSet v (mkVarSet vs) = false.
Proof.
  rewrite -> (mkVarSet_extendVarSetList (v' :: vs)), (mkVarSet_extendVarSetList vs), extendVarSetList_cons.
  rewrite -> !elemVarSet_extendVarSetList by solve_varset_inv.
  rewrite -> elemVarSet_extendVarSet by solve_varset_inv.
  rewrite -> !elemVarSet_emptyVarSet. destruct (Foldable.elem v vs), (v' == v); simpl; intuition discriminate.
Qed.
Lemma elemVarSet_mkVarset_iff_In v vs :
  elemVarSet v (mkVarSet vs) <-> List.In (varUnique v) (map varUnique vs).
Proof.
  rewrite -> mkVarSet_extendVarSetList, elemVarSet_extendVarSetList by solve_varset_inv.
  rewrite -> elemVarSet_emptyVarSet, Bool.orb_false_r. symmetry. apply In_varUnique_elem.
Qed.

Lemma lookupVarSet_extendVarSetList_false vars v s : WF s ->
  ~~ Foldable.elem v vars ->
  lookupVarSet (extendVarSetList s vars) v = lookupVarSet s v.
Proof.
  revert s. induction vars as [|x xs IH]; intros s W H; [reflexivity|].
  rewrite -> elem_cons, negb_orb in H. apply Bool.andb_true_iff in H.
  destruct H as [H H']. rewrite -> extendVarSetList_cons, IH by (solve_varset_inv || assumption).
  apply lookupVarSet_extendVarSet_neq; [exact W|].
  rewrite Eq_sym. intro E. rewrite E in H. discriminate.
Qed.
Lemma lookupVarSet_extendVarSetList_l v s vars : WF s ->
  ~~ elemVarSet v (mkVarSet vars) ->
  lookupVarSet (extendVarSetList s vars) v = lookupVarSet s v.
Proof.
  intro W. rewrite -> mkVarSet_extendVarSetList,
    elemVarSet_extendVarSetList by solve_varset_inv.
  rewrite -> elemVarSet_emptyVarSet, Bool.orb_false_r.
  apply lookupVarSet_extendVarSetList_false; exact W.
Qed.
Lemma lookupVarSet_extendVarSetList_self vars v s : WF s ->
  Foldable.elem v vars -> lookupVarSet (extendVarSetList s vars) v == Some v.
Proof.
  revert s. induction vars as [|x xs IH]; intros s W H.
  - rewrite elem_nil in H. discriminate.
  - rewrite elem_cons in H. apply Bool.orb_true_iff in H.
    rewrite extendVarSetList_cons.
    destruct (Foldable.elem v xs) eqn:M.
    + apply IH; [solve_varset_inv|reflexivity].
    + assert (N : negb (Foldable.elem v xs) = true) by (rewrite M; reflexivity).
      rewrite -> (lookupVarSet_extendVarSetList_false xs v (extendVarSet s x)
        (extendVarSet_WF s x W) N).
      destruct H as [H|H]; [|discriminate].
      assert (E : x == v) by (rewrite Eq_sym; exact H).
      rewrite -> (lookupVarSet_extendVarSet_eq x v s W E).
      change (x == v). rewrite Eq_sym. exact H.
Qed.
Lemma lookupVarSet_extendVarSetList_self_in vars v s : WF s ->
  List.In v vars -> NoDup (map varUnique vars) ->
  lookupVarSet (extendVarSetList s vars) v = Some v.
Proof.
  revert s. induction vars as [|x xs IH]; intros s W H D; [contradiction|].
  inversion D as [|u us N ND]; subst.
  rewrite extendVarSetList_cons. destruct H as [H|H].
  - subst x. assert (M : negb (Foldable.elem v xs) = true).
    { apply Bool.negb_true_iff; apply Bool.not_true_is_false.
      intro M; apply N; apply In_varUnique_elem; exact M. }
    rewrite -> (lookupVarSet_extendVarSetList_false xs v (extendVarSet s v)
      (extendVarSet_WF s v W) M).
    apply lookupVarSet_extendVarSet_self; exact W.
  - apply IH; [solve_varset_inv|exact H|exact ND].
Qed.

Inductive LastIn : Var -> list Var -> Prop :=
| LastIn_head : forall v vs, Foldable.elem v vs = false -> LastIn v (v :: vs)
| LastIn_tail : forall v w vs, LastIn v vs -> LastIn v (w :: vs).
Lemma LastIn_elem v vs : LastIn v vs -> Foldable.elem v vs.
Proof.
  intro H; induction H; rewrite elem_cons; apply Bool.orb_true_iff;
    [left; apply Eq_refl|right; assumption].
Qed.

Lemma elemVarSet_delVarSetList_false_l v s xs : WF s ->
  elemVarSet v s = false -> elemVarSet v (delVarSetList s xs) = false.
Proof.
  intros W H. apply Bool.not_true_is_false. change (~ In v (delVarSetList s xs)).
  rewrite -> delVarSetList_iff by exact W. unfold In. rewrite H. intuition discriminate.
Qed.
Lemma delVarSetList_cons2 xs s a : WF s ->
  delVarSetList s (a :: xs) [=] delVarSet (delVarSetList s xs) a.
Proof.
  intros W x. rewrite -> delVarSetList_iff by exact W.
  rewrite -> delVarSet_remove, remove_iff by solve_varset_inv.
  rewrite -> delVarSetList_iff by exact W.
  rewrite elem_cons. unfold is_true. rewrite Bool.orb_true_iff.
  unfold E.eq, E.eqb, E.t. rewrite Eq_sym. tauto.
Qed.
Lemma delVarSetList_rev s xs : WF s -> delVarSetList s (rev xs) [=] delVarSetList s xs.
Proof.
  intros W x. rewrite -> !delVarSetList_iff by exact W.
  rewrite <- (In_varUnique_elem x (rev xs)), <- (In_varUnique_elem x xs), map_rev, in_rev.
  rewrite rev_involutive. reflexivity.
Qed.

Lemma elemVarSet_filterVarSet x f s : WF s -> ValidVarSet s -> RespectsVar f ->
  elemVarSet x (filterVarSet f s) = f x && elemVarSet x s.
Proof.
  intros W V R. apply Bool.eq_true_iff_eq.
  change (In x (filter f s) <-> (f x && elemVarSet x s) = true).
  rewrite -> filter_iff by assumption. rewrite Bool.andb_true_iff. unfold In. tauto.
Qed.
Lemma filterVarSet_equal f s t : WF s -> WF t ->
  ValidVarSet s -> ValidVarSet t -> RespectsVar f -> s [=] t ->
  filterVarSet f s [=] filterVarSet f t.
Proof. intros W T V U R E x. rewrite -> !filterVarSet_filter, !filter_iff by assumption. rewrite E. reflexivity. Qed.
Lemma filterVarSet_emptyVarSet f : filterVarSet f emptyVarSet = emptyVarSet.
Proof. reflexivity. Qed.
Lemma filterSingletonTrue f x : RespectsVar f -> f x = true ->
  filterVarSet f (unitVarSet x) [=] unitVarSet x.
Proof.
  intros R H y. rewrite -> filterVarSet_filter, filter_iff by (solve_varset_inv || assumption).
  rewrite -> unitVarSet_singleton, singleton_iff. split; [tauto|].
  intro E; split; [exact E|]. rewrite <- (R x y E). exact H.
Qed.
Lemma filterSingletonFalse f x : RespectsVar f -> f x = false ->
  filterVarSet f (unitVarSet x) [=] emptyVarSet.
Proof.
  intros R H y. rewrite -> filterVarSet_filter, filter_iff by (solve_varset_inv || assumption).
  rewrite -> unitVarSet_singleton, singleton_iff, emptyVarSet_empty, empty_iff.
  split; [|tauto]. intros [E K]. rewrite <- (R x y E), H in K. discriminate.
Qed.
Lemma filterVarSet_constTrue s : WF s ->
  filterVarSet (const true) s [=] s.
Proof.
  intro W. apply lookupVarSet_Equal; [solve_varset_inv|exact W|].
  intro x. rewrite -> (lookupVarSet_filter (const true) s x W).
  destruct (lookupVarSet s x); reflexivity.
Qed.
Lemma lookupVarSet_filterVarSet_true f v s : WF s -> ValidVarSet s ->
  RespectsVar f -> f v = true -> lookupVarSet (filterVarSet f s) v = lookupVarSet s v.
Proof.
  intros W V R H. rewrite (lookupVarSet_filter f s v W).
  destruct (lookupVarSet s v) as [w|] eqn:L; [|reflexivity].
  rewrite <- (R v w (V v w L)), H. reflexivity.
Qed.
Lemma lookupVarSet_filterVarSet_false f v s : WF s -> ValidVarSet s ->
  RespectsVar f -> f v = false -> lookupVarSet (filterVarSet f s) v = None.
Proof.
  intros W V R H. rewrite (lookupVarSet_filter f s v W).
  destruct (lookupVarSet s v) as [w|] eqn:L; [|reflexivity].
  rewrite <- (R v w (V v w L)), H. reflexivity.
Qed.

Lemma elemVarSet_unionVarSet v s t : WF s -> WF t ->
  elemVarSet v (unionVarSet s t) = elemVarSet v s || elemVarSet v t.
Proof. apply elemVarSet_union. Qed.
Lemma unionVarSet_sym s t : WF s -> WF t -> unionVarSet s t [=] unionVarSet t s.
Proof. intros W T; fsetdec. Qed.
Lemma unionEmpty_l s : unionVarSet emptyVarSet s [=] s.
Proof.
  destruct s as [[m]].
  change (UniqSet.Mk_UniqSet (UniqFM.UFM (Data.IntMap.Internal.union m Data.IntMap.Internal.Nil))
    [=] UniqSet.Mk_UniqSet (UniqFM.UFM m)).
  rewrite IntMapUnionProofs.union_Nil_r. reflexivity.
Qed.
Lemma unionEmpty_r s : unionVarSet s emptyVarSet [=] s.
Proof.
  destruct s as [[m]].
  change (UniqSet.Mk_UniqSet (UniqFM.UFM (Data.IntMap.Internal.union Data.IntMap.Internal.Nil m))
    [=] UniqSet.Mk_UniqSet (UniqFM.UFM m)).
  rewrite IntMapUnionProofs.union_Nil_l. reflexivity.
Qed.
Lemma unionSingle_l x s : WF s -> unionVarSet (unitVarSet x) s [=] extendVarSet s x.
Proof. intros W; fsetdec. Qed.
Lemma unionSingle_r x s : WF s -> unionVarSet s (unitVarSet x) [=] extendVarSet s x.
Proof. intros W; fsetdec. Qed.
Lemma delVarSet_unionVarSet s t x : WF s -> WF t ->
  delVarSet (unionVarSet s t) x [=] unionVarSet (delVarSet s x) (delVarSet t x).
Proof. intros W T; fsetdec. Qed.
Lemma delVarSetList_unionVarSet xs s t : WF s -> WF t ->
  delVarSetList (unionVarSet s t) xs [=]
  unionVarSet (delVarSetList s xs) (delVarSetList t xs).
Proof.
  intros W T x. rewrite -> !delVarSetList_iff by solve_varset_inv.
  rewrite -> !unionVarSet_union, !union_iff by solve_varset_inv.
  rewrite -> !delVarSetList_iff by assumption. tauto.
Qed.
Lemma unionVarSet_filterVarSet f s t : WF s -> WF t ->
  ValidVarSet s -> ValidVarSet t -> RespectsVar f ->
  unionVarSet (filterVarSet f s) (filterVarSet f t) [=] filterVarSet f (unionVarSet s t).
Proof. intros W T V U R; fsetdec. Qed.
Lemma filterVarSet_delVarSet f s v : WF s -> RespectsVar f ->
  filterVarSet f (delVarSet s v) [=] delVarSet (filterVarSet f s) v.
Proof.
  intros W R. apply lookupVarSet_Equal; [solve_varset_inv|solve_varset_inv|].
  intro x. rewrite -> (lookupVarSet_filter f (delVarSet s v) x (delVarSet_WF s v W)),
    (lookupVarSet_del s v x W),
    (lookupVarSet_del (filterVarSet f s) v x (filterVarSet_WF f s W)),
    (lookupVarSet_filter f s x W).
  destruct (N.eqb (Unique.getWordKey (Unique.getUnique x))
    (Unique.getWordKey (Unique.getUnique v))); reflexivity.
Qed.
Lemma filterVarSet_comp f g s : WF s ->
  filterVarSet f (filterVarSet g s) [=] filterVarSet (fun v => f v && g v) s.
Proof.
  intro W. apply lookupVarSet_Equal; [solve_varset_inv|solve_varset_inv|].
  intro x. rewrite -> (lookupVarSet_filter f (filterVarSet g s) x (filterVarSet_WF g s W)),
    (lookupVarSet_filter g s x W), (lookupVarSet_filter (fun v => f v && g v) s x W).
  destruct (lookupVarSet s x) as [v|]; [destruct (g v), (f v)|]; reflexivity.
Qed.
Lemma filterVarSet_extendVarSet f v s : WF s -> ValidVarSet s -> RespectsVar f ->
  filterVarSet f (extendVarSet s v) [=]
    if f v then extendVarSet (filterVarSet f s) v else filterVarSet f s.
Proof.
  intros W V R x. rewrite -> filterVarSet_filter, filter_iff by (solve_varset_inv || assumption).
  rewrite -> extendVarSet_add, add_iff by exact W.
  destruct (f v) eqn:F.
  - rewrite -> extendVarSet_add, add_iff by solve_varset_inv.
    rewrite -> filter_iff by assumption.
    assert (K : E.eq v x -> f x = true) by (intro E; rewrite <- (R v x E); exact F).
    tauto.
  - rewrite -> filter_iff by assumption.
    assert (K : E.eq v x -> f x <> true) by (intro E; rewrite <- (R v x E), F; discriminate).
    tauto.
Qed.
Lemma filterVarSet_delVarSetList f xs s : WF s -> RespectsVar f ->
  filterVarSet f (delVarSetList s xs) [=] delVarSetList (filterVarSet f s) xs.
Proof.
  revert s. induction xs as [|x xs IH]; intros s W R.
  - rewrite !delVarSetList_nil. reflexivity.
  - rewrite !delVarSetList_cons.
    transitivity (delVarSetList (filterVarSet f (delVarSet s x)) xs).
    + apply IH; [solve_varset_inv|exact R].
    + apply delVarSetList_m; [solve_varset_inv|solve_varset_inv| |].
      * apply filterVarSet_delVarSet; assumption.
      * clear IH. induction xs as [|y ys IHy]; [constructor|].
        constructor; [apply Eq_refl|exact IHy].
Qed.

Lemma subVarSet_refl s : WF s -> ValidVarSet s -> subVarSet s s.
Proof. intros W V. apply (proj2 (subVarSet_spec s s W W V)); auto. Qed.
Lemma subVarSet_trans s t u : WF s -> WF t -> WF u ->
  ValidVarSet s -> ValidVarSet t ->
  subVarSet s t -> subVarSet t u -> subVarSet s u.
Proof.
  intros W T U V Q H K. apply (proj2 (subVarSet_spec s u W U V)).
  intros x M. apply (proj1 (subVarSet_spec t u T U Q) K).
  apply (proj1 (subVarSet_spec s t W T V) H). exact M.
Qed.
Lemma subVarSet_emptyVarSet s : WF s -> subVarSet emptyVarSet s.
Proof.
  intro W. apply (proj2 (subVarSet_spec _ _ emptyVarSet_WF W emptyVarSet_valid)).
  intros x H. discriminate H.
Qed.
Lemma subVarSet_equal_empty s t : WF s -> WF t -> ValidVarSet s ->
  s [=] emptyVarSet -> subVarSet s t = true.
Proof.
  intros W T V E. apply (proj2 (subVarSet_spec _ _ W T V)).
  intros x H. apply (proj1 (E x)) in H. discriminate H.
Qed.
Lemma subVarSet_elemVarSet_true v s t : WF s -> WF t -> ValidVarSet s ->
  subVarSet s t -> elemVarSet v s -> elemVarSet v t.
Proof. intros W T V H; apply (proj1 (subVarSet_spec s t W T V) H). Qed.
Lemma subVarSet_elemVarSet_false v s t : WF s -> WF t -> ValidVarSet s ->
  subVarSet s t -> elemVarSet v t = false -> elemVarSet v s = false.
Proof.
  intros W T V H K. destruct (elemVarSet v s) eqn:M; [|reflexivity].
  pose proof (subVarSet_elemVarSet_true v s t W T V H M) as N.
  rewrite K in N. discriminate.
Qed.
Lemma subVarSet_unitVarSet v s : WF s ->
  subVarSet (unitVarSet v) s = elemVarSet v s.
Proof.
  intro W. apply Bool.eq_true_iff_eq.
  rewrite (subVarSet_spec _ _ (unitVarSet_WF v) W (unitVarSet_valid v)).
  split.
  - intro H. apply H. rewrite elemVarSet_unit. apply Eq_refl.
  - intros H x M. rewrite elemVarSet_unit in M.
    rewrite (elemVarSet_eq x v s M). exact H.
Qed.
Lemma extendVarSet_subset s t x : WF s -> WF t ->
  s [<=] t -> extendVarSet s x [<=] extendVarSet t x.
Proof. intros W T H; fsetdec. Qed.
Lemma extendVarSetList_subset s t xs : WF s -> WF t ->
  s [<=] t -> extendVarSetList s xs [<=] extendVarSetList t xs.
Proof.
  intros W T H x. rewrite -> !extendVarSetList_iff by assumption. firstorder.
Qed.
Lemma subVarSet_extendVarSet s t v : WF s -> WF t -> ValidVarSet s ->
  subVarSet s t -> subVarSet s (extendVarSet t v).
Proof. intros W T V H; fsetdec. Qed.
Lemma subVarSet_extendVarSet_both s t v : WF s -> WF t -> ValidVarSet s ->
  subVarSet s t -> subVarSet (extendVarSet s v) (extendVarSet t v).
Proof. intros W T V H; fsetdec. Qed.
Lemma subVarSet_extendVarSet_l s t v w : WF s -> WF t -> ValidVarSet s ->
  subVarSet s t -> lookupVarSet t v = Some w -> subVarSet (extendVarSet s v) t.
Proof.
  intros W T V H K. pose proof (lookupVarSet_member t v w T K) as M.
  fsetdec.
Qed.
Lemma subVarSet_extendVarSetList s t xs : WF s -> WF t -> ValidVarSet s ->
  subVarSet s t -> subVarSet s (extendVarSetList t xs).
Proof.
  intros W T V H. apply (proj2 (subVarSet_spec _ _ W
    (extendVarSetList_WF t xs T) V)).
  intros x M. change (In x (extendVarSetList t xs)). rewrite -> extendVarSetList_iff by exact T. left.
  apply (proj1 (subVarSet_spec s t W T V) H). exact M.
Qed.
Lemma subVarSet_extendVarSetList_l s t xs : WF s -> WF t -> ValidVarSet s ->
  subVarSet s t -> subVarSet s (extendVarSetList t xs).
Proof. apply subVarSet_extendVarSetList. Qed.
Lemma subVarSet_delVarSet s v : WF s -> ValidVarSet s -> subVarSet (delVarSet s v) s.
Proof. intros W V; fsetdec. Qed.
Lemma subVarSet_delVarSetList s xs : WF s -> ValidVarSet s ->
  subVarSet (delVarSetList s xs) s.
Proof.
  intros W V. apply (proj2 (subVarSet_spec _ _ (delVarSetList_WF s xs W) W
    (delVarSetList_valid s xs W V))).
  intros x H. change (In x (delVarSetList s xs)) in H.
  rewrite -> delVarSetList_iff in H by exact W. exact (proj1 H).
Qed.
Lemma subVarSet_unionVarSet s t u : WF s -> WF t -> WF u ->
  ValidVarSet s -> ValidVarSet t ->
  subVarSet (unionVarSet s t) u = subVarSet s u && subVarSet t u.
Proof.
  intros W T U V Q. apply Bool.eq_true_iff_eq. rewrite Bool.andb_true_iff.
  rewrite -> !subVarSet_spec by solve_varset_inv.
  split.
  - intro H. split; intros x M; apply H; rewrite -> elemVarSet_union by assumption;
      apply Bool.orb_true_iff; auto.
  - intros [H K] x M. rewrite -> elemVarSet_union in M by assumption.
    apply Bool.orb_true_iff in M. destruct M; auto.
Qed.

Lemma subVarSet_delVarSetList_both s t xs : WF s -> WF t -> ValidVarSet s ->
  subVarSet s t -> subVarSet (delVarSetList s xs) (delVarSetList t xs).
Proof.
  intros W T V H. apply (proj2 (subVarSet_spec _ _
    (delVarSetList_WF s xs W) (delVarSetList_WF t xs T) (delVarSetList_valid s xs W V))).
  intros x M. change (In x (delVarSetList s xs)) in M.
  rewrite -> delVarSetList_iff in M by exact W.
  change (In x (delVarSetList t xs)). rewrite -> delVarSetList_iff by exact T. split; [|exact (proj2 M)].
  apply (proj1 (subVarSet_spec _ _ W T V) H). exact (proj1 M).
Qed.
Lemma subVarSet_delVarSet_extendVarSet s t v : WF s -> WF t -> ValidVarSet s ->
  subVarSet s t -> subVarSet (delVarSet s v) (extendVarSet t v).
Proof. intros W T V H; fsetdec. Qed.
Lemma subVarSet_delVarSetList_extendVarSetList s t xs : WF s -> WF t -> ValidVarSet s ->
  subVarSet s t -> subVarSet (delVarSetList s xs) (extendVarSetList t xs).
Proof.
  intros W T V H. apply (proj2 (subVarSet_spec _ _
    (delVarSetList_WF s xs W) (extendVarSetList_WF t xs T) (delVarSetList_valid s xs W V))).
  intros x M. change (In x (delVarSetList s xs)) in M.
  rewrite -> delVarSetList_iff in M by exact W.
  change (In x (extendVarSetList t xs)). rewrite -> extendVarSetList_iff by exact T. left.
  apply (proj1 (subVarSet_spec _ _ W T V) H). exact (proj1 M).
Qed.
Lemma subVarSet_delVarSetList_extendVarSetList_dual s t xs : WF s -> WF t -> ValidVarSet s ->
  subVarSet s (extendVarSetList t xs) -> subVarSet (delVarSetList s xs) t.
Proof.
  intros W T V H. apply (proj2 (subVarSet_spec _ _
    (delVarSetList_WF s xs W) T (delVarSetList_valid s xs W V))).
  intros x M. change (In x (delVarSetList s xs)) in M.
  rewrite -> delVarSetList_iff in M by exact W.
  pose proof (proj1 (subVarSet_spec _ _ W (extendVarSetList_WF t xs T) V) H x (proj1 M)) as N.
  change (In x (extendVarSetList t xs)) in N.
  rewrite -> extendVarSetList_iff in N by exact T. tauto.
Qed.
Lemma subVarSet_extendVarSetList_r xs s t : WF s -> WF t -> ValidVarSet s ->
  subVarSet s (mkVarSet xs) -> subVarSet s (extendVarSetList t xs).
Proof.
  intros W T V H. apply (proj2 (subVarSet_spec _ _ W (extendVarSetList_WF t xs T) V)).
  intros x M. pose proof (proj1 (subVarSet_spec _ _ W (mkVarSet_WF xs) V) H x M) as N.
  change (In x (mkVarSet xs)) in N.
  rewrite -> mkVarSet_extendVarSetList, extendVarSetList_iff in N by solve_varset_inv.
  change (In x (extendVarSetList t xs)).
  rewrite -> extendVarSetList_iff by exact T. destruct N as [N|N]; [discriminate N|auto].
Qed.
Lemma elemVarSet_false_true v1 s v2 :
  elemVarSet v1 s = false -> elemVarSet v2 s -> varUnique v1 <> varUnique v2.
Proof.
  intros H K E. assert (Q : v1 == v2) by (rewrite varUnique_iff; exact E).
  rewrite -> (elemVarSet_eq v1 v2 s Q), K in H. discriminate.
Qed.

Lemma mapUnionVarSet_In_subVarSet {a} (x : a) xs f :
  (forall y, List.In y xs -> WF (f y)) ->
  (forall y, List.In y xs -> ValidVarSet (f y)) ->
  List.In x xs -> subVarSet (f x) (mapUnionVarSet f xs).
Proof.
  intros W V H. apply (proj2 (subVarSet_spec _ _ (W x H)
    (mapUnionVarSet_WF f xs W) (V x H))).
  intros v M. revert W V H. induction xs as [|y ys IH]; intros W V H; [contradiction|].
  change (elemVarSet v (unionVarSet (f y) (mapUnionVarSet f ys)) = true).
  assert (Wy : WF (f y)) by (apply W; left; reflexivity).
  assert (Ws : WF (mapUnionVarSet f ys)) by
    (apply mapUnionVarSet_WF; intros z Z; apply W; right; exact Z).
  rewrite -> elemVarSet_union by assumption.
  apply Bool.orb_true_iff. destruct H as [H|H].
  - subst y. auto.
  - right. apply IH; auto; intros z Z; [apply W|apply V]; right; exact Z.
Qed.

Lemma lookupVarSet_ae vs v1 v2 : almostEqual v1 v2 ->
  lookupVarSet vs v1 = lookupVarSet vs v2.
Proof. induction 1; simpl; unfold UniqFM.lookupUFM; simpl; auto. Qed.
Lemma delVarSet_ae vs v1 v2 : almostEqual v1 v2 ->
  delVarSet vs v1 = delVarSet vs v2.
Proof. induction 1; simpl; unfold UniqFM.delFromUFM; simpl; auto. Qed.
Lemma elemVarSet_ae vs v1 v2 : almostEqual v1 v2 ->
  elemVarSet v1 vs = elemVarSet v2 vs.
Proof. induction 1; simpl; unfold UniqFM.delFromUFM; simpl; auto. Qed.
Lemma Forall2_diag a P (xs : list a) :
  Forall2 P xs xs <-> Forall (fun x => P x x) xs.
Proof. induction xs; split; intro H; constructor; inversion H; intuition. Qed.
Lemma lookupVarSet_delVarSet_None v s : WF s -> lookupVarSet (delVarSet s v) v = None.
Proof. intro W. rewrite -> (lookupVarSet_del s v v W), N.eqb_refl. reflexivity. Qed.
Definition freshList (vars : list Var) (vs : VarSet) :=
  forall v, Foldable.elem v vars -> lookupVarSet vs v = None.
Lemma freshList_nil s : freshList nil s.
Proof. intros v H. rewrite elem_nil in H. discriminate. Qed.
Lemma freshList_cons x xs s :
  lookupVarSet s x = None /\ freshList xs s <-> freshList (x :: xs) s.
Proof.
  unfold freshList. split.
  - intros [H K] v M. rewrite elem_cons in M. apply Bool.orb_true_iff in M.
    destruct M as [E|M]; [rewrite (lookupVarSet_eq v x s E); exact H|apply K; exact M].
  - intro H; split.
    + apply H. rewrite -> elem_cons, Eq_refl. reflexivity.
    + intros v M. apply H. rewrite -> elem_cons, M, Bool.orb_true_r. reflexivity.
Qed.
Lemma freshList_app s xs ys : freshList (xs ++ ys) s <-> freshList xs s /\ freshList ys s.
Proof.
  induction xs as [|x xs IH]; simpl List.app.
  - split; [intro H; split; [apply freshList_nil|exact H]|tauto].
  - rewrite <- !freshList_cons, IH. tauto.
Qed.
Lemma elemVarSet_unitVarSet_is_eq x v : elemVarSet x (unitVarSet v) = (x == v).
Proof. apply elemVarSet_unit. Qed.
Lemma UniqSet_Mk_UniqSet_eta a b (x : UniqSet.UniqSet a) (f : UniqSet.UniqSet a -> b) :
  match x with UniqSet.Mk_UniqSet s => f (UniqSet.Mk_UniqSet s) end = f x.
Proof. destruct x; reflexivity. Qed.

(* These higher-order instances are raw-true: the premise explicitly demands
   the congruence law for the supplied folding function.  They do not assert
   any such law for the structural VarSet operations. *)
#[export] Instance foldr_m :
  Proper (((fun x y : Var => x == y) ==> Equal ==> Equal) ==> Equal ==>
    (fun a b : list Var => a = b) ==> Equal) Foldable.foldr.
Proof.
  intros f g F s t E xs ys L; subst ys. revert s t E.
  induction xs as [|x xs IH]; intros s t E.
  - exact E.
  - rewrite !Foldable_foldr_cons. apply F; [apply Eq_refl|apply IH; exact E].
Qed.
#[export] Instance foldr_mE :
  Proper ((Equal ==> Equal ==> Equal) ==> Equal ==> Forall2 Equal ==> Equal) Foldable.foldr.
Proof.
  intros f g F s t E xs ys L. revert s t E.
  induction L; intros s t E.
  - exact E.
  - rewrite !Foldable_foldr_cons. apply F; [assumption|apply IHL; exact E].
Qed.

Lemma LastIn_inj v1 v2 vs : LastIn v1 vs -> v1 == v2 -> LastIn v2 vs -> v1 = v2.
Proof.
  intro H. induction H; intros E K; inversion K; subst; try reflexivity;
    try solve [eapply IHLastIn; eauto].
  all: match goal with
    | N : Foldable.elem ?a ?xs = false, L : LastIn ?b ?xs |- _ =>
      let M := fresh "M" in
      let Q := fresh "Q" in
      pose proof (LastIn_elem b xs L) as M;
      assert (Q : a == b) by (assumption || (rewrite Eq_sym; assumption));
      rewrite <- (elem_eq xs a b Q) in M; rewrite N in M; discriminate M
    end.
Qed.
Lemma lookupVarSet_extendVarSetList_self_exists_LastIn vars v s : WF s ->
  Foldable.elem v vars -> exists v', and3
    (lookupVarSet (extendVarSetList s vars) v = Some v') (v == v') (LastIn v' vars).
Proof.
  revert s. induction vars as [|x xs IH]; intros s W M.
  - rewrite elem_nil in M; discriminate.
  - rewrite elem_cons in M. apply Bool.orb_true_iff in M.
    rewrite extendVarSetList_cons. destruct (Foldable.elem v xs) eqn:T.
    + destruct (IH (extendVarSet s x) (extendVarSet_WF s x W) (Logic.eq_refl true))
        as [w [L E K]]. exists w; split; [exact L|exact E|apply LastIn_tail; exact K].
    + destruct M as [E|M]; [|discriminate M].
      assert (N : negb (Foldable.elem v xs) = true) by (rewrite T; reflexivity).
      rewrite -> (lookupVarSet_extendVarSetList_false xs v (extendVarSet s x)
        (extendVarSet_WF s x W) N).
      exists x; split; [|exact E|].
      * apply lookupVarSet_extendVarSet_eq; [exact W|rewrite Eq_sym; exact E].
      * apply LastIn_head. rewrite <- (elem_eq xs v x E). exact T.
Qed.
Lemma extendVarSetList_same v vars s t : WF s -> WF t -> Foldable.elem v vars ->
  lookupVarSet (extendVarSetList s vars) v = lookupVarSet (extendVarSetList t vars) v.
Proof.
  intros W T M.
  destruct (lookupVarSet_extendVarSetList_self_exists_LastIn vars v s W M) as [x [L E K]].
  destruct (lookupVarSet_extendVarSetList_self_exists_LastIn vars v t T M) as [y [L' E' K']].
  assert (Q : x == y) by (eapply Eq_trans; [rewrite Eq_sym; exact E|exact E']).
  pose proof (LastIn_inj x y vars K Q K') as F. subst y. rewrite -> L, L'. reflexivity.
Qed.

Lemma IntMapEq_VarSetEq x y : x == y ->
  UniqSet.Mk_UniqSet (UniqFM.UFM x) [=] UniqSet.Mk_UniqSet (UniqFM.UFM y).
Proof.
  intros E v. unfold In, elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
  rewrite -> (Proofs.ContainerProofs.Eq_membership Var _ EqLaws_Var x y E). reflexivity.
Qed.
Lemma minusVarSet_emptyVarSet s : minusVarSet s emptyVarSet = s.
Proof.
  destruct s as [[m]]. unfold minusVarSet, emptyVarSet, UniqSet.minusUniqSet,
    UniqSet.emptyUniqSet, UniqFM.minusUFM, UniqFM.emptyUFM.
  rewrite Proofs.ContainerProofs.difference_nil_r. reflexivity.
Qed.
Lemma minusVarSet_emptyVarSet_l s : minusVarSet emptyVarSet s = emptyVarSet.
Proof.
  destruct s as [[m]]. unfold minusVarSet, emptyVarSet, UniqSet.minusUniqSet,
    UniqSet.emptyUniqSet, UniqFM.minusUFM, UniqFM.emptyUFM.
  rewrite Proofs.ContainerProofs.difference_nil_l. reflexivity.
Qed.
Lemma elemVarSet_minusVarSet x s t : WF s -> WF t ->
  elemVarSet x (minusVarSet s t) = elemVarSet x s && negb (elemVarSet x t).
Proof. apply elemVarSet_minus. Qed.
Lemma elemVarSet_minusVarSetTrue x s : WF s -> elemVarSet x s = true ->
  minusVarSet (unitVarSet x) s [=] emptyVarSet.
Proof. intros W H; fsetdec. Qed.
Lemma elemVarSet_minusVarSetFalse x s : WF s -> elemVarSet x s = false ->
  minusVarSet (unitVarSet x) s [=] unitVarSet x.
Proof.
  intros W H a. rewrite -> minusVarSet_diff, diff_iff by solve_varset_inv.
  rewrite -> unitVarSet_singleton, singleton_iff. split; [tauto|].
  intro E; split; [exact E|]. intro K.
  assert (L : In x s) by (eapply In_1; [symmetry; exact E|exact K]).
  unfold In in L; rewrite H in L; discriminate.
Qed.
Lemma unionVarSet_minusVarSet s t u : WF s -> WF t -> WF u ->
  unionVarSet (minusVarSet s u) (minusVarSet t u) [=] minusVarSet (unionVarSet s t) u.
Proof. intros W T U; fsetdec. Qed.

Lemma extendVarSetList_foldl' s xs :
  extendVarSetList s xs = Foldable.foldl' (fun s x => add x s) s xs.
Proof. reflexivity. Qed.
Lemma delVarSetList_foldl xs s : delVarSetList s xs = Foldable.foldl delVarSet s xs.
Proof.
  revert s. induction xs as [|x xs IH]; intro s.
  - rewrite delVarSetList_nil. reflexivity.
  - rewrite -> delVarSetList_cons, Foldable_foldl_cons. apply IH.
Qed.
Lemma foldl_m s t (xs ys : list Var) : WF s -> WF t -> s [=] t -> xs = ys ->
  Foldable.foldl delVarSet s xs [=] Foldable.foldl delVarSet t ys.
Proof.
  intros W T E L; subst ys. rewrite <- !delVarSetList_foldl.
  apply delVarSetList_m; [exact W|exact T|exact E|].
  induction xs; constructor; [apply Eq_refl|assumption].
Qed.
Lemma delVarSetList_commute (xs : list Var) s x : WF s ->
  Foldable.foldl delVarSet (delVarSet s x) xs [=]
  delVarSet (Foldable.foldl delVarSet s xs) x.
Proof.
  intro W. rewrite <- !delVarSetList_foldl.
  rewrite <- (delVarSetList_cons2 xs s x W). rewrite delVarSetList_cons. reflexivity.
Qed.
Lemma delVarSetList_foldr s xs : WF s ->
  delVarSetList s xs [=] Foldable.foldr (fun x s => delVarSet s x) s xs.
Proof.
  revert s. induction xs as [|x xs IH]; intros s W.
  - rewrite delVarSetList_nil. reflexivity.
  - rewrite Foldable_foldr_cons. transitivity (delVarSet (delVarSetList s xs) x).
    + apply delVarSetList_cons2; exact W.
    + apply delVarSet_m; [solve_varset_inv| |apply IH; exact W|apply Eq_refl].
      clear IH. induction xs as [|y ys IH]; [exact W|].
      rewrite Foldable_foldr_cons. apply delVarSet_WF. exact IH.
Qed.
Lemma delVarSetList_commute_foldr (xs : list Var) s x : WF s ->
  Foldable.foldr (fun x s => delVarSet s x) (delVarSet s x) xs [=]
  delVarSet (Foldable.foldr (fun x s => delVarSet s x) s xs) x.
Proof.
  intro W. transitivity (delVarSetList (delVarSet s x) xs).
  - symmetry. apply delVarSetList_foldr. solve_varset_inv.
  - transitivity (delVarSet (delVarSetList s xs) x).
    + rewrite <- delVarSetList_cons. apply delVarSetList_cons2; exact W.
    + apply delVarSet_m; [solve_varset_inv| |apply delVarSetList_foldr; exact W|apply Eq_refl].
      induction xs as [|y ys IH]; [exact W|].
      rewrite Foldable_foldr_cons. apply delVarSet_WF. exact IH.
Qed.

Lemma fold_unionVarSet_iff (ss : list VarSet) s x :
  (forall t, List.In t ss -> WF t) -> WF s ->
  (In x (Foldable.foldr unionVarSet s ss) <->
   In x s \/ exists t, List.In t ss /\ In x t).
Proof.
  intros W S. induction ss as [|t ts IH].
  - change (In x s <-> In x s \/ exists t, False /\ In x t). firstorder.
  - rewrite Foldable_foldr_cons. rewrite -> unionVarSet_union, union_iff.
    + rewrite -> IH by (intros u U; apply W; right; exact U).
      split.
      * intros [H|[H|[u [U H]]]].
        -- right; exists t; split; [left; reflexivity|exact H].
        -- left; exact H.
        -- right; exists u; split; [right; exact U|exact H].
      * intros [H|[u [[U|U] H]]].
        -- right; left; exact H.
        -- subst u; left; exact H.
        -- right; right; exists u; auto.
    + apply W; left; reflexivity.
    + apply fold_unionVarSet_WF; [intros u U; apply W; right; exact U|exact S].
Qed.
Lemma unionVarSet_commute (ss : list VarSet) v a :
  (forall s, List.In s ss -> WF s) -> WF v -> WF a ->
  unionVarSet v (Foldable.foldr unionVarSet a ss) [=]
  unionVarSet a (Foldable.foldr unionVarSet v ss).
Proof.
  intros W V A x. rewrite -> !unionVarSet_union, !union_iff by
    (assumption || (apply fold_unionVarSet_WF; assumption)).
  rewrite -> !fold_unionVarSet_iff by assumption. tauto.
Qed.
Lemma unionVarSets_def ss : (forall s, List.In s ss -> WF s) ->
  unionVarSets ss [=] Foldable.foldr unionVarSet emptyVarSet ss.
Proof.
  intros W x. destruct ss as [|s ss]; [reflexivity|].
  change (In x (Foldable.foldr unionVarSet s ss) <->
    In x (Foldable.foldr unionVarSet emptyVarSet (s :: ss))).
  rewrite -> !fold_unionVarSet_iff by
    (assumption || solve_varset_inv || (apply W; left; reflexivity) ||
     (intros t T; apply W; right; exact T)).
  rewrite -> emptyVarSet_empty, empty_iff.
  split.
  - intros [H|[t [T H]]]; right.
    + exists s; split; [left; reflexivity|exact H].
    + exists t; split; [right; exact T|exact H].
  - intros [H|[t [[T|T] H]]]; [contradiction|subst t; auto|right; exists t; auto].
Qed.
Lemma unionVarSets_cons s ss : WF s -> (forall t, List.In t ss -> WF t) ->
  unionVarSets (s :: ss) [=] unionVarSet s (unionVarSets ss).
Proof.
  intros S W x.
  rewrite -> (unionVarSets_def (s :: ss)) by (intros t [E|T]; [subst t; exact S|apply W; exact T]).
  rewrite Foldable_foldr_cons.
  rewrite -> !unionVarSet_union, !union_iff by
    (solve_varset_inv || (apply fold_unionVarSet_WF; [exact W|apply emptyVarSet_WF]) ||
      (apply unionVarSets_WF; exact W)).
  rewrite <- (unionVarSets_def ss W). reflexivity.
Qed.
Lemma unionsVarSet_equal ss ts :
  (forall s, List.In s ss -> WF s) -> (forall t, List.In t ts -> WF t) ->
  Forall2 Equal ss ts ->
  Foldable.foldr unionVarSet emptyVarSet ss [=] Foldable.foldr unionVarSet emptyVarSet ts.
Proof.
  intros W T L. revert W T. induction L; intros W T; [reflexivity|].
  rewrite !Foldable_foldr_cons. apply unionVarSet_m.
  - apply W; left; reflexivity.
  - apply T; left; reflexivity.
  - apply fold_unionVarSet_WF; [intros s S; apply W; right; exact S|apply emptyVarSet_WF].
  - apply fold_unionVarSet_WF; [intros s S; apply T; right; exact S|apply emptyVarSet_WF].
  - assumption.
  - apply IHL; intros s S; [apply W|apply T]; right; exact S.
Qed.
Lemma unionsVarSet_m ss ts :
  (forall s, List.In s ss -> WF s) -> (forall t, List.In t ts -> WF t) ->
  Forall2 Equal ss ts -> unionVarSets ss [=] unionVarSets ts.
Proof.
  intros W T L. rewrite -> (unionVarSets_def ss W), (unionVarSets_def ts T).
  apply unionsVarSet_equal; assumption.
Qed.
Lemma mapUnionVarSet_cons {a} f (x : a) xs :
  mapUnionVarSet f (x :: xs) [=] unionVarSet (f x) (mapUnionVarSet f xs).
Proof. reflexivity. Qed.
Lemma mapUnionVarSets_unionVarSets {a} (f : a -> VarSet) xs :
  (forall x, List.In x xs -> WF (f x)) ->
  mapUnionVarSet f xs [=] unionVarSets (List.map f xs).
Proof.
  intro W. rewrite -> unionVarSets_def by
    (intros s S; apply in_map_iff in S; destruct S as [x [E X]]; subst s; apply W; exact X).
  change (fold_right (fun x s => unionVarSet (f x) s) emptyVarSet xs [=]
    fold_right unionVarSet emptyVarSet (List.map f xs)).
  assert (E : fold_right (fun x s => unionVarSet (f x) s) emptyVarSet xs =
    fold_right unionVarSet emptyVarSet (List.map f xs)).
  { clear W. induction xs; simpl; [reflexivity|rewrite IHxs; reflexivity]. }
  rewrite E. reflexivity.
Qed.
Lemma delVarSet_unionVarSets ss x : (forall s, List.In s ss -> WF s) ->
  delVarSet (unionVarSets ss) x [=] unionVarSets (List.map (fun s => delVarSet s x) ss).
Proof.
  intro W. induction ss as [|s ss IH]; [reflexivity|].
  assert (S : WF s) by (apply W; left; reflexivity).
  assert (T : forall t, List.In t ss -> WF t) by (intros t U; apply W; right; exact U).
  transitivity (delVarSet (unionVarSet s (unionVarSets ss)) x).
  - apply delVarSet_m; [apply unionVarSets_WF; exact W|solve_varset_inv|apply unionVarSets_cons; assumption|apply Eq_refl].
  - transitivity (unionVarSet (delVarSet s x) (delVarSet (unionVarSets ss) x)).
    + apply delVarSet_unionVarSet; [exact S|apply unionVarSets_WF; exact T].
    + transitivity (unionVarSet (delVarSet s x) (unionVarSets (List.map (fun s => delVarSet s x) ss))).
      * apply unionVarSet_m; try solve_varset_inv.
        -- apply unionVarSets_WF; intros t U; apply in_map_iff in U;
             destruct U as [u [E U]]; subst t; apply delVarSet_WF; apply T; exact U.
        -- reflexivity.
        -- apply IH; exact T.
      * symmetry. apply unionVarSets_cons; [solve_varset_inv|].
        intros t U; apply in_map_iff in U; destruct U as [u [E U]];
          subst t; apply delVarSet_WF; apply T; exact U.
Qed.
Lemma subVarSet_mapUnionVarSet {a} (xs : list a) f s : WF s ->
  (forall x, List.In x xs -> WF (f x)) ->
  (forall x, List.In x xs -> ValidVarSet (f x)) ->
  Forall (fun x => subVarSet (f x) s) xs -> subVarSet (mapUnionVarSet f xs) s.
Proof.
  intros S W V H. induction xs as [|x xs IH]; [apply subVarSet_emptyVarSet; exact S|].
  inversion H as [|y ys Hx Hxs]; subst.
  change (subVarSet (unionVarSet (f x) (mapUnionVarSet f xs)) s = true).
  rewrite -> subVarSet_unionVarSet by
    (solve_varset_inv || (apply W; left; reflexivity) || (apply V; left; reflexivity) ||
     (apply mapUnionVarSet_WF; intros y Y; apply W; right; exact Y) ||
     (apply mapUnionVarSet_valid; intros y Y; [apply W|apply V]; right; exact Y)).
  apply Bool.andb_true_iff; split; [exact Hx|].
  apply IH; [intros y Y; apply W; right; exact Y|intros y Y; apply V; right; exact Y|exact Hxs].
Qed.

Lemma disjointVarSet_iff s t : WF s -> WF t -> ValidVarSet s ->
  (disjointVarSet s t = true <-> forall x, In x s -> ~ In x t).
Proof.
  intros W T V. rewrite -> (disjointVarSet_spec s t W T V).
  unfold In. split; intros H x M; specialize (H x M).
  - rewrite H; discriminate.
  - apply Bool.not_true_is_false; exact H.
Qed.
Lemma disjointVarSet_m s t u v : WF s -> WF t -> WF u -> WF v ->
  ValidVarSet s -> ValidVarSet t -> s [=] t -> u [=] v ->
  disjointVarSet s u = disjointVarSet t v.
Proof.
  intros W T U V P Q E F. apply Bool.eq_true_iff_eq.
  rewrite -> !disjointVarSet_iff by assumption.
  split; intros H x M N.
  - apply (H x); [apply (proj2 (E x)); exact M|apply (proj2 (F x)); exact N].
  - apply (H x); [apply (proj1 (E x)); exact M|apply (proj1 (F x)); exact N].
Qed.
Lemma disjointVarSet_empytVarSet s : disjointVarSet s emptyVarSet.
Proof.
  destruct s as [[m]]. apply Proofs.ContainerProofs.disjoint_empty_r.
Qed.
Lemma disjointVarSet_mkVarSet_nil s : disjointVarSet s (mkVarSet []).
Proof. apply disjointVarSet_empytVarSet. Qed.
Lemma disjointVarSet_extendVarSet s x t : WF s -> WF t -> ValidVarSet s ->
  (disjointVarSet s (extendVarSet t x) <-> elemVarSet x s = false /\ disjointVarSet s t).
Proof.
  intros W T V. unfold is_true.
  rewrite -> !disjointVarSet_iff by solve_varset_inv.
  split.
  - intro H; split.
    + apply Bool.not_true_is_false. intro M. apply (H x M).
      apply add_1; [exact T|apply E.eq_refl].
    + intros y M N. apply (H y M). apply add_2; assumption.
  - intros [H K] y M N. change (In y (add x t)) in N.
    rewrite -> add_iff in N by exact T. destruct N as [E|N].
    + assert (L : In x s) by (eapply In_1; [symmetry; exact E|exact M]).
      unfold In in L. rewrite H in L; discriminate.
    + exact (K y M N).
Qed.
Lemma disjointVarSet_mkVarSet s xs : WF s -> ValidVarSet s ->
  (disjointVarSet s (mkVarSet xs) <-> Forall (fun v => elemVarSet v s = false) xs).
Proof.
  intros W V. unfold is_true.
  rewrite -> (disjointVarSet_spec s (mkVarSet xs) W (mkVarSet_WF xs) V).
  rewrite Forall_forall. split.
  - intros H x X. apply Bool.not_true_is_false. intro M.
    specialize (H x M). assert (K : elemVarSet x (mkVarSet xs) = true).
    { apply elemVarSet_mkVarset_iff_In. apply in_map; exact X. }
    rewrite H in K; discriminate.
  - intros H x M. apply Bool.not_true_is_false. intro K.
    apply elemVarSet_mkVarset_iff_In in K. apply in_map_iff in K.
    destruct K as [v [E X]]. specialize (H v X).
    assert (Q : x == v) by (apply varUnique_iff; symmetry; exact E).
    rewrite <- (elemVarSet_eq x v s Q) in H. rewrite M in H; discriminate.
Qed.
Lemma disjointVarSet_mkVarSet_cons v s xs : WF s -> ValidVarSet s ->
  (disjointVarSet s (mkVarSet (v :: xs)) <->
   elemVarSet v s = false /\ disjointVarSet s (mkVarSet xs)).
Proof.
  intros W V. rewrite -> !disjointVarSet_mkVarSet by assumption.
  rewrite Forall_cons_iff. reflexivity.
Qed.
Lemma disjointVarSet_mkVarSet_append s xs ys : WF s -> ValidVarSet s ->
  (disjointVarSet s (mkVarSet (xs ++ ys)) <->
   disjointVarSet s (mkVarSet xs) /\ disjointVarSet s (mkVarSet ys)).
Proof.
  intros W V. rewrite -> !disjointVarSet_mkVarSet by assumption.
  apply Forall_app.
Qed.
Lemma elemNegbDisjoint s xs : WF s -> ValidVarSet s ->
  disjointVarSet s (mkVarSet xs) -> forall v, Foldable.elem v xs -> negb (elemVarSet v s).
Proof.
  intros W V H v M. apply Bool.negb_true_iff.
  pose proof (proj1 (disjointVarSet_spec s (mkVarSet xs) W (mkVarSet_WF xs) V) H) as D.
  apply Bool.not_true_is_false. intro K. specialize (D v K).
  rewrite -> mkVarSet_extendVarSetList, elemVarSet_extendVarSetList in D by solve_varset_inv.
  rewrite -> M, Bool.orb_true_l in D. discriminate.
Qed.
Lemma disjointVarSet_subVarSet_l s t u : WF s -> WF t -> WF u ->
  ValidVarSet s -> ValidVarSet t -> disjointVarSet t u -> subVarSet s t -> disjointVarSet s u.
Proof.
  intros W T U V Q H K. apply (proj2 (disjointVarSet_spec s u W U V)).
  intros x M. apply (proj1 (disjointVarSet_spec t u T U Q) H).
  apply (proj1 (subVarSet_spec s t W T V) K). exact M.
Qed.

#[export] Hint Rewrite elemVarSet_emptyVarSet
  extendVarSetList_nil extendVarSetList_cons extendVarSetList_singleton
  extendVarSetList_append delVarSetList_nil delVarSetList_cons
  delVarSetList_single delVarSetList_app delVarSet_emptyVarSet
  filterVarSet_emptyVarSet minusVarSet_emptyVarSet minusVarSet_emptyVarSet_l
  elemVarSet_unitVarSet_is_eq : hs_simpl.
#[export] Hint Rewrite elemVarSet_extendVarSet elemVarSet_extendVarSetList
  elemVarSet_delVarSet elemVarSet_unionVarSet elemVarSet_minusVarSet
  using solve_varset_inv : hs_simpl.
