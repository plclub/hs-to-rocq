(* Correctness and representation preservation for FV accumulators. *)
Set Warnings "-notation-overridden".
From Coq Require Import Lists.List Bool.Bool.
Require Import Core FV Proofs.Axioms Proofs.VarSetFSet Proofs.Var.
Require Import Proofs.Prelude.
Require Import GHC.Base.
Import GHC.Base.ManualNotations.
Local Ltac solve_varset_inv :=
  match goal with
  | |- VarSetFSet.WF _ => unfold VarSetFSet.WF in *; solve [eauto 6 with varset_invariant]
  | |- IntMapProofs.WF (VarSet_IntMap _) => solve [eauto 6 with varset_invariant]
  | |- ValidVarSet _ => solve [eauto 6 with varset_invariant]
  end.

Local Lemma elemVarSet_eq v w s : (v == w) = true -> elemVarSet v s = elemVarSet w s.
Proof.
  intro E. apply Proofs.Var.eq_unique in E. destruct s as [[m]].
  unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM. now rewrite E.
Qed.
Local Lemma elemVarSet_filterVarSet f s v : WF s -> ValidVarSet s -> RespectsVar f ->
  elemVarSet v (filterVarSet f s) = f v && elemVarSet v s.
Proof.
  intros W V R. rewrite (elemVarSet_lookup _ _ (filterVarSet_WF f s W)),
    (lookupVarSet_filter f s v W), (elemVarSet_lookup s v W).
  destruct (lookupVarSet s v) as [w|] eqn:L.
  - rewrite (R v w (V v w L)). destruct (f w); reflexivity.
  - destruct (f v); reflexivity.
Qed.

Lemma RespectsVar_const_true : RespectsVar (const true).
Proof. intros x y E; reflexivity. Qed.
#[export] Hint Resolve RespectsVar_const_true : core.
Lemma RespectsVar_andb f g : RespectsVar f -> RespectsVar g ->
  RespectsVar (fun v => f v && g v).
Proof. intros F G x y E; rewrite (F x y E), (G x y E); reflexivity. Qed.

(* Membership equality alone does not make insertion into a raw IntMap sound.
   Both the denotation and every input/output accumulator carry evidence.
   Set correctness does not inspect the list; list/set agreement is preserved
   separately when it holds initially. *)
Record Denotes (vs : VarSet) (fv : FV) : Prop := DenotesVarSet {
  Denotes_WF : WF vs;
  Denotes_valid : ValidVarSet vs;
  Denotes_run : forall f scope l acc,
    RespectsVar f -> WF scope -> ValidVarSet scope ->
    WF acc -> ValidVarSet acc ->
    WF (Tuple.snd (fv f scope (l, acc))) /\
    ValidVarSet (Tuple.snd (fv f scope (l, acc))) /\
    forall v, elemVarSet v (Tuple.snd (fv f scope (l, acc))) =
      ((f v && elemVarSet v vs && negb (elemVarSet v scope)) || elemVarSet v acc);
  Denotes_list : forall f scope l acc,
    RespectsVar f -> WF scope -> ValidVarSet scope -> WF acc -> ValidVarSet acc ->
    extendVarSetList emptyVarSet l [=] acc ->
    extendVarSetList emptyVarSet (Tuple.fst (fv f scope (l, acc))) [=]
      Tuple.snd (fv f scope (l, acc))
}.
Arguments Denotes_WF {vs fv} _.
Arguments Denotes_valid {vs fv} _.
Arguments Denotes_run {vs fv} _ f scope l acc _ _ _ _ _.
Arguments Denotes_list {vs fv} _ f scope l acc _ _ _ _ _ _.
Notation "A ⊢ B" := (Denotes A B) (at level 70, no associativity).
Definition WF_fv (fv : FV) : Prop := exists vs, Denotes vs fv.

Lemma equal_members s t : s [=] t -> forall v, elemVarSet v s = elemVarSet v t.
Proof. intros E v. apply Bool.eq_true_iff_eq. apply E. Qed.

(* No Proper instance for raw Equal: the target's evidence is essential. *)
Lemma Denotes_Equal vs1 vs2 fv : WF vs2 -> ValidVarSet vs2 ->
  vs1 [=] vs2 -> Denotes vs1 fv -> Denotes vs2 fv.
Proof.
  intros W V E D. constructor; auto.
  { intros f scope l acc R S T A B.
  destruct (Denotes_run D f scope l acc R S T A B) as [X [Y H]].
  repeat split; auto. intro v. rewrite H, (equal_members _ _ E v). reflexivity. }
  exact (Denotes_list D).
Qed.

Lemma emptyVarSet_emptyFV : Denotes emptyVarSet emptyFV.
Proof.
  constructor; try solve_varset_inv.
  { intros f scope l acc R S T A B. split; [exact A|]. split; [exact B|].
    intro v. simpl. destruct (f v); reflexivity. }
  intros f scope l acc R S T A B E. exact E.
Qed.

Local Lemma elemVarSet_extendVarSetList q s xs : WF s ->
  elemVarSet q (extendVarSetList s xs) =
    existsb (fun x => q == x) xs || elemVarSet q s.
Proof.
  revert s. induction xs as [|x xs IH]; intros s W.
  - reflexivity.
  - rewrite extendVarSetList_cons, IH by (apply extendVarSet_WF; exact W).
    rewrite (elemVarSet_extend_eq s x q W). cbn [existsb].
    destruct (q == x), (existsb (fun x => q == x) xs), (elemVarSet q s); reflexivity.
Qed.

Local Lemma extendVarSetList_cons_equal l x acc : WF acc ->
  extendVarSetList emptyVarSet l [=] acc ->
  extendVarSetList emptyVarSet (x :: l) [=] extendVarSet acc x.
Proof.
  intros W E q. unfold VarSetFSet.In.
  pose proof (equal_members _ _ E q) as L.
  rewrite (elemVarSet_extendVarSetList q emptyVarSet l emptyVarSet_WF),
    elemVarSet_empty, Bool.orb_false_r in L.
  rewrite (elemVarSet_extendVarSetList q emptyVarSet (x :: l) emptyVarSet_WF),
    elemVarSet_empty, Bool.orb_false_r, (elemVarSet_extend_eq acc x q W).
  cbn [existsb]. rewrite L. reflexivity.
Qed.

Lemma unitVarSet_unitFV x : Denotes (unitVarSet x) (unitFV x).
Proof.
  constructor; try solve_varset_inv.
  { intros f scope l acc R S T A B. unfold unitFV.
  destruct (elemVarSet x scope) eqn:XS;
    destruct (elemVarSet x acc) eqn:XA;
    destruct (f x) eqn:FX; cbn [Tuple.snd];
    split; try solve_varset_inv; split; try solve_varset_inv;
    intro v; rewrite elemVarSet_unit;
    try rewrite (elemVarSet_extend_eq acc x v A).
  all: destruct (v == x) eqn:E; simpl.
  all: try (rewrite (elemVarSet_eq v x scope E), XS;
            rewrite ?(elemVarSet_eq v x acc E), ?XA;
            rewrite ?(R v x E), ?FX; reflexivity).
  all: try (rewrite (elemVarSet_eq v x acc E), XA;
            rewrite ?(R v x E), ?FX; destruct (f v), (elemVarSet v scope); reflexivity).
  all: try (rewrite (R v x E), FX; reflexivity).
  all: destruct (f v), (elemVarSet v scope), (elemVarSet v acc); reflexivity. }
  intros f scope l acc R S T A B E. unfold unitFV.
  destruct (elemVarSet x scope); destruct (elemVarSet x acc); destruct (f x);
    cbn [Tuple.fst Tuple.snd]; try exact E.
  apply extendVarSetList_cons_equal; assumption.
Qed.

Lemma filterVarSet_filterFV f vs fv : RespectsVar f ->
  Denotes vs fv -> Denotes (filterVarSet f vs) (filterFV f fv).
Proof.
  intros R D. pose proof (Denotes_WF D) as W. pose proof (Denotes_valid D) as V.
  constructor; try solve_varset_inv.
  { intros g scope l acc G S T A B.
  destruct (Denotes_run D (fun v => g v && f v) scope l acc
    (RespectsVar_andb _ _ G R) S T A B) as [X [Y H]].
  split; [exact X|]. split; [exact Y|]. intro v.
  rewrite H, (elemVarSet_filterVarSet f vs v) by assumption.
  destruct (g v), (f v), (elemVarSet v vs), (elemVarSet v scope); reflexivity. }
  intros g scope l acc G S T A B E.
  apply (Denotes_list D (fun v => g v && f v) scope l acc
    (RespectsVar_andb _ _ G R) S T A B E).
Qed.

Lemma delVarSet_delFV vs v fv : Denotes vs fv -> Denotes (delVarSet vs v) (delFV v fv).
Proof.
  intro D. pose proof (Denotes_WF D) as W. pose proof (Denotes_valid D) as V.
  constructor; try solve_varset_inv.
  { intros f scope l acc R S T A B.
  destruct (Denotes_run D f (extendVarSet scope v) l acc R
    ltac:(solve_varset_inv) ltac:(solve_varset_inv) A B) as [X [Y H]].
  split; [exact X|]. split; [exact Y|]. intro q. unfold delFV. rewrite H.
  rewrite (elemVarSet_extend_eq scope v q S), (elemVarSet_del vs v q W), <- Var_eq_key.
  destruct (q == v), (f q), (elemVarSet q vs), (elemVarSet q scope); reflexivity. }
  intros f scope l acc R S T A B E.
  apply (Denotes_list D f (extendVarSet scope v) l acc R
    ltac:(solve_varset_inv) ltac:(solve_varset_inv) A B E).
Qed.

Lemma unionVarSet_unionFV vs vs' fv fv' :
  Denotes vs fv -> Denotes vs' fv' -> Denotes (unionVarSet vs vs') (unionFV fv' fv).
Proof.
  intros D E. pose proof (Denotes_WF D) as W. pose proof (Denotes_valid D) as V.
  pose proof (Denotes_WF E) as W'. pose proof (Denotes_valid E) as V'.
  constructor; try solve_varset_inv.
  { intros f scope l acc R S T A B.
  destruct (Denotes_run D f scope l acc R S T A B) as [X [Y H]].
  destruct (fv f scope (l, acc)) as [ls mid] eqn:M. simpl in X,Y,H.
  destruct (Denotes_run E f scope ls mid R S T X Y) as [X' [Y' H']].
  unfold unionFV. rewrite M. split; [exact X'|]. split; [exact Y'|].
  intro q. rewrite H', H, (elemVarSet_union vs vs' q W W').
  destruct (f q), (elemVarSet q vs), (elemVarSet q vs'),
    (elemVarSet q scope), (elemVarSet q acc); reflexivity. }
  intros f scope l acc R S T A B L.
  destruct (Denotes_run D f scope l acc R S T A B) as [X [Y H]].
  pose proof (Denotes_list D f scope l acc R S T A B L) as M.
  destruct (fv f scope (l, acc)) as [ls mid] eqn:F.
  cbn [Tuple.fst Tuple.snd] in X,Y,M.
  unfold unionFV. rewrite F. exact (Denotes_list E f scope ls mid R S T X Y M).
Qed.

Lemma empty_FV_WF : WF_fv emptyFV.
Proof. exists emptyVarSet; apply emptyVarSet_emptyFV. Qed.
Lemma unit_FV_WF x : WF_fv (unitFV x).
Proof. exists (unitVarSet x); apply unitVarSet_unitFV. Qed.
Lemma filter_FV_WF f fv : RespectsVar f -> WF_fv fv -> WF_fv (filterFV f fv).
Proof. intros R [vs D]. exists (filterVarSet f vs); apply filterVarSet_filterFV; assumption. Qed.
Lemma del_FV_WF fv v : WF_fv fv -> WF_fv (delFV v fv).
Proof. intros [vs D]. exists (delVarSet vs v); apply delVarSet_delFV; assumption. Qed.
Lemma union_FV_WF fv fv' : WF_fv fv -> WF_fv fv' -> WF_fv (unionFV fv fv').
Proof. intros [vs D] [vs' E]. exists (unionVarSet vs' vs); apply unionVarSet_unionFV; assumption. Qed.

Lemma mapUnionFV_nil A f : mapUnionFV f (nil : list A) = emptyFV.
Proof. reflexivity. Qed.
Lemma mapUnionFV_cons A f (x : A) xs :
  mapUnionFV f (x :: xs) = unionFV (mapUnionFV f xs) (f x).
Proof. reflexivity. Qed.
#[export] Hint Rewrite mapUnionFV_nil mapUnionFV_cons : hs_simpl.

Lemma map_union_FV_WF A f (ls : list A) :
  (forall e, List.In e ls -> WF_fv (f e)) -> WF_fv (mapUnionFV f ls).
Proof.
  induction ls as [|x xs IH]; intro H.
  - apply empty_FV_WF.
  - rewrite mapUnionFV_cons. apply union_FV_WF.
    + apply IH. intros e I; apply H; right; exact I.
    + apply H; left; reflexivity.
Qed.
Lemma unions_FV_WF fvs : (forall fv, List.In fv fvs -> WF_fv fv) -> WF_fv (unionsFV fvs).
Proof. apply map_union_FV_WF. Qed.
Lemma mkFVs_FV_WF vs : WF_fv (mkFVs vs).
Proof. apply map_union_FV_WF; intros; apply unit_FV_WF. Qed.
#[export] Hint Resolve unit_FV_WF empty_FV_WF union_FV_WF unions_FV_WF del_FV_WF mkFVs_FV_WF : core.

Lemma union_empty_l fv : unionFV emptyFV fv = fv.
Proof. reflexivity. Qed.
Lemma union_empty_r fv : unionFV fv emptyFV = fv.
Proof. reflexivity. Qed.

Lemma fvVarSet_WF fv : WF_fv fv -> WF (fvVarSet fv).
Proof.
  intros [vs D]. exact (proj1 (Denotes_run D (const true) emptyVarSet nil emptyVarSet
    RespectsVar_const_true emptyVarSet_WF emptyVarSet_valid emptyVarSet_WF emptyVarSet_valid)).
Qed.
Lemma fvVarSet_valid fv : WF_fv fv -> ValidVarSet (fvVarSet fv).
Proof.
  intros [vs D]. exact (proj1 (proj2 (Denotes_run D (const true) emptyVarSet nil emptyVarSet
    RespectsVar_const_true emptyVarSet_WF emptyVarSet_valid emptyVarSet_WF emptyVarSet_valid))).
Qed.
Lemma DenotesfvVarSet vs fv : Denotes vs fv -> fvVarSet fv [=] vs.
Proof.
  intro D. destruct (Denotes_run D (const true) emptyVarSet nil emptyVarSet
    RespectsVar_const_true emptyVarSet_WF emptyVarSet_valid emptyVarSet_WF emptyVarSet_valid)
    as [_ [_ H]]. intro v.
  change (elemVarSet v (Tuple.snd (fv (const true) emptyVarSet (nil, emptyVarSet))) = true <-> elemVarSet v vs = true).
  rewrite H, !elemVarSet_empty. simpl. rewrite Bool.andb_true_r, Bool.orb_false_r. reflexivity.
Qed.
Lemma Denotes_inj1 vs1 vs2 fv : Denotes vs1 fv -> Denotes vs2 fv -> vs1 [=] vs2.
Proof.
  intros D E v. unfold VarSetFSet.In. rewrite <- (equal_members _ _ (DenotesfvVarSet _ _ D) v),
    (equal_members _ _ (DenotesfvVarSet _ _ E) v). reflexivity.
Qed.

Lemma Denotes_fvVarSet m fv f scope l acc : Denotes m fv ->
  RespectsVar f -> WF scope -> ValidVarSet scope -> WF acc -> ValidVarSet acc ->
  Tuple.snd (fv f scope (l, acc)) [=]
    unionVarSet (minusVarSet (filterVarSet f m) scope) acc.
Proof.
  intros D R S T A B. pose proof (Denotes_WF D) as W. pose proof (Denotes_valid D) as V.
  destruct (Denotes_run D f scope l acc R S T A B) as [_ [_ H]].
  intro v. unfold VarSetFSet.In. rewrite H.
  rewrite elemVarSet_union, elemVarSet_minus, elemVarSet_filterVarSet by (try assumption; solve_varset_inv).
  destruct (f v), (elemVarSet v m), (elemVarSet v scope), (elemVarSet v acc); reflexivity.
Qed.

Lemma delVarSet_fvVarSet fv x : WF_fv fv ->
  delVarSet (fvVarSet fv) x [=] fvVarSet (delFV x fv).
Proof.
  intros [vs D] v. unfold VarSetFSet.In.
  pose proof (fvVarSet_WF fv (ex_intro _ vs D)) as W.
  rewrite (elemVarSet_del _ _ _ W),
    (equal_members _ _ (DenotesfvVarSet _ _ (delVarSet_delFV _ x _ D)) v),
    (elemVarSet_del _ _ _ (Denotes_WF D)),
    (equal_members _ _ (DenotesfvVarSet _ _ D) v). reflexivity.
Qed.

Lemma mapUnionVarSet_mapUnionFV A (ps : list A) (f1 : A -> VarSet) (f2 : A -> FV) :
  Forall2 Denotes (map f1 ps) (map f2 ps) -> Denotes (mapUnionVarSet f1 ps) (mapUnionFV f2 ps).
Proof.
  induction ps as [|p ps IH]; intro H.
  - apply emptyVarSet_emptyFV.
  - inversion H; subst. change (Denotes (unionVarSet (f1 p) (mapUnionVarSet f1 ps))
      (unionFV (mapUnionFV f2 ps) (f2 p))).
    apply unionVarSet_unionFV; auto.
Qed.
Lemma unionsFV_cons fv fvs : unionsFV (fv :: fvs) = unionFV (unionsFV fvs) fv.
Proof. reflexivity. Qed.
Lemma unionsVarSet_unionsFV vss fvs : Forall2 Denotes vss fvs ->
  Denotes (Foldable.foldr unionVarSet emptyVarSet vss) (unionsFV fvs).
Proof.
  intro H; induction H.
  - apply emptyVarSet_emptyFV.
  - change (Denotes (unionVarSet x (Foldable.foldr unionVarSet emptyVarSet l))
      (unionFV (unionsFV l') y)). apply unionVarSet_unionFV; assumption.
Qed.

Print Assumptions unitVarSet_unitFV.
Print Assumptions fvVarSet_WF.
Print Assumptions fvVarSet_valid.

Lemma mapUnionFV_map A B (f : B -> FV) (g : A -> B) xs :
  mapUnionFV f (map g xs) = mapUnionFV (fun x => f (g x)) xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (unionFV (mapUnionFV f (map g xs)) (f (g x)) =
    unionFV (mapUnionFV (fun x => f (g x)) xs) (f (g x))).
  rewrite IH. reflexivity.
Qed.

Lemma delFV_mapUnionFV A v (f : A -> FV) xs :
  delFV v (mapUnionFV f xs) = mapUnionFV (fun x => delFV v (f x)) xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (unionFV (delFV v (mapUnionFV f xs)) (delFV v (f x)) =
    unionFV (mapUnionFV (fun x => delFV v (f x)) xs) (delFV v (f x))).
  rewrite IH. reflexivity.
Qed.

Lemma fvVarSet_Denotes fv : WF_fv fv -> Denotes (fvVarSet fv) fv.
Proof.
  intros [vs D]. apply (Denotes_Equal vs (fvVarSet fv) fv).
  - apply fvVarSet_WF; exists vs; exact D.
  - apply fvVarSet_valid; exists vs; exact D.
  - intro v; symmetry; apply (DenotesfvVarSet _ _ D).
  - exact D.
Qed.

Lemma fvVarSet_unionFV fv fv' : WF_fv fv -> WF_fv fv' ->
  fvVarSet (unionFV fv fv') [=] unionVarSet (fvVarSet fv) (fvVarSet fv').
Proof.
  intros H K v. unfold VarSetFSet.In.
  pose proof (unionVarSet_unionFV _ _ _ _ (fvVarSet_Denotes _ K) (fvVarSet_Denotes _ H)) as D.
  rewrite (equal_members _ _ (DenotesfvVarSet _ _ D) v),
    !elemVarSet_union by (apply fvVarSet_WF; assumption).
  rewrite Bool.orb_comm. reflexivity.
Qed.

Lemma fvVarSet_filterFV f fv : RespectsVar f -> WF_fv fv ->
  fvVarSet (filterFV f fv) [=] filterVarSet f (fvVarSet fv).
Proof.
  intros R H. apply DenotesfvVarSet, filterVarSet_filterFV; [exact R|].
  apply fvVarSet_Denotes; exact H.
Qed.

Lemma unionVarSet_unionFV_forward vs vs' fv fv' : Denotes vs fv -> Denotes vs' fv' ->
  Denotes (unionVarSet vs vs') (unionFV fv fv').
Proof.
  intros D E. eapply Denotes_Equal with (vs1 := unionVarSet vs' vs).
  - apply unionVarSet_WF; [exact (Denotes_WF D)|exact (Denotes_WF E)].
  - apply unionVarSet_valid; [exact (Denotes_WF D)|exact (Denotes_WF E)|exact (Denotes_valid D)|exact (Denotes_valid E)].
  - intro v. unfold VarSetFSet.In. rewrite !elemVarSet_union by (exact (Denotes_WF D) || exact (Denotes_WF E)).
    rewrite Bool.orb_comm. reflexivity.
  - apply unionVarSet_unionFV; [exact E|exact D].
Qed.

Lemma fvVarSet_mapUnionFV A f (xs : list A) :
  (forall x, List.In x xs -> WF_fv (f x)) ->
  fvVarSet (mapUnionFV f xs) [=] mapUnionVarSet (fun x => fvVarSet (f x)) xs.
Proof.
  intro H. apply DenotesfvVarSet, mapUnionVarSet_mapUnionFV.
  induction xs as [|x xs IH]; simpl; constructor.
  - apply fvVarSet_Denotes, H; left; reflexivity.
  - apply IH. intros y I; apply H; right; exact I.
Qed.
