(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Psatz.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import SetoidList.
Require Import Coq.Logic.ProofIrrelevance.

Require Import GHC.Base.

Require Import Proofs.Prelude.

Require Import CoreFVs.
Require Import Id.
Require Import Core.
Require UniqFM.

Require Import Proofs.Base.
Require Import Proofs.Axioms.
Require Import Proofs.ContainerProofs.
Require Import Proofs.GhcTactics.
Require Import Proofs.Unique.
Require Import Proofs.Var.
Require Import Proofs.VarSetFSet.
Require Import Proofs.VarSet.

Open Scope Z_scope.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

#[local] Hint Resolve emptyVarSet_WF unitVarSet_WF mkVarSet_WF
  extendVarSet_WF extendVarSetList_WF delVarSet_WF delVarSetList_WF
  filterVarSet_WF emptyVarSet_valid unitVarSet_valid mkVarSet_valid
  extendVarSet_valid extendVarSetList_valid delVarSet_valid delVarSetList_valid
  filterVarSet_valid : core.

(** ** [StrongSubset] *)


(* A strong subset doesn't just have a subset of the uniques, but 
     also requires that the variables in common be almostEqual. *)
Definition StrongSubset (vs1 : VarSet) (vs2: VarSet) := 
  forall var, match lookupVarSet vs1 var with 
           | Some v =>  match lookupVarSet vs2 var with
                          | Some v' => almostEqual v v'
                          | None => False
                       end
           | None => True 
         end.


Notation "s1 {<=} s2" := (StrongSubset s1 s2) (at level 70, no associativity).
Definition StrongEquivalence s1 s2 := (StrongSubset s1 s2 /\ StrongSubset s2 s1).
Notation "s1 {=} s2" := (StrongEquivalence s1 s2)  (at level 70, no associativity).


Lemma StrongSubset_refl : forall vs, 
    StrongSubset vs vs.
Proof.
  unfold StrongSubset.
  move=> vs var.
  elim h: (lookupVarSet vs var) => //.
  eapply almostEqual_refl.
Qed.

Instance StrongSubset_Reflexive : Reflexive StrongSubset := StrongSubset_refl.

Lemma StrongSubset_trans : forall vs1 vs2 vs3, 
    StrongSubset vs1 vs2 -> StrongSubset vs2 vs3 -> StrongSubset vs1 vs3.
Proof.
  move => vs1 vs2 vs3 h1 h2 var.
  specialize (h1 var).
  specialize (h2 var).
  move: h1 h2.
  elim p1: (lookupVarSet vs1 var) => //;
  elim p2: (lookupVarSet vs2 var) => //;
  elim p3: (lookupVarSet vs3 var) => //.
  eapply almostEqual_trans.
Qed.


Instance StrongSubset_Transitive : Transitive StrongSubset := StrongSubset_trans.

Instance StrongSubset_Equivalence : Equivalence StrongEquivalence.
Proof.
  split; unfold Reflexive, Symmetric, Transitive, StrongEquivalence.
  - intros. split; reflexivity.
  - move=> x y [h1 h2]. eauto.
  - move=> x y z [h1 h2] [h3 h4].
    eauto using StrongSubset_trans.
Defined.  

Lemma StrongSubset_implies_Subset :
  forall vs1 vs2 , WF vs1 -> WF vs2 -> vs1 {<=} vs2 -> vs1 [<=] vs2.
Proof. 
  intros vs1 vs2.
  unfold StrongSubset, Subset.
   intros W1 W2 SS var IN.
  unfold In in *.
  specialize (SS var). 
  destruct (lookupVarSet vs1 var) eqn:VS1;
  destruct (lookupVarSet vs2 var) eqn:VS2; try contradiction.
  - eapply lookupVarSet_elemVarSet; eauto.
  - apply elemVarSet_lookupVarSet in IN. destruct IN.
    rewrite VS1 in H. discriminate.
  - apply elemVarSet_lookupVarSet in IN. destruct IN.
    rewrite VS1 in H. discriminate.
Qed.

Lemma StrongEquivalence_implies_Equal :
  forall vs1 vs2 , WF vs1 -> WF vs2 -> vs1 {=} vs2 -> vs1 [=] vs2.
Proof. 
  intros vs1 vs2 W1 W2 [S1 S2].
  eapply subset_antisym;
  eauto using StrongSubset_implies_Subset.
Qed.

Lemma StrongSubset_extend_fresh :
  forall vs v, WF vs -> lookupVarSet vs v = None -> vs {<=} (extendVarSet vs v).
Proof.
  intros vs v W H.
  unfold StrongSubset.
  intros var.
  destruct (var == v) eqn:EQV.
  rewrite -> lookupVarSet_eq with (v2 := v); auto.
  rewrite H. auto.
  destruct (lookupVarSet vs var) eqn:Lvar; auto.
  rewrite lookupVarSet_extendVarSet_neq; [|exact W|].
  rewrite Lvar.
  apply almostEqual_refl.
  unfold CoreBndr in *. intro h. rewrite Base.Eq_sym in h. rewrite h in EQV. discriminate.
Qed.


Lemma StrongSubset_extendList_fresh :
  forall vs vs2,
  WF vs ->
  disjointVarSet vs (mkVarSet vs2) -> vs {<=} (extendVarSetList vs vs2).
Proof.
  intros vs vs2 W D v.
  destruct (lookupVarSet vs v) as [w|] eqn:L; [|exact I].
  assert (M : elemVarSet v vs = true) by (eapply lookupVarSet_elemVarSet; eauto).
  assert (N : elemVarSet v (mkVarSet vs2) = false).
  { pose proof (mkVarSet_WF vs2) as X.
    destruct vs as [[m]], (mkVarSet vs2) as [[n]].
    exact (proj1 (ContainerProofs.disjoint_spec _ _ _ _ W X) D
      (Unique.getWordKey (Unique.getUnique v)) M). }
  rewrite lookupVarSet_extendVarSetList_l; [|exact W|rewrite N; reflexivity].
  rewrite L. apply almostEqual_refl.
Qed.


Lemma StrongSubset_extend_ae :
  forall vs1 vs2 v1 v2,
  WF vs1 -> WF vs2 ->
  vs1 {<=} vs2 -> almostEqual v1 v2 ->  (extendVarSet vs1 v1) {<=} (extendVarSet vs2 v2).
Proof.
  intros vs1 vs2 v1 v2 W1 W2 S E var.
  pose proof E as Ev. apply almostEqual_eq in Ev.
  assert (Evq : (v1 == var) = (v2 == var)).
  { apply Var.eq_m; [exact Ev|apply Eq_refl]. }
  destruct (v1 == var) eqn:EQv.
  - rewrite lookupVarSet_extendVarSet_eq; [|exact W1|exact EQv].
    rewrite lookupVarSet_extendVarSet_eq; [exact E|exact W2|].
    rewrite <- Evq. reflexivity.
  - rewrite lookupVarSet_extendVarSet_neq; [|exact W1|rewrite EQv; discriminate].
    rewrite lookupVarSet_extendVarSet_neq; [apply S|exact W2|].
    rewrite <- Evq. discriminate.
Qed.

Lemma extendVarSet_ae_m : forall x1 y1, WF x1 -> WF y1 ->
  x1 {<=} y1 -> forall x2 y2, almostEqual x2 y2 ->
  extendVarSet x1 x2 {<=} extendVarSet y1 y2.
Proof. intros; eapply StrongSubset_extend_ae; eauto. Qed.


Lemma StrongSubset_extend :
  forall vs1 vs2 v,
  WF vs1 -> WF vs2 ->
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSet vs1 v) (extendVarSet vs2 v).
Proof.
  intros.
  apply StrongSubset_extend_ae.
   all: auto using almostEqual_refl.
Qed.

Lemma StrongSubset_extendVarSetList_ae :
  forall l1 l2 vs1 vs2,
  WF vs1 -> WF vs2 ->
  Forall2 almostEqual l1 l2 ->
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSetList vs1 l1) (extendVarSetList vs2 l2).
Proof.
  intros l1 l2 vs1 vs2 W1 W2 H H0.
  revert vs1 vs2 W1 W2 H0. induction H; intros.
  * apply H0.
   * rewrite !extendVarSetList_cons.
    apply IHForall2.
    all: unfold VarSetFSet.WF in *; eauto using extendVarSet_WF, StrongSubset_extend_ae.
Qed.

Lemma extendVarSetList_ae_m : forall x1 y1, WF x1 -> WF y1 ->
  x1 {<=} y1 -> forall x2 y2, Forall2 almostEqual x2 y2 ->
  extendVarSetList x1 x2 {<=} extendVarSetList y1 y2.
Proof. intros; eapply StrongSubset_extendVarSetList_ae; eauto. Qed.



Lemma StrongSubset_extendVarSetList :
  forall l vs1 vs2,
  WF vs1 -> WF vs2 ->
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSetList vs1 l) (extendVarSetList vs2 l).
Proof.
  intros.
  apply StrongSubset_extendVarSetList_ae; try assumption.
  apply Forall2_diag.
  rewrite Forall_forall. intros. apply almostEqual_refl.
Qed.

Lemma StrongSubset_delVarSet :
  forall vs1 vs2 v,
  WF vs1 -> WF vs2 ->
  StrongSubset vs1 vs2 ->
  StrongSubset (delVarSet vs1 v) (delVarSet vs2 v).
Proof.
  intros vs1 vs2 v W1 W2 H.
  unfold StrongSubset in *.
  intro var.
  specialize (H var).
  destruct (v == var) eqn:EQv.
  - rewrite Base.Eq_sym in EQv.
     erewrite lookupVarSet_eq;
       [|eassumption].
    rewrite lookupVarSet_delVarSet_None; [trivial|exact W1].
  - rewrite lookupVarSet_delVarSet_neq;
       [|exact W1|rewrite EQv; auto].
    destruct (lookupVarSet vs1 var) eqn:Hl; auto.
    rewrite lookupVarSet_delVarSet_neq;
       [|exact W2|rewrite EQv; auto].
    auto.
Qed.


Lemma delVarSet_ae_m : forall x1 y1, WF x1 -> WF y1 ->
  x1 {<=} y1 -> forall x2 y2, almostEqual x2 y2 ->
  delVarSet x1 x2 {<=} delVarSet y1 y2.
Proof.
  move=> x1 y1 W1 W2 E1 x2 y2 E2.
  unfold StrongSubset in *.
  move=>var. specialize (E1 var).
  destruct (x2 == var) eqn:EQv.
  - rewrite Base.Eq_sym in EQv.
    erewrite lookupVarSet_eq;
      [|eassumption].
    rewrite lookupVarSet_delVarSet_None; [trivial|exact W1].
  - rewrite lookupVarSet_delVarSet_neq;
      [|exact W1|rewrite EQv; auto].
    destruct (lookupVarSet x1 var) eqn:Hl; auto.
    pose proof E2 as E. apply almostEqual_eq in E.
    assert (K : (x2 == var) = (y2 == var)).
    { apply Var.eq_m; [exact E|apply Eq_refl]. }
    rewrite K in EQv.
    rewrite lookupVarSet_delVarSet_neq;
      [|exact W2|rewrite EQv; auto].
    auto.
Qed.  


Lemma StrongSubset_delete_fresh :
  forall vs v,
  WF vs ->
  lookupVarSet vs v = None ->
  StrongSubset vs (delVarSet vs v).
Proof.
  intros vs v W H.
  unfold StrongSubset in *.
  intro var.
  destruct (v == var) eqn:EQv.
  - rewrite Base.Eq_sym in EQv.
    erewrite lookupVarSet_eq;
      [|eassumption].
    rewrite H.
    trivial.
  - rewrite lookupVarSet_delVarSet_neq;
      [|exact W|rewrite EQv; auto].
    destruct (lookupVarSet vs var) eqn:Hl; auto.
    apply almostEqual_refl.
Qed.

Lemma StrongSubset_delVarSetList:
  forall vs1 vs2 vs,
  WF vs1 -> WF vs2 ->
  StrongSubset vs1 vs2 ->
  StrongSubset (delVarSetList vs1 vs) (delVarSetList vs2 vs).
Proof.
  intros vs1 vs2 vs.
  generalize dependent vs2.
  generalize dependent vs1.
  induction vs;
      intros vs1 vs2 W1 W2 H; hs_simpl;
      [assumption|].
  eapply IHvs; unfold VarSetFSet.WF in *; eauto using delVarSet_WF, StrongSubset_delVarSet.
Qed.

Lemma delVarSetList_ae_m : forall vs1 vs2, WF vs1 -> WF vs2 ->
  vs1 {<=} vs2 -> forall xs1 xs2, Forall2 almostEqual xs1 xs2 ->
  delVarSetList vs1 xs1 {<=} delVarSetList vs2 xs2.
Proof.
  move=> vs1 vs2 W1 W2 E1 xs1 xs2 E2.
  revert W1 W2 E1.
  generalize dependent vs2.
  generalize dependent vs1.
  induction E2;
    move=> vs1 vs2 W1 W2 SS; hs_simpl; [assumption|].
  eapply IHE2.
  all: unfold VarSetFSet.WF in *; eauto using delVarSet_WF, delVarSet_ae_m.
Qed.  

(* Respects_StrongSubset *)

Definition Respects_StrongSubset (P : VarSet -> Prop) : Prop :=
  forall (vs1 vs2 : VarSet),
  WF vs1 -> WF vs2 ->
  vs1 {<=} vs2 -> P vs1 -> P vs2.
Existing Class Respects_StrongSubset.

Require Import Coq.Classes.Morphisms.
Global Instance Respects_StrongSubset_iff_morphism:
  Proper (pointwise_relation VarSet iff ==> iff) Respects_StrongSubset.
Proof.
  intros P Q E. split; intros R s t W X S HP.
  - apply (proj1 (E t)). apply (R s t W X S).
    apply (proj2 (E s)). exact HP.
  - apply (proj2 (E t)). apply (R s t W X S).
    apply (proj1 (E s)). exact HP.
Qed.

Lemma Respects_StrongSubset_const:
  forall P, Respects_StrongSubset (fun _ => P).
Proof. unfold Respects_StrongSubset; auto. Qed.

Lemma Respects_StrongSubset_and:
  forall P Q,
    Respects_StrongSubset P ->
    Respects_StrongSubset Q ->
    Respects_StrongSubset (fun x => P x /\ Q x).
Proof.
  intros P Q RP RQ s t W X S [HP HQ].
  split; [exact (RP s t W X S HP)|exact (RQ s t W X S HQ)].
Qed.

Lemma Respects_StrongSubset_andb:
  forall (P Q : VarSet -> bool),
    Respects_StrongSubset (fun x => P x = true) ->
    Respects_StrongSubset (fun x => Q x = true) ->
    Respects_StrongSubset (fun x => P x && Q x = true).
Proof.
  intros P Q RP RQ s t W X S H.
  apply Bool.andb_true_iff in H as [HP HQ].
  apply Bool.andb_true_iff. split.
  - exact (RP s t W X S HP).
  - exact (RQ s t W X S HQ).
Qed.


Lemma Respects_StrongSubset_forall:
  forall a (xs : list a) P,
    Forall (fun x => Respects_StrongSubset (fun vs => P vs x)) xs ->
    Respects_StrongSubset (fun vs => Forall (P vs) xs).
Proof.
  intros a xs P R s t W X S H.
  rewrite -> Forall_forall in R, H |- *.
  intros x M. exact (R x M s t W X S (H x M)).
Qed.

Lemma Respects_StrongSubset_forallb:
  forall a (xs : list a) P,
    Forall (fun x => Respects_StrongSubset (fun vs => P vs x = true)) xs ->
    Respects_StrongSubset (fun vs => forallb (P vs) xs = true).
Proof.
  intros a xs P R s t W X S H.
  rewrite -> forallb_forall in H |- *.
  rewrite -> Forall_forall in R.
  intros x M. exact (R x M s t W X S (H x M)).
Qed.


Lemma Respects_StrongSubset_elemVarSet:
  forall v,
  Respects_StrongSubset (fun vs => elemVarSet v vs = true).
Proof.
  intros v s t Ws Wt H Hs.
  eapply (StrongSubset_implies_Subset Ws Wt H). exact Hs.
Qed.

Lemma Respects_StrongSubset_delVarSet:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (delVarSet vs v)).
Proof.
  intros v P H vs1 vs2 W1 W2 Hs Hvs1.
  apply StrongSubset_delVarSet with (v:=v) in Hs; try assumption.
  unfold Respects_StrongSubset in H.  
  apply (H (delVarSet vs1 v) (delVarSet vs2 v)); try assumption; solve_varset_inv.
Qed.

Lemma Respects_StrongSubset_delVarSetList:
  forall vs2 P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (delVarSetList vs vs2)).
Proof.
  intros vs2 P H vs vs' W1 W2 Hs Hvs2.
  apply StrongSubset_delVarSetList with (vs:=vs2) in Hs; try assumption.
  unfold Respects_StrongSubset in H.  
  apply (H (delVarSetList vs vs2) (delVarSetList vs' vs2)); try assumption; solve_varset_inv.
Qed.


Lemma Respects_StrongSubset_extendVarSet:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (extendVarSet vs v)).
Proof.
  intros v P H vs vs' W1 W2 Hs Hvs.
  apply StrongSubset_extend with (v:=v) in Hs; try assumption.
  unfold Respects_StrongSubset in H.
  apply (H (extendVarSet vs v) (extendVarSet vs' v)); try assumption; solve_varset_inv.
Qed.


Lemma Respects_StrongSubset_extendVarSetList:
  forall vs' P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (extendVarSetList vs vs')).
Proof.
  intros vs P H vs1 vs2 W1 W2 Hs Hvs1.
  eapply StrongSubset_extendVarSetList with (l:=vs) in Hs; try assumption.
  unfold Respects_StrongSubset in H.
  apply (H (extendVarSetList vs1 vs) (extendVarSetList vs2 vs)); try assumption; solve_varset_inv.
Qed. 

Lemma StrongSubset_filterVarSet: 
  forall f1 f2 vs,
     WF vs -> ValidVarSet vs ->
    RespectsVar f1 -> RespectsVar f2 ->
  (forall v, f1 v = true  -> f2 v = true) ->
  filterVarSet f1 vs {<=} filterVarSet f2 vs.
Proof.
  intros.
  unfold StrongSubset.
  intros var.
  destruct (f1 var) eqn:Heq1.
  - rewrite lookupVarSet_filterVarSet_true; auto.
    destruct (lookupVarSet vs var) eqn:Hl; [|trivial].
    rewrite lookupVarSet_filterVarSet_true; auto.
    rewrite Hl.
    apply almostEqual_refl.
  - rewrite lookupVarSet_filterVarSet_false; auto.
Qed.

(* Is this weakening? *)
Lemma weaken:
  forall {P : VarSet -> Prop} {R : Respects_StrongSubset P},
  forall {vs1} {vs2},
  WF vs1 -> WF vs2 ->
  StrongSubset vs1 vs2 ->
  P vs1 -> P vs2.
Proof. intros P R vs1 vs2 W X S H. exact (R vs1 vs2 W X S H). Qed.

Lemma weakenb:
  forall {P : VarSet -> bool} {R : Respects_StrongSubset (fun x => P x )},
  forall {vs1} {vs2},
  WF vs1 -> WF vs2 ->
  StrongSubset vs1 vs2 ->
  P vs1  -> P vs2 .
Proof. intros P R vs1 vs2 W X S H. exact (R vs1 vs2 W X S H). Qed.

Lemma Respects_StrongSubset_extendVarSet_ae:
  forall {P : VarSet -> Prop} {R : Respects_StrongSubset P},
  forall vs v1 v2,
  WF vs ->
  almostEqual v1 v2 ->
  P (extendVarSet vs v1) <-> P (extendVarSet vs v2).
Proof.
  intros P R vs v1 v2 W E.
  split; intro HP.
  - apply (R (extendVarSet vs v1) (extendVarSet vs v2)); try exact HP;
      try solve [solve_varset_inv].
    apply StrongSubset_extend_ae; auto using StrongSubset_refl.
  - apply (R (extendVarSet vs v2) (extendVarSet vs v1)); try exact HP;
      try solve [solve_varset_inv].
    apply StrongSubset_extend_ae; auto using StrongSubset_refl, almostEqual_sym.
Qed.


Lemma Respects_StrongSubset_extendVarSetList_ae:
  forall {P : VarSet -> Prop} {R : Respects_StrongSubset P},
  forall vs vs1 vs2,
  WF vs ->
  Forall2 almostEqual vs1 vs2 ->
  P (extendVarSetList vs vs1) <-> P (extendVarSetList vs vs2).
Proof.
  intros P R vs vs1 vs2 W H.
  assert (Forall2 almostEqual vs2 vs1) as Hrev.
  { induction H; constructor; auto using almostEqual_sym. }
  split; intro HP.
  - apply (R (extendVarSetList vs vs1) (extendVarSetList vs vs2)); try exact HP;
      try solve [solve_varset_inv].
    apply StrongSubset_extendVarSetList_ae; auto using StrongSubset_refl.
  - apply (R (extendVarSetList vs vs2) (extendVarSetList vs vs1)); try exact HP;
      try solve [solve_varset_inv].
    apply StrongSubset_extendVarSetList_ae; auto using StrongSubset_refl.
Qed.

Lemma StrongSubset_extendVarSet_fresh : 
  forall vs var, WF vs -> lookupVarSet vs var = None ->
            StrongSubset vs (extendVarSet vs var).
Proof.
  apply StrongSubset_extend_fresh.
Qed.

Lemma StrongSubset_extendVarSetList_fresh :
  forall vs vars, WF vs -> freshList vars vs ->
             StrongSubset vs (extendVarSetList vs vars).
Proof.
  intros vs vars W H.
  intro v. destruct (Foldable.elem v vars) eqn:M.
  - rewrite (H v M). exact I.
  - rewrite lookupVarSet_extendVarSetList_false; [|exact W|rewrite M; reflexivity].
    destruct (lookupVarSet vs v); auto using almostEqual_refl.
Qed.

(* Audit the evidence-premised operation and monotonicity interfaces. *)
Print Assumptions StrongSubset_extend_ae.
Print Assumptions StrongSubset_extendList_fresh.
Print Assumptions StrongSubset_delVarSetList.
Print Assumptions Respects_StrongSubset_extendVarSetList.
Print Assumptions StrongSubset_filterVarSet.
