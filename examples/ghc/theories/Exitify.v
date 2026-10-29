Require Import GHC.Base.
Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.

Require Import Proofs.Prelude.

Require Import Psatz.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.NArith.BinNat.
Require Import Coq.Program.Equality. (* for dependent destruction *)
 
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Proofs.Axioms.
Require Import Proofs.Base.
Require Import Proofs.JoinPointInvariants.
Require Import Proofs.ScopeInvariant.
Require Import Proofs.StateLogic.
Require Import Proofs.CoreInduct.
Require Import Proofs.Forall.
Require Import Proofs.Core.
Require Import Proofs.CoreFVs.
Require Import Proofs.GhcTactics.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetStrong.
Require Import Proofs.VarEnv.
Require Import Proofs.Unique.
Require Import Proofs.GhcUtils.
Require Import Proofs.Util.

Set Bullet Behavior "Strict Subproofs".
Opaque Base.hs_string__.
Close Scope Z_scope.

(** * Proofs about the Exitification pass *)

Lemma etaUnique: forall u, Unique.MkUnique (Unique.getKey u) = u.
Proof. intro u. destruct u. simpl. auto. Qed.

(* GHC 9.10: initExitJoinUnique moved to GHC.Builtin.Uniques (not translated) *)
Lemma isLocalId_mkLocalId : forall u s w ty,
  Unique.isLocalUnique u = true ->
  is_true
    (isLocalId
       (mkLocalId (Name.mkSystemVarName u s) w ty)).
Proof.
  intros u s w ty Hlocal.
  unfold mkLocalId, Id.mkLocalIdWithInfo, mkLocalVar, mk_id.
  unfold isLocalId.
  unfold Name.mkSystemVarName, Name.mkSystemName, Name.mkSystemNameAt.
  simpl. exact Hlocal.
Qed.        

Lemma idJoinPointHood_isJoinId_maybe v :
  idJoinPointHood v =
  match isJoinId_maybe v with
  | Some n => Outputable.JoinPoint n
  | None => Outputable.NotJoinPoint
  end.
Proof.
  destruct v; unfold idJoinPointHood, isJoinId_maybe, isId, idDetails;
    simpl; repeat destruct_match; reflexivity.
Qed.



(**
In this module, we prove that the exitification pass preserves the various
invariants of Core. But first we need to do some yak-shaving to deal
with the kind of definitions that we get out of hs-to-rocq here.
*)



(** ** A domain predicate for [go] *)

(**
The local function [go] of [exitifyRec] is defined via [deferredFix]. Unfortunately, it
is not defined everywhere, but only on certain well-formed terms. Because it calls
[error] (i.e. [default]) in the other cases, it is not possibly to prove termination 
using [deferredFix_eq_on] on all input, but we need to restrict accordingly.

The following predicate describes expressions on which [go] does not call [error]:
*)

Definition alt_rhs {b} (alt : Alt b) : Expr b :=
  let '(Mk_Alt _ _ rhs) := alt in rhs.

Definition alt_pats {b} (alt : Alt b) : list b :=
  let '(Mk_Alt _ pats _) := alt in pats.

Definition alt_con {b} (alt : Alt b) : AltCon :=
  let '(Mk_Alt con _ _) := alt in con.

Inductive GoDom : CoreExpr -> Prop :=
  | GoDom_Var  v: GoDom (Mk_Var v)
  | GoDom_Lit  l: GoDom (Lit l)
  | GoDom_App e1 e2:
    GoDom e1 -> GoDom (App e1 e2)
  | GoDom_Lam v e:
    GoDom e -> GoDom (Lam v e)
  | GoDom_LetNonRec_Join v rhs e:
    GoDom_JoinPair v rhs ->
    GoDom e ->
    GoDom (Let (NonRec v rhs) e)
  | GoDom_LetNonRec v rhs e:
    GoDom_Pair v rhs ->
    GoDom e ->
    GoDom (Let (NonRec v rhs) e)
  | GoDom_LetRec_Join pairs e:
    Forall (fun p => GoDom_JoinPair (fst p) (snd p)) pairs ->
    pairs <> []  -> (* because [go] uses [head] *)
    GoDom e ->
    GoDom (Let (Rec pairs) e)
  | GoDom_LetRec pairs e:
    Forall (fun p => GoDom_Pair (fst p) (snd p)) pairs ->
    pairs <> [] -> (* because [go] uses [head] *)
    GoDom e ->
    GoDom (Let (Rec pairs) e)
  | GoDom_Case scrut bndr ty alts:
    Forall (fun alt => GoDom (alt_rhs alt)) alts ->
    GoDom (Case scrut bndr ty alts)
  | GoDom_Cast e c:
    GoDom e ->
    GoDom (Cast e c)
(*  | GoDom_Tick  e t:
    GoDom e ->
    GoDom (Tick t e) *)
  | GoDom_Type t:
    GoDom (Mk_Type t)
  | GoDom_Coercion t:
    GoDom (Mk_Coercion t) 
 with GoDom_JoinPair : CoreBndr -> CoreExpr -> Prop :=
  | GoDom_Join v params rhs :
    isJoinId_maybe v = Some (length params) ->
    GoDom rhs ->
    GoDom_JoinPair v (mkLams params rhs)
    (* This is crucial: Every join point has enough lambdas *)
 with GoDom_Pair : CoreBndr -> CoreExpr -> Prop :=
  | GoDom_NotJoin v rhs :
    isJoinId_maybe v = None ->
    GoDom_Pair v rhs
  .

Lemma GoDom_JoinPair_head_isJoinId {a} `{Err.Default a}
  (erase : a -> CoreExpr) (ps : list (Var * a)) :
  ps <> [] ->
  Forall (fun p => GoDom_JoinPair (fst p) (snd p))
    (map (fun '(v,rhs) => (v,erase rhs)) ps) ->
  isJoinId (Tuple.fst (Err.head ps)) = true.
Proof.
  intros Hnonempty Hall.
  destruct ps as [|[v rhs] rest]; [contradiction|].
  inversion Hall as [|p ps' Hpair Hrest]; subst.
  inversion Hpair as [v' params body Hjoin Hbody]; subst.
  simpl in Hjoin.
  rewrite isJoinId_eq. simpl. rewrite Hjoin. reflexivity.
Qed.

Lemma GoDom_Pair_head_not_isJoinId {a} `{Err.Default a}
  (erase : a -> CoreExpr) (ps : list (Var * a)) :
  ps <> [] ->
  Forall (fun p => GoDom_Pair (fst p) (snd p))
    (map (fun '(v,rhs) => (v,erase rhs)) ps) ->
  isJoinId (Tuple.fst (Err.head ps)) = false.
Proof.
  intros Hnonempty Hall.
  destruct ps as [|[v rhs] rest]; [contradiction|].
  inversion Hall as [|p ps' Hpair Hrest]; subst.
  inversion Hpair as [v' body Hnotjoin]; subst.
  simpl in Hnotjoin.
  rewrite isJoinId_eq. simpl. rewrite Hnotjoin. reflexivity.
Qed.

Record JoinRHS := MkJoinRHS
  { jrhs_v : CoreBndr;
    jrhs_params : list CoreBndr;
    jrhs_rhs : CoreExpr;
    jrhs_isJoinRHS : isJoinId_maybe jrhs_v = Some (length jrhs_params)
  }.
  
Lemma GoDom_JoinPair_JoinRHS:
  forall v rhs,
  GoDom_JoinPair v rhs ->
  exists r, (v, rhs) = (fun '(MkJoinRHS j params body _) => (j, mkLams params body)) r.
Proof.
  intros v rhs H.
  inversion H; subst.
  eexists (MkJoinRHS v params rhs0 _).
  simpl. reflexivity.
  Unshelve. assumption.
Qed.

Lemma GoDom_JoinPair_JoinRHS_pairs:
  forall pairs,
  Forall (fun p => GoDom_JoinPair (fst p) (snd p)) pairs ->
  exists pairs', pairs = map (fun '(MkJoinRHS j params body _) => (j, mkLams params body)) pairs'.
Proof.
  intros pairs H. induction H.
  - exists nil. reflexivity.
  - destruct x as [v rhs]. simpl in H.
    apply GoDom_JoinPair_JoinRHS in H. destruct H as [r Hr].
    destruct IHForall as [pairs' Hpairs'].
    exists (r :: pairs'). simpl. rewrite <- Hpairs'.
    inversion Hr. reflexivity.
Qed.

(** The predicate is actually a corollary of being join-point valid.

So we could just use [isJoinPointsValid e n jps = true] instead of [GoDom], but that
would add the complexity of the following proof to other proofs in this module.
*)


Program Fixpoint isJoinPointsValid_GoDom
  e n jps { measure e (CoreLT) } :
  isJoinPointsValid e n jps = true ->
  GoDom e := _.
Next Obligation.
  rename isJoinPointsValid_GoDom into IH.
  destruct e.
  * constructor.
  * constructor.
  * simpl in H. simpl_bool. destruct H as [He1 He2].
    apply IH in He1; only 2: Core_termination.
    constructor. assumption.
  * simpl in H. simpl_bool. destruct H as [_ He].
    apply IH in He; only 2: Core_termination.
    constructor. assumption.
  * simpl in H.
    destruct b as [v rhs | pairs].
    + simpl_bool. destruct H as [Hpair He].
      fold isJoinPointsValidPair in Hpair.
      destruct (isJoinId_maybe v) eqn:HiJI.
      - apply GoDom_LetNonRec_Join.
        ** eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in Hpair; only 2: apply HiJI.
           destruct  (isJoinRHS_mkLams3 _ _ _ Hpair) as [rhs' [vs [Heq1 Heq2]]].
           subst.
           apply isJoinRHS_mkLams2 in Hpair.
           destruct Hpair as [_ Hpair].
           apply IH in Hpair; only 2: Core_termination.
           constructor; assumption.
        ** eapply IH in He; only 2: Core_termination.
           assumption.
      - eapply isJoinPointsValidPair_isJoinPointsValid in Hpair; only 2: apply HiJI.
        apply GoDom_LetNonRec.
        ** constructor. assumption.
        ** eapply IH in He; only 2: Core_termination.
           assumption.
    + simpl_bool. destruct H as [[HnotNull Hall_or_none] [Hpair He]].
      fold isJoinPointsValidPair in Hpair.
      simpl_bool. destruct Hall_or_none as [Hnone|Hall].
      - apply GoDom_LetRec.
        ** rewrite forallb_forall in Hnone.
           rewrite Forall_forall.
           intros [v rhs] HIn. specialize (Hnone _ HIn).
           constructor. simpl in *.
           rewrite negb_true_iff in Hnone.
           rewrite isJoinId_eq in Hnone.
           destruct_match; congruence.
        ** destruct pairs; simpl in HnotNull; congruence.
        ** eapply IH in He; only 2: Core_termination.
           assumption.
      - apply GoDom_LetRec_Join.
        ** rewrite forallb_forall in Hpair.
           rewrite forallb_forall in Hall.
           rewrite Forall_forall.
           intros [v rhs] HIn.
           specialize (Hall _ HIn).
           specialize (Hpair _ HIn).
           simpl in *.
           rewrite isJoinId_eq in Hall; destruct_match; try congruence; clear Hall.
           eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in Hpair; only 2: apply Heq.
           destruct  (isJoinRHS_mkLams3 _ _ _ Hpair) as [rhs' [vs [Heq1 Heq2]]].
           subst.
           apply isJoinRHS_mkLams2 in Hpair.
           destruct Hpair as [_ Hpair].
           apply IH in Hpair; only 2: Core_termination.
           constructor; assumption.
        ** destruct pairs; simpl in HnotNull; congruence.
        ** eapply IH in He; only 2: Core_termination.
           assumption.
   * simpl in H.  simpl_bool. destruct H as [[HnotJoin He] Halts].
     constructor.
     rewrite Forall_forall.
     intros [dc pats rhs] HIn.
     rewrite forallb_forall in Halts. specialize (Halts _ HIn).
     simpl in *.
     simpl_bool. destruct Halts as [HnotJoins Hrhs].
     apply IH in Hrhs; only 2: Core_termination.
     assumption.
   * simpl in H.
     apply IH in H; only 2: Core_termination.
     constructor. assumption.
(*   * simpl in H.
     apply IH in H; only 2: Core_termination.
     constructor. assumption. *)
   * constructor.
   * constructor. 
Qed.

Lemma isValidJoinPointsPair_GoDom_JoinPair:
  forall v e jps,
  isValidJoinPointsPair v e jps = true ->
  GoDom_JoinPair v e.
Proof.
  intros v e jps H.
  unfold isValidJoinPointsPair in H.
  destruct (isJoinId_maybe v) eqn:HiJI; try discriminate.
  destruct (isJoinRHS_mkLams3 _ _ _ H) as [body [vs [Heq1 Heq2]]].
  subst.
  apply isJoinRHS_mkLams2 in H.
  destruct H as [_ Hvalid].
  apply isJoinPointsValid_GoDom in Hvalid.
  constructor; assumption.
Qed.

(** * Working within [exitifyRec] *)

(**
A large part of this module deals with what happens “inside” [exitifyRec]. So instead
of passing the arguments to [exitifyRec] around everywhere, we use a section to “enter
this context”:
*)

Section in_exitifyRec.

  (* For better proof paralellism, see 
     https://coq.inria.fr/refman/proof-engine/proof-handling.html#coq:opt.default-proof-using-expression
   *)
  Set Default Proof Using "Type".

  (** These are (almost) the parameters of [exitifyRec] *)
  Variable in_scope : InScopeSet.
  Variable pairs : list (CoreBndr * CoreExpr).
  (** almost, because [exitifyRec] is actually called with the following
      in-scope-set, but we need access to the underlying [in_scope] in our proofs.
  *)
  Definition in_scope2 := extendInScopeSetList in_scope (map fst pairs).

  (** Not a parameter of [exitifyRec], but when doing the
      proofs about join-point-validity, we need to know which join points are
      in scope outside the [Rec] *)
  Variable jps : VarSet.

  (** Now we give  names to the local functions of [exitifyRec].
     See http://www.joachim-breitner.de/blog/738-Verifying_local_definitions_in_Coq
     for more on that idiom.
   *)

  (* Extract the actual translated local definitions, rather than introducing
     a second implementation of the exitification traversal. *)
  Definition go_exit := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 pairs) in
    lazymatch rhs with (let x := ?rhs in _) => exact rhs end).

  Definition recursive_calls := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 pairs) in
    lazymatch rhs with (let x := _ in let y := ?rhs in _) => exact rhs end).

  Definition go := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 pairs) in
    lazymatch rhs with
    | (let x1 := _ in let x2 := _ in let y := @?rhs x1 x2 in _) =>
      let def := eval cbv beta in (rhs go_exit recursive_calls) in exact def
    end).

  Definition ann_pairs := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 pairs) in
    lazymatch rhs with
    | (let x1 := _ in let x2 := _ in let x3 := _ in let y := ?rhs in _) => exact rhs
    end).

  Definition pairs'_exits := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 pairs) in
    lazymatch rhs with
    | (let x1 := _ in let x2 := _ in let x3 := _ in let x4 := _ in
         let '(pairs',exits) := @?rhs x3 x4 in _) =>
      let def := eval cbv beta in (rhs go ann_pairs) in exact def
    end).
  Definition pairs' := fst pairs'_exits.
  Definition exits := snd pairs'_exits.

  Definition go_f := ltac:(
    let rhs := eval cbv delta [go] in go in
    lazymatch rhs with
    | @DeferredFix.deferredFix2 ?a ?b ?r ?d ?f => exact f
    end).

  Lemma go_eq_on : forall captured ann_e,
    GoDom (deAnnotate ann_e) ->
    go captured ann_e = go_f go captured ann_e.
  Proof.
    intros captured ann_e Hdom.
    unfold go; fold go_f.
    unfold DeferredFix.deferredFix2, DeferredFix.curry.
    rewrite DeferredFix.deferredFix_eq_on with
      (P := fun p : list Var * CoreExprWithFVs => GoDom (deAnnotate (snd p)))
      (R := fun p1 p2 => CoreLT (deAnnotate (snd p1)) (deAnnotate (snd p2))).
    * reflexivity.
    * apply Inverse_Image.wf_inverse_image. apply CoreLT_wf.
    * clear captured ann_e Hdom.
      intros g h [captured ann_e] HP Hgh.
      simpl. cbv beta delta [go_f].
      repeat float_let; cse_let.
      enough (Hnext : j_40__ = j_40__0).
      { repeat (destruct_match; try reflexivity); try apply Hnext. }
      subst j_40__ j_40__0. cleardefs.
      destruct ann_e; destruct a;
        simpl; rewrite ?freeVarsBind1_freeVarsBind;
        try destruct n; simpl;
        try destruct (isLocalVar _);
        repeat expand_pairs; simpl;
        rewrite ?idJoinPointHood_isJoinId_maybe;
        repeat (cbv zeta; rewrite ?idJoinPointHood_isJoinId_maybe in *; destruct_match);
        simpl; rewrite ?freeVarsBind1_freeVarsBind;
        rewrite ?collectNAnnBndrs_freeVars_mkLams in *;
        try (simpl in Heq);
        try (inversion Heq; subst; clear Heq);
        try solve [congruence]; try reflexivity; simpl in HP.
      - f_equal.
        inversion_clear HP. rename H into HP.
        rewrite Forall_map in HP.
        apply forM_cong. intros [dc pats rhs] HIn.
        f_equal. apply Hgh; clear Hgh.
        + rewrite Forall_forall in HP. apply (HP _ HIn).
        + simpl. expand_pairs. simpl.
          eapply CoreLT_case_alts.
          rewrite in_map_iff. eexists. split; [|eassumption]. simpl.
          repeat expand_pairs. simpl.
          rewrite ?deAnnotate_freeVars, ?deAnnotate'_snd_freeVars.
          reflexivity.
      - subst.
        inversion HP; subst; rename H1 into HPair; clear HP;
        inversion HPair; try congruence; subst; clear H HPair.
        f_equal. apply Hgh; simpl.
        + assumption.
        + destruct p0. simpl. Core_termination.
      - subst.
        inversion HP; subst; rename H1 into HPair; clear HP;
        inversion HPair; only 2: congruence.
        subst. rename H0 into HisJoinId. rename H2 into Hdom_rhs.
        rename H into Heq. clear HPair.
        assert (n = length params) by congruence. subst n.
        pose proof (collectNAnnBndrs_mkLams_collectNBinders _ _ _ Heq) as H.
        unfold CoreBndr, Id in *. rewrite Heq2 in H. simpl in H.
        destruct H as [Eparams Erhs]. subst l.
        f_equal.
        + apply Hgh; simpl.
          -- rewrite Erhs. assumption.
          -- rewrite Erhs. destruct p0. simpl. rewrite <- Heq. Core_termination.
        + extensionality join_body'. f_equal. apply Hgh.
          -- simpl. assumption.
          -- simpl. expand_pairs. Core_termination.
      - rewrite flat_map_unpack_cons_f in *.
        inversion HP; subst; clear HP.
        2: { exfalso.
             destruct l; only 1: (apply H2; reflexivity).
             destruct p. destruct p0.
             rewrite isJoinId_eq in Heq0. simpl in Heq0.
             inversion H1. inversion_clear H4. simpl in *.
             rewrite H6 in Heq0. congruence. }
        rename H1 into Hpairs. rename H2 into HnotNil. rename H3 into He.
        f_equal.
        + apply forM_cong. intros [j e'] HIn.
          rewrite Forall_map in Hpairs. rewrite Forall_forall in Hpairs.
          specialize (Hpairs _ HIn). simpl in Hpairs.
          inversion Hpairs. subst. rename H0 into HiNJ.
          rename H2 into Hrhs. rename H into Heq2.
          expand_pairs. erewrite idJoinArity_join by eassumption.
          pose proof (collectNAnnBndrs_mkLams_collectNBinders _ _ _ Heq2) as H.
          destruct H as [Heq1 Heq3]. subst.
          f_equal. apply Hgh.
          -- assumption.
          -- simpl. rewrite ?freeVarsBind1_freeVarsBind. simpl.
             repeat expand_pairs. simpl. rewrite flat_map_unpack_cons_f.
             eapply CoreLT_let_pairs_mkLam with (vs := params).
             rewrite in_map_iff. eexists. split; [|eassumption]. simpl.
             expand_pairs. f_equal. symmetry. destruct e'. apply Heq2.
        + extensionality pairs'. f_equal. apply Hgh.
          -- apply He.
          -- simpl. repeat expand_pairs. simpl. Core_termination.
      - rewrite flat_map_unpack_cons_f in *.
        inversion HP; subst; clear HP.
        1: { exfalso.
             destruct l; only 1: (apply H2; reflexivity).
             destruct p0.
             rewrite isJoinId_eq in Heq0. simpl in Heq0.
             inversion H1. inversion_clear H4. simpl in *.
             rewrite H6 in Heq0. congruence. }
        rename H1 into Hpairs. rename H2 into HnotNil. rename H3 into He.
        f_equal. apply Hgh.
        + apply He.
        + simpl. repeat expand_pairs. simpl. Core_termination.
    * simpl. assumption.
  Qed.

  Lemma go_eq : forall captured e,
    Forall GoodVar captured -> GoDom e ->
    go captured (freeVars e) = go_f go captured (freeVars e).
  Proof.
    intros captured e _ Hdom. apply go_eq_on.
    rewrite deAnnotate_freeVars. assumption.
  Qed.

  (* A guarded induction interface for the actual annotated traversal.  The
     recursive hypothesis is available only on domain-valid, smaller terms. *)
  Lemma go_ind_on : forall
    (P : list Var -> CoreExprWithFVs -> ExitifyM CoreExpr -> Prop),
    (forall captured ann_e,
      GoDom (deAnnotate ann_e) ->
      (forall captured' ann_e',
        GoDom (deAnnotate ann_e') ->
        CoreLT (deAnnotate ann_e') (deAnnotate ann_e) ->
        P captured' ann_e' (go captured' ann_e')) ->
      P captured ann_e (go_f go captured ann_e)) ->
    forall captured ann_e,
      GoDom (deAnnotate ann_e) -> P captured ann_e (go captured ann_e).
  Proof.
    intros P Hstep.
    assert (Hind : forall e captured ann_e,
      deAnnotate ann_e = e -> GoDom e -> P captured ann_e (go captured ann_e)).
    { refine (well_founded_ind CoreLT_wf _ _).
      intros e IH captured ann_e E Hdom.
      rewrite go_eq_on by (rewrite E; assumption).
      apply Hstep; [rewrite E; assumption|].
      intros captured' ann_e' Hdom' Hlt.
      eapply IH; [rewrite <- E; exact Hlt|reflexivity|exact Hdom']. }
    intros captured ann_e Hdom.
    eapply Hind; [reflexivity|exact Hdom].
  Qed.

  Definition isvs := getInScopeVars in_scope.
  Definition fs := map fst pairs.

  Definition isvsp := extendVarSetList isvs fs.
  Definition isvs' := extendVarSetList isvs (map fst exits).
  Definition isvsp' := extendVarSetList isvs' fs.
  Definition jpsp := updJPSs jps fs.
  Definition jps' := updJPSs jps (map fst exits).
  Definition jpsp' := updJPSs jps' fs.

  (* Generic scopes are raw VarSets.  Carry both certificates explicitly;
     membership equality alone does not preserve the IntMap invariant. *)
  Hypothesis isvs_WF : WF isvs.
  Hypothesis isvs_valid : ValidVarSet isvs.
  Hypothesis jps_WF : WF jps.
  Hypothesis jps_valid : ValidVarSet jps.

  Set Default Proof Using "Type isvs_WF isvs_valid jps_WF jps_valid".

  #[local] Hint Resolve updJPS_WF updJPS_valid updJPSs_WF updJPSs_valid : varset_inv.

  Local Ltac exit_inv :=
    rewrite ?getInScopeVars_extendInScopeSet, ?getInScopeVars_extendInScopeSetList;
    unfold in_scope2;
    rewrite ?getInScopeVars_extendInScopeSetList;
    change (getInScopeVars in_scope) with isvs;
    unfold isvsp', isvs', isvsp, jpsp', jps', jpsp;
    repeat first [apply updJPSs_WF | apply updJPS_WF | apply updJPSs_valid | apply updJPS_valid];
    solve_varset_inv.

  Lemma isvsp_extended_WF vs : WF (extendVarSetList isvsp vs).
  Proof. exit_inv. Qed.
  Lemma isvsp'_extended_WF vs : WF (extendVarSetList isvsp' vs).
  Proof. exit_inv. Qed.

  Local Lemma exit_weaken {P : VarSet -> Prop} `{Respects_StrongSubset P}
    {s t} (S : StrongSubset s t) : WF s -> WF t -> P s -> P t.
  Proof. intros W T Hs. exact (weaken W T S Hs). Qed.

  Local Lemma exit_weakenb {P : VarSet -> bool}
    `{Respects_StrongSubset (fun s => P s = true)}
    {s t} (S : StrongSubset s t) : WF s -> WF t -> P s = true -> P t = true.
  Proof. intros W T Hs. exact (weaken W T S Hs). Qed.

  Definition WellScopedFloats (floats : list (Var * CoreExpr)) :=
    Forall (fun p => elemVarSet (fst p) isvs = false) floats /\
    NoDup (map (fun p => varUnique (fst p)) floats) /\
    Forall (fun p => WellScoped (snd p) isvs) floats /\
    Forall (fun p => GoodLocalVar (fst p)) floats.

  Lemma mkLets_WellScoped : forall exits' e,
    WellScoped e (extendVarSetList isvs (map fst exits')) ->
    WellScopedFloats exits' ->
    WellScoped (mkLets (map (fun '(v,rhs) => NonRec v rhs) exits') e) isvs.
  Proof.
    intros exits'. unfold WellScopedFloats.
    generalize isvs_WF, isvs_valid.
    generalize isvs as outer.
    induction exits' as [|[v rhs] rest IH]; intros outer W V e Hbase Hfloats.
    * simpl. unfold Base.id. assumption.
    * simpl in *.
      rewrite extendVarSetList_cons, extendVarSetList_nil.
      destruct Hfloats as [Hfreshs [HNoDup [Hrhss HGLVs]]].
      inversion HNoDup; subst; clear HNoDup.
      rename H1 into Hfresh. rename H2 into HNoDup.
      inversion_clear Hrhss. rename H into Hrhs. rename H0 into Hrhss.
      inversion_clear Hfreshs. rename H into Hfresh_v. rename H0 into Hfreshs.
      inversion_clear HGLVs. rename H into HGLVv. rename H0 into HGLVs.
      simpl in *.
      rewrite extendVarSetList_cons in Hbase.
      split; [split; [apply HGLVv|apply Hrhs]|].
      apply IH; try solve [solve_varset_inv]; [assumption|]. repeat split.
      - rewrite Forall_forall. rewrite Forall_forall in Hfreshs.
        rewrite in_map_iff in Hfresh.
        intros [v' rhs'] HIn. rewrite elemVarSet_extendVarSet by assumption.
        simpl_bool. split.
        + simpl.
          unfold GHC.Base.op_zeze__, Core.Eq___Var, op_zeze____,
            Core.Eq___Var_op_zeze__.
          unfold GHC.Base.op_zeze__, Core.Eq___Var, op_zeze____, Eq_Char___.
          change (Unique.eqUnique (realUnique v) (realUnique v') = false).
          rewrite eqUnique_neq. intro E. apply Hfresh.
          exists (v',rhs'). split; [simpl; unfold varUnique; rewrite E; reflexivity|assumption].
        + apply Hfreshs. assumption.
      - assumption.
      - rewrite Forall_forall. rewrite Forall_forall in Hrhss.
        intros p HIn. simpl.
        rewrite WellScoped_extendVarSet_fresh; try exact W.
        + apply Hrhss. assumption.
        + eapply subVarSet_elemVarSet_false; try solve [solve_varset_inv].
          -- apply WellScoped_subset; [apply Hrhss; assumption|exact W|exact V].
          -- eassumption.
      - assumption.
  Qed.

  Lemma addExit_all_WellScopedFloats : forall captured ja e,
    WellScoped e isvs ->
    StateInvariant WellScopedFloats
      (addExit (extendInScopeSetList in_scope2 captured) ja e).
  Proof.
    intros captured ja e HWS.
    unfold addExit, mkExitJoinId, StateInvariant, SP, State.runState.
    cbn.
    intros floats Hfloats.
    set (v := uniqAway _ _).
    split; [|exact I].
    unfold WellScopedFloats in *.
    destruct Hfloats as [Hfresh [Hnodup [Hrhss Hgood]]].
    repeat split.
    * constructor; [|assumption]. simpl. subst v.
      unfold isvs, in_scope2 in *.
      apply elemVarSet_uniqAway; try solve [exit_inv].
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet; try solve [exit_inv].
      repeat (apply subVarSet_extendVarSetList_l; try solve [exit_inv]). apply subVarSet_refl; exit_inv.
    * constructor; [|assumption].
      change (~ List.In (varUnique v) (map (fun p => varUnique (fst p)) floats)).
      rewrite <- (map_map fst varUnique floats).
      rewrite <- hs_coq_map.
      rewrite <- elemVarSet_mkVarset_iff_In. subst v.
      unfold is_true. rewrite not_true_iff_false.
      apply elemVarSet_uniqAway; try solve [exit_inv].
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet; try solve [exit_inv].
      apply subVarSet_extendVarSetList_r; try solve [exit_inv].
      apply subVarSet_refl; exit_inv.
    * constructor; assumption.
    * constructor; [|assumption]. simpl. subst v.
      apply GoodLocalVar_uniqAway. apply GoodLocalVar_asJoinId_mkSysLocal.
      apply isLocalUnique_initExitJoinUnique.
  Qed.

  Definition zap := ltac:(
    let rhs := eval cbv beta delta [go_exit] in
      (go_exit [] HsToRocq.Err.default emptyVarSet) in
    lazymatch rhs with (let zap := ?rhs in _) => exact rhs end).

  Definition pick := ltac:(
    let rhs := eval cbv beta delta [go_exit] in
      (go_exit [] HsToRocq.Err.default emptyVarSet) in
    lazymatch rhs with
    | (let zap' := _ in let abs_vars := let pick := @?rhs zap' in _ in _) =>
      let def := eval cbv beta in (rhs zap) in exact def
    end).

  Lemma zap_ae : forall x, almostEqual x (zap x).
  Proof. intro v. unfold zap. destruct v. simpl. constructor. Qed.

  Lemma GoodVar_zap : forall x, GoodVar x -> GoodVar (zap x).
  Proof.
    intros x Hgood. eapply GoodVar_almostEqual; [exact Hgood|apply zap_ae].
  Qed.

  Lemma fst_pick_list : forall fvs vs xs,
    fst (fold_right pick (fvs,vs) xs) = fst (fold_right pick (fvs,[]) xs).
  Proof.
    induction xs; [reflexivity|].
    simpl. unfold pick at 1 3. do 2 expand_pairs.
    rewrite !IHxs. destruct_match; simpl; reflexivity.
  Qed.

  Lemma snd_pick_list : forall fvs vs xs,
    snd (fold_right pick (fvs,vs) xs) = snd (fold_right pick (fvs,[]) xs) ++ vs.
  Proof.
    induction xs; [reflexivity|].
    simpl. unfold pick at 1 3. do 2 expand_pairs.
    rewrite !fst_pick_list. simpl. destruct_match; simpl; rewrite IHxs; reflexivity.
  Qed.

  Definition varset_pair_eq (x y : VarSet * list Id) :=
    let '(a,b) := x in let '(c,d) := y in
    VarSetFSet.VarSetFSet.Equal a c /\ b = d.

  #[local] Instance pair_l_m :
    Morphisms.Proper (Morphisms.respectful VarSetFSet.VarSetFSet.Equal
      (Morphisms.respectful Logic.eq varset_pair_eq)) pair.
  Proof. intros v1 v2 Heq1 x y E. subst y. split; auto. Qed.

  Lemma fold_right_pick_WF fvs vs xs : WF fvs ->
    WF (fst (fold_right pick (fvs,vs) xs)).
  Proof.
    intro W. induction xs; simpl; [exact W|].
    unfold pick at 1. destruct (fold_right pick (fvs,vs) xs) as [s l].
    simpl in *. destruct (elemVarSet a s); simpl; solve_varset_inv.
  Qed.

  Lemma fold_right_m v1 v2 l l0 xs : WF v1 -> WF v2 ->
    varset_pair_eq (v1,l) (v2,l0) ->
    varset_pair_eq (fold_right pick (v1,l) xs) (fold_right pick (v2,l0) xs).
  Proof.
    intros W T Heq. induction xs as [|a xs IH]; simpl; [exact Heq|].
    pose proof (fold_right_pick_WF v1 l xs W) as W1.
    pose proof (fold_right_pick_WF v2 l0 xs T) as W2.
    unfold pick at 1 3. destruct (fold_right pick (v1,l) xs) as [s ls].
    destruct (fold_right pick (v2,l0) xs) as [t lt].
    destruct IH as [E L]. simpl in *. subst lt.
    assert (M : elemVarSet a s = elemVarSet a t) by (apply eqE; exact (E a)).
    rewrite M. destruct (elemVarSet a t); split; auto.
    apply delVarSet_m; auto. apply Eq_refl.
  Qed.

  #[local] Instance snd_m :
    Morphisms.Proper (Morphisms.respectful varset_pair_eq Logic.eq)
      (@snd VarSet (list Id)).
  Proof. intros [v1 l1] [v2 l2] [H E]. exact E. Qed.

  Lemma WellScoped_picked_aux : forall fvs captured e vs,
    WF fvs ->
    WellScoped e (extendVarSetList fvs (captured ++ vs)) ->
    WellScoped e (extendVarSetList fvs
      (snd (fold_right pick (delVarSetList (exprFreeVars e) vs,[]) captured) ++ vs)).
  Proof.
    intros fvs captured e. induction captured using rev_ind; intros vs W HWS; simpl.
    * assumption.
    * rewrite fold_right_app. simpl. destruct_match; simpl.
      + rewrite snd_pick_list, <- app_assoc.
        erewrite delVarSet_ae by apply zap_ae.
        assert (E : snd (fold_right pick (delVarSet (delVarSetList (exprFreeVars e) vs) (zap x),[]) captured) =
          snd (fold_right pick (delVarSetList (exprFreeVars e) (zap x :: vs),[]) captured)).
        { apply snd_m. apply fold_right_m; try solve [solve_varset_inv].
          split; [symmetry; apply delVarSetList_cons2; solve_varset_inv|reflexivity]. }
        rewrite E. apply IHcaptured; [exact W|].
        rewrite app_assoc.
        erewrite Respects_StrongSubset_extendVarSetList_ae; only 1: apply HWS.
        all: try exact W.
        repeat apply Forall2_app.
        - apply Forall2_symmetric. intro. apply almostEqual_refl.
        - constructor; [apply almostEqual_sym; apply zap_ae|constructor].
        - apply Forall2_symmetric. intro. apply almostEqual_refl.
      + apply IHcaptured; [exact W|].
        rewrite <- WellScoped_extendVarSetList_fresh_between; [apply HWS| |exact W].
        apply disjointVarSet_mkVarSet; try solve [solve_varset_inv]. constructor; [assumption|constructor].
  Qed.

  Lemma WellScoped_picked : forall fvs captured e,
    WF fvs ->
    WellScoped e (extendVarSetList fvs captured) ->
    WellScoped e (extendVarSetList fvs
      (snd (fold_right pick (exprFreeVars e,[]) captured))).
  Proof.
    intros fvs captured e W HWS.
    pose proof (WellScoped_picked_aux fvs captured e []).
    rewrite !app_nil_r, delVarSetList_nil in *. auto.
  Qed.

  Lemma Forall_picked : forall P captured fvs,
    Forall (fun x => P (zap x)) captured ->
    Forall P (snd (fold_right pick (fvs,[]) captured)).
  Proof.
    intros P captured fvs H. induction H; [constructor|].
    simpl. unfold pick. expand_pairs. destruct_match.
    - constructor; assumption.
    - assumption.
  Qed.

  Lemma go_exit_all_WellScopedFloats captured e :
    Forall GoodLocalVar captured ->
    WellScoped e (extendVarSetList isvsp captured) ->
    disjointVarSet (exprFreeVars e) recursive_calls = true ->
    StateInvariant WellScopedFloats (go_exit captured e (exprFreeVars e)).
  Proof.
    intros HGLV HWS Hdisjoint.
    set (P := WellScopedFloats).
    cbv beta delta [go_exit]. repeat float_let.
    enough (Hnext : StateInvariant P j_16__).
    { clearbody j_16__; cleardefs. subst _go3.
      destruct (collectArgs _) as [rhs args] eqn:Hargs.
      destruct rhs; try apply Hnext.
      destruct (isJoinId i && Foldable.all isCapturedVarArg args);
        [apply StateInvariant_return|apply Hnext]. }
    cleardefs. subst j_16__.
    enough (Hnext : StateInvariant P j_15__).
    { subst _go2. destruct (negb is_interesting);
        [apply StateInvariant_return|apply Hnext]. }
    cleardefs. subst j_15__.
    enough (Hnext : StateInvariant P j_14__).
    { destruct captures_join_points; [apply StateInvariant_return|apply Hnext]. }
    cleardefs. subst _go _go0 j_14__.
    unfold recursive_calls in Hdisjoint.
    apply StateInvariant_bind_return. apply addExit_all_WellScopedFloats.
    rewrite WellScoped_mkLams. subst abs_vars.
    repeat float_let.
    replace pick0 with pick by reflexivity.
    replace pick1 with pick by reflexivity. cleardefs.
    rewrite Foldable.hs_coq_foldr_list. split.
    * apply Forall_picked.
      eapply Forall_impl; only 2: apply HGLV.
      intros v Hv. eapply GoodLocalVar_almostEqual; [exact Hv|apply zap_ae].
    * apply WellScoped_picked; [exit_inv|].
      rewrite hs_coq_map in Hdisjoint.
      replace (map _ pairs) with fs in Hdisjoint by reflexivity.
      unfold isvsp in HWS.
      rewrite WellScoped_extendVarSetList_fresh_under in HWS; try exact isvs_WF; only 1: assumption.
      eapply disjointVarSet_subVarSet_l with (t := exprFreeVars e); try solve [exit_inv]; only 1: eassumption.
      apply subVarSet_delVarSetList; exit_inv.
  Qed.

  Lemma go_all_WellScopedFloats_on : forall captured ann_e,
    GoDom (deAnnotate ann_e) ->
    Forall GoodLocalVar captured ->
    WellScoped (deAnnotate ann_e) (extendVarSetList isvsp captured) ->
    StateInvariant WellScopedFloats (go captured ann_e).
  Proof.
    refine (go_ind_on
      (fun captured ann_e r => Forall GoodLocalVar captured ->
        WellScoped (deAnnotate ann_e) (extendVarSetList isvsp captured) ->
        StateInvariant WellScopedFloats r) _).
    intros captured ann_e Hdom IH Hcapt HWS.
    unfold CoreBndr, Id in *.
    cbv beta delta [go_f]. unfold CoreBndr, Id in *.
    unfold dVarSetToVarSet.
    destruct (disjointVarSet (exprFreeVars (deAnnotate ann_e)) recursive_calls)
      eqn:Hdisjoint.
    { apply go_exit_all_WellScopedFloats; assumption. }
    destruct ann_e as [f a]. destruct a; simpl in *;
      try apply StateInvariant_return.
    - destruct HWS as [Hscrut [Hgood Halts]].
      inversion Hdom; subst.
      rewrite Forall'_Forall, hs_coq_map, Forall_map, Forall_forall in Halts.
      match goal with H : Forall _ (Base.map _ l) |- _ =>
        rewrite hs_coq_map, Forall_map, Forall_forall in H;
        rename H into Hdomalts end.
      apply StateInvariant_bind_return. apply StateInvariant_forM.
      intros [dc pats rhs] HIn.
      apply StateInvariant_bind_return. apply IH.
      + exact (Hdomalts _ HIn).
      + eapply CoreLT_case_alts. rewrite hs_coq_map, in_map_iff.
        exists (Mk_AnnAlt dc pats rhs). split; [reflexivity|exact HIn].
      + rewrite Forall_app. split; [exact Hcapt|].
        constructor; [exact Hgood|exact (proj1 (Halts _ HIn))].
      + rewrite extendVarSetList_append. exact (proj2 (Halts _ HIn)).
    - destruct a as [j rhs|aps]; simpl in *.
      + rewrite idJoinPointHood_isJoinId_maybe.
        inversion Hdom; subst.
        * match goal with H : GoDom_JoinPair _ _ |- _ => inversion H; subst end.
          unfold CoreBndr, Id in *. rewrite H0. simpl.
          pose proof (collectNAnnBndrs_mkLams_collectNBinders _ _ _ H) as HC.
          unfold CoreBndr, Id in HC.
          destruct (collectNAnnBndrs (length params) rhs) as [ps body] eqn:HE.
          simpl in HC. destruct HC as [Eps Ebody]. subst ps.
          destruct HWS as [[Hgood Hrhs] Hbody].
          rewrite <- H, WellScoped_mkLams in Hrhs.
          eapply StateInvariant_bind.
          -- apply IH.
             ++ rewrite Ebody. exact H4.
             ++ rewrite Ebody. rewrite <- H. Core_termination.
             ++ rewrite Forall_app. split; [exact Hcapt|exact (proj1 Hrhs)].
             ++ rewrite Ebody, extendVarSetList_append. exact (proj2 Hrhs).
          -- intros body'. apply StateInvariant_bind_return. apply IH.
             ++ exact H3.
             ++ Core_termination.
             ++ rewrite Forall_app. split; [exact Hcapt|].
                constructor; [exact Hgood|constructor].
             ++ rewrite extendVarSetList_append. exact Hbody.
        * match goal with H : GoDom_Pair _ _ |- _ => inversion H; subst end.
          match goal with H : isJoinId_maybe j = None |- _ => rewrite H end. simpl.
          destruct HWS as [[Hgood Hrhs] Hbody].
          apply StateInvariant_bind_return. apply IH.
          -- exact H3.
          -- Core_termination.
          -- rewrite Forall_app. split; [exact Hcapt|].
             constructor; [exact Hgood|constructor].
          -- rewrite extendVarSetList_append. exact Hbody.
      + repeat rewrite flat_map_unpack_cons_f in *.
        rewrite !hs_coq_map in *.
        assert (Efst : map fst
          (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps) = map fst aps).
        { rewrite map_map. apply map_ext. intros [v rhs]. reflexivity. }
        change (GoDom (Let (Rec (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))
          (deAnnotate p))) in Hdom.
        change ((Forall (fun q => GoodLocalVar (fst q))
            (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps) /\
          NoDup (map varUnique (map fst
            (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))) /\
          Forall' (fun q => WellScoped (snd q)
            (extendVarSetList (extendVarSetList isvsp captured)
              (map fst (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))))
            (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps)) /\
          WellScoped (deAnnotate p)
            (extendVarSetList (extendVarSetList isvsp captured)
              (map fst (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps)))) in HWS.
        rewrite Efst in HWS.
        destruct HWS as [[Hgood [Hnodup Hrhss]] Hbody].
        rewrite Forall_map, Forall_forall in Hgood.
        rewrite Forall'_Forall, Forall_map, Forall_forall in Hrhss.
        inversion Hdom; subst.
        * assert (Hjoin : isJoinId (Tuple.fst (Err.head aps)) = true).
          { eapply GoDom_JoinPair_head_isJoinId with (erase := @deAnnotate Var FVAnn).
            - intro Hnil. subst aps. apply H2. reflexivity.
            - exact H1. }
          rewrite Hjoin. apply StateInvariant_bind.
          -- apply StateInvariant_forM. intros [j rhs] HIn.
             rewrite Forall_map, Forall_forall in H1.
             specialize (H1 _ HIn). simpl in H1.
             inversion H1; subst. erewrite idJoinArity_join by eassumption.
             pose proof (collectNAnnBndrs_mkLams_collectNBinders _ _ _ H) as HC.
             unfold CoreBndr, Id in *.
             destruct (collectNAnnBndrs (length params) rhs) as [ps body] eqn:HE.
             simpl in HC. destruct HC as [Eps Ebody]. subst ps.
             apply StateInvariant_bind_return. apply IH.
             ++ rewrite Ebody. assumption.
             ++ rewrite Ebody. eapply CoreLT_let_pairs_mkLam with (vs := params).
                rewrite in_map_iff. exists (j,rhs).
                split; [simpl; f_equal; symmetry; exact H|exact HIn].
             ++ rewrite !Forall_app. split; [exact Hcapt|]. split.
                ** rewrite Forall_map, Forall_forall. intros [v rhs'] Hin.
                   exact (Hgood _ Hin).
                ** specialize (Hrhss _ HIn). simpl in Hrhss.
                   rewrite <- H, WellScoped_mkLams in Hrhss. exact (proj1 Hrhss).
             ++ rewrite Ebody, !extendVarSetList_append.
                specialize (Hrhss _ HIn). simpl in Hrhss.
                rewrite <- H, WellScoped_mkLams in Hrhss. exact (proj2 Hrhss).
          -- intros ps. apply StateInvariant_bind_return. apply IH.
             ++ assumption.
             ++ Core_termination.
             ++ rewrite Forall_app. split; [exact Hcapt|].
                rewrite Forall_map, Forall_forall. intros [v rhs'] Hin. exact (Hgood _ Hin).
             ++ rewrite extendVarSetList_append. exact Hbody.
        * assert (Hjoin : isJoinId (Tuple.fst (Err.head aps)) = false).
          { eapply GoDom_Pair_head_not_isJoinId with (erase := @deAnnotate Var FVAnn).
            - intro Hnil. subst aps. apply H2. reflexivity.
            - exact H1. }
          rewrite Hjoin.
          assert (Ebinders : map (fun '(x,_) => x)
            (map (fun '(x,y) => (x,deAnnotate y)) aps) = map fst aps).
          { rewrite map_map. apply map_ext. intros [v rhs]. reflexivity. }
          change (StateInvariant WellScopedFloats
            (go (captured ++ map (fun '(x,_) => x)
                (map (fun '(x,y) => (x,deAnnotate y)) aps)) p >>=
              (fun body' => return_ (Let
                (Rec (map (fun '(x,y) => (x,deAnnotate y)) aps)) body')))).
          rewrite Ebinders. apply StateInvariant_bind_return. apply IH.
          -- exact H3.
          -- Core_termination.
          -- rewrite Forall_app. split; [exact Hcapt|].
             rewrite Forall_map, Forall_forall. intros [v rhs'] Hin. exact (Hgood _ Hin).
          -- rewrite extendVarSetList_append. exact Hbody.
  Qed.

  Hypothesis pairs_WS :
    Forall (fun p => GoodLocalVar (fst p) /\ WellScoped (snd p) (extendVarSetList (isvs) fs)) pairs.

  Hypothesis pairs_VJPP :
    Forall (fun p => isValidJoinPointsPair (fst p) (snd p) (updJPSs jps fs) = true) pairs.

  Hypothesis pairs_NoDup :
    NoDup (map varUnique fs).

  Hypothesis jps_subset_isvs :
    subVarSet jps (isvs) = true.

  Lemma all_exits_WellScoped : WellScopedFloats exits.
  Proof using Type pairs_WS pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    unfold exits, pairs'_exits, ann_pairs, GHC.Prim.rightSection.
    rewrite hs_coq_map, forM_map.
    eapply SP_snd_runState.
    * apply StateInvariant_forM. intros [v e] HIn.
      assert (Hdom : GoDom_JoinPair v e).
      { eapply isValidJoinPointsPair_GoDom_JoinPair.
        rewrite Forall_forall in pairs_VJPP. exact (pairs_VJPP _ HIn). }
      inversion Hdom; subst.
      simpl. erewrite idJoinArity_join by eassumption.
      rewrite collectNAnnBndrs_freeVars_mkLams.
      apply StateInvariant_bind_return. apply go_all_WellScopedFloats_on.
      - rewrite deAnnotate_freeVars. assumption.
      - rewrite Forall_forall in pairs_WS.
        specialize (pairs_WS _ HIn). simpl in pairs_WS.
        rewrite WellScoped_mkLams in pairs_WS. exact (proj1 (proj2 pairs_WS)).
      - rewrite deAnnotate_freeVars.
        rewrite Forall_forall in pairs_WS.
        specialize (pairs_WS _ HIn). simpl in pairs_WS.
        rewrite WellScoped_mkLams in pairs_WS. exact (proj2 (proj2 pairs_WS)).
    * repeat split; constructor.
  Qed.

  Lemma disjoint_isvs_exits : disjointVarSet isvs (mkVarSet (map fst exits)) = true.
  Proof using Type pairs_WS pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    rewrite <- hs_coq_map. apply disjointVarSet_mkVarSet; try solve [exit_inv].
    rewrite hs_coq_map, Forall_map.
    exact (proj1 all_exits_WellScoped).
  Qed.

  Lemma isvs_to_isvs' : StrongSubset isvs isvs'.
  Proof using Type pairs_WS pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    apply StrongSubset_extendList_fresh; try solve [exit_inv]. exact disjoint_isvs_exits.
  Qed.

  Lemma isvsp_to_isvsp' : StrongSubset isvsp isvsp'.
  Proof using Type pairs_WS pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    apply StrongSubset_extendVarSetList; try solve [exit_inv]. exact isvs_to_isvs'.
  Qed.

  Lemma isvsp_to_isvsp'_extended : forall vs,
    StrongSubset (extendVarSetList isvsp vs) (extendVarSetList isvsp' vs).
  Proof using Type pairs_WS pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    intro vs. apply StrongSubset_extendVarSetList; try solve [exit_inv]. exact isvsp_to_isvsp'.
  Qed.

  Lemma WellScopedVar_picked_aux : forall vsis captured fvs,
    WF vsis -> WF fvs ->
    Forall GoodVar captured ->
    Forall (fun v => WellScopedVar v (extendVarSetList vsis captured))
      (snd (fold_right pick (fvs,[]) captured)) /\
    Forall (fun v => elemVarSet v fvs = true)
      (snd (fold_right pick (fvs,[]) captured)).
  Proof.
    clear pairs_WS pairs_VJPP pairs_NoDup jps_subset_isvs.
    intros vsis captured. induction captured using rev_ind; intros fvs W T Hgood.
    * split; constructor.
    * rewrite fold_right_app. simpl.
      rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
      destruct_match.
      + rewrite snd_pick_list.
        assert (Hg : Forall GoodVar captured) by (rewrite Forall_app in Hgood; tauto).
        destruct (IHcaptured (delVarSet fvs x) W (delVarSet_WF _ _ T) Hg) as [IH1 IH2].
        split; apply Forall_app; split.
        - rewrite Forall_forall in *. intros v HIn.
          specialize (IH1 _ HIn). specialize (IH2 _ HIn).
          change (WellScoped (Mk_Var v) (extendVarSet (extendVarSetList vsis captured) x)).
          apply WellScoped_extendVarSet_fresh; try solve [solve_varset_inv]; only 2: exact IH1.
          apply elemVarSet_exprFreeVars_Var_false.
          rewrite elemVarSet_delVarSet in IH2 by exact T.
          rewrite andb_true_iff in IH2. destruct IH2 as [Hneq _].
          rewrite negb_true_iff in Hneq.
          rewrite var_eq_realUnique in Hneq.
          change (Unique.eqUnique (realUnique x) (realUnique v) = false) in Hneq.
          apply eqUnique_neq in Hneq.
          intro E. unfold varUnique in E.
          exact (Hneq E).
        - constructor; [|constructor].
          change (WellScoped (Mk_Var (zap x)) (extendVarSet (extendVarSetList vsis captured) x)).
          rewrite Respects_StrongSubset_extendVarSet_ae by (solve_varset_inv || apply zap_ae).
          apply WellScopedVar_extendVarSet; try solve [solve_varset_inv].
          rewrite Forall_app in Hgood. destruct Hgood as [_ Hx]. inversion Hx.
          eauto using GoodVar_zap.
        - rewrite Forall_forall in *. intros v HIn.
          specialize (IH2 _ HIn). rewrite elemVarSet_delVarSet in IH2 by exact T.
          rewrite andb_true_iff in IH2. tauto.
        - constructor; [|constructor].
          erewrite <- elemVarSet_ae by apply zap_ae. assumption.
      + assert (Hg : Forall GoodVar captured) by (rewrite Forall_app in Hgood; tauto).
        destruct (IHcaptured fvs W T Hg) as [IH1 IH2]. split.
        - rewrite Forall_forall in *. intros v HIn.
          specialize (IH1 _ HIn). specialize (IH2 _ HIn).
          change (WellScoped (Mk_Var v) (extendVarSet (extendVarSetList vsis captured) x)).
          apply WellScoped_extendVarSet_fresh; try solve [solve_varset_inv]; only 2: exact IH1.
          apply elemVarSet_exprFreeVars_Var_false.
          eapply elemVarSet_false_true; eassumption.
        - exact IH2.
  Qed.

  Lemma WellScopedVar_picked : forall vsis captured fvs,
    WF vsis -> WF fvs ->
    Forall GoodVar captured ->
    Forall (fun v => WellScopedVar v (extendVarSetList vsis captured))
      (snd (fold_right pick (fvs,[]) captured)).
  Proof. intros. apply WellScopedVar_picked_aux; assumption. Qed.

  Lemma addExit_all_WellScopedVar : forall captured ja e,
    Forall GoodVar captured ->
    RevStateInvariant (sublistOf exits)
      (addExit (extendInScopeSetList in_scope2 captured) ja e)
      (fun v => WellScopedVar v (extendVarSetList isvsp' captured)).
  Proof using Type pairs_WS pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    intros captured ja e Hcapt.
    unfold addExit, mkExitJoinId, RevStateInvariant, SP, State.runState.
    cbn. intros floats Hfloats.
    set (v := uniqAway _ _) in *.
    apply sublistOf_cons in Hfloats. destruct Hfloats as [HIn Hsub].
    apply in_map with (f := fst) in HIn. simpl in HIn.
    split; [exact Hsub|].
    apply WellScopedVar_extendVarSetList_l; try solve [exit_inv]; only 1: (apply WellScopedVar_extendVarSetList_l; try solve [exit_inv]).
    * apply WellScopedVar_extendVarSetList_r; try solve [exit_inv]; only 2: exact HIn.
      - destruct all_exits_WellScoped as [_ [_ [_ Hgood]]].
        rewrite Forall_map. eapply Forall_impl; only 2: exact Hgood.
        intros [x rhs] Hx. exact (proj1 Hx).
      - rewrite map_map. exact (proj1 (proj2 all_exits_WellScoped)).
    * subst v. apply elemVarSet_uniqAway; try solve [exit_inv].
      unfold in_scope2.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet; try solve [exit_inv].
      apply subVarSet_extendVarSetList_l; try solve [exit_inv]. apply subVarSet_extendVarSetList_l; try solve [exit_inv].
      apply subVarSet_extendVarSetList_r; try solve [exit_inv]. apply subVarSet_refl; exit_inv.
    * subst v. apply elemVarSet_uniqAway; try solve [exit_inv].
      unfold in_scope2.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet; try solve [exit_inv]. apply subVarSet_extendVarSetList_l; try solve [exit_inv].
      apply subVarSet_extendVarSetList_r; try solve [exit_inv]. apply subVarSet_refl; exit_inv.
  Qed.

  Lemma go_exit_res_WellScoped captured e :
    Forall GoodVar captured ->
    WellScoped e (extendVarSetList isvsp captured) ->
    RevStateInvariant (sublistOf exits) (go_exit captured e (exprFreeVars e))
      (fun e' => WellScoped e' (extendVarSetList isvsp' captured)).
  Proof using Type pairs_WS pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    intros Hcapt HWS.
    set (P := fun act => RevStateInvariant (sublistOf exits) act
      (fun e' => WellScoped e' (extendVarSetList isvsp' captured))).
    change (P (go_exit captured e (exprFreeVars e))).
    cbv beta delta [go_exit]. repeat float_let.
    assert (Hreturn : P (return_ e)).
    { apply RevStateInvariant_return.
      exact (weaken (vs1 := extendVarSetList isvsp captured)
        (vs2 := extendVarSetList isvsp' captured)
        ltac:(exit_inv) ltac:(exit_inv) (isvsp_to_isvsp'_extended captured) HWS). }
    enough (Hnext : P j_16__).
    { clearbody j_16__; cleardefs. subst _go3.
      destruct (collectArgs _) as [rhs args]. destruct rhs; try exact Hnext.
      destruct (isJoinId i && Foldable.all isCapturedVarArg args); assumption. }
    cleardefs. subst j_16__.
    enough (Hnext : P j_15__).
    { subst _go2. destruct (negb is_interesting); assumption. }
    cleardefs. subst j_15__.
    enough (Hnext : P j_14__).
    { destruct captures_join_points; assumption. }
    cleardefs. subst j_14__ P. cleardefs.
    eapply RevStateInvariant_bind; only 1: (apply addExit_all_WellScopedVar; exact Hcapt).
    intros v. apply RevStateInvariant_return. intros Hv.
    apply WellScoped_mkVarApps; only 1: exact Hv.
    subst abs_vars.
    eapply Forall_impl.
    * intros v' Hv'. apply (weaken (isvsp_extended_WF _) (isvsp'_extended_WF _) (isvsp_to_isvsp'_extended _)). exact Hv'.
    * subst _go0 zap0. fold zap. fold pick. simpl.
      rewrite Foldable.hs_coq_foldr_list. apply WellScopedVar_picked; try solve [exit_inv]. exact Hcapt.
  Qed.

  Lemma go_res_WellScoped_on : forall captured ann_e,
    GoDom (deAnnotate ann_e) ->
    Forall GoodLocalVar captured ->
    WellScoped (deAnnotate ann_e) (extendVarSetList isvsp captured) ->
    RevStateInvariant (sublistOf exits) (go captured ann_e)
      (fun e' => WellScoped e' (extendVarSetList isvsp' captured)).
  Proof using Type pairs_WS pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    refine (go_ind_on (fun captured ann_e r =>
      Forall GoodLocalVar captured ->
      WellScoped (deAnnotate ann_e) (extendVarSetList isvsp captured) ->
      RevStateInvariant (sublistOf exits) r
        (fun e' => WellScoped e' (extendVarSetList isvsp' captured))) _).
    intros captured ann_e Hdom IH Hcapt HWS.
    cbv beta delta [go_f]. unfold CoreBndr, Id in *.
    unfold dVarSetToVarSet.
    destruct (disjointVarSet (exprFreeVars (deAnnotate ann_e)) recursive_calls).
    { apply go_exit_res_WellScoped; [|exact HWS].
      eapply Forall_impl; only 2: exact Hcapt. intros v Hv. exact (proj1 Hv). }
    destruct ann_e as [f a]. destruct a; simpl in *;
      try solve [apply RevStateInvariant_return;
        apply (weaken (isvsp_extended_WF _) (isvsp'_extended_WF _) (isvsp_to_isvsp'_extended _)); exact HWS].
    - destruct HWS as [Hscrut [Hgood Halts]].
      inversion Hdom; subst.
      rewrite Forall'_Forall, hs_coq_map, Forall_map, Forall_forall in Halts.
      match goal with H : Forall _ (Base.map _ l) |- _ =>
        rewrite hs_coq_map, Forall_map, Forall_forall in H;
        rename H into Hdomalts end.
      eapply RevStateInvariant_bind.
      + apply RevStateInvariant_forM with
          (R := fun alt => WellScopedAlt v alt (extendVarSetList isvsp' captured)).
        intros [dc pats rhs] HIn.
        eapply RevStateInvariant_bind.
        * apply IH.
          -- exact (Hdomalts _ HIn).
          -- eapply CoreLT_case_alts. rewrite hs_coq_map, in_map_iff.
             exists (Mk_AnnAlt dc pats rhs). split; [reflexivity|exact HIn].
          -- rewrite Forall_app. split; [exact Hcapt|].
             constructor; [exact Hgood|exact (proj1 (Halts _ HIn))].
          -- rewrite extendVarSetList_append. exact (proj2 (Halts _ HIn)).
        * intros rhs'. apply RevStateInvariant_return. intro Hrhs'.
          split; [exact (proj1 (Halts _ HIn))|].
          rewrite extendVarSetList_append in Hrhs'. exact Hrhs'.
      + intros alts'. apply RevStateInvariant_return. intros Halts'.
        simpl. split; [|split].
        * apply (weaken (isvsp_extended_WF _) (isvsp'_extended_WF _) (isvsp_to_isvsp'_extended _)). exact Hscrut.
        * exact Hgood.
        * rewrite Forall'_Forall. exact Halts'.
    - destruct a as [j rhs|aps]; simpl in *.
      + rewrite idJoinPointHood_isJoinId_maybe.
        inversion Hdom; subst.
        * match goal with H : GoDom_JoinPair _ _ |- _ => inversion H; subst end.
          unfold CoreBndr, Id in *. rewrite H0. simpl.
          pose proof (collectNAnnBndrs_mkLams_collectNBinders _ _ _ H) as HC.
          unfold CoreBndr, Id in HC.
          destruct (collectNAnnBndrs (length params) rhs) as [ps body] eqn:HE.
          simpl in HC. destruct HC as [Eps Ebody]. subst ps.
          destruct HWS as [[Hgood Hrhs] Hbody].
          rewrite <- H, WellScoped_mkLams in Hrhs.
          eapply RevStateInvariant_bind.
          -- apply IH.
             ++ rewrite Ebody. exact H4.
             ++ rewrite Ebody. rewrite <- H. Core_termination.
             ++ rewrite Forall_app. split; [exact Hcapt|exact (proj1 Hrhs)].
             ++ rewrite Ebody, extendVarSetList_append. exact (proj2 Hrhs).
          -- intros rhs'. eapply RevStateInvariant_bind.
             ++ apply IH.
                ** exact H3.
                ** Core_termination.
                ** rewrite Forall_app. split; [exact Hcapt|].
                   constructor; [exact Hgood|constructor].
                ** rewrite extendVarSetList_append. exact Hbody.
             ++ intros body'. apply RevStateInvariant_return. intros Hb Hr.
                simpl. split; [split|].
                ** exact Hgood.
                ** rewrite WellScoped_mkLams. split; [exact (proj1 Hrhs)|].
                   rewrite extendVarSetList_append in Hr. exact Hr.
                ** rewrite extendVarSetList_append, extendVarSetList_cons,
                     extendVarSetList_nil in Hb. exact Hb.
        * match goal with H : GoDom_Pair _ _ |- _ => inversion H; subst end.
          match goal with H : isJoinId_maybe j = None |- _ => rewrite H end. simpl.
          destruct HWS as [[Hgood Hrhs] Hbody].
          eapply RevStateInvariant_bind.
          -- apply IH.
             ++ exact H3.
             ++ Core_termination.
             ++ rewrite Forall_app. split; [exact Hcapt|].
                constructor; [exact Hgood|constructor].
             ++ rewrite extendVarSetList_append. exact Hbody.
          -- intros body'. apply RevStateInvariant_return. intro Hb.
             simpl. split; [split|].
             ++ exact Hgood.
             ++ apply (weaken (isvsp_extended_WF _) (isvsp'_extended_WF _) (isvsp_to_isvsp'_extended _)). exact Hrhs.
             ++ rewrite extendVarSetList_append, extendVarSetList_cons,
                  extendVarSetList_nil in Hb. exact Hb.
      + repeat rewrite flat_map_unpack_cons_f in *.
        rewrite !hs_coq_map in *.
        assert (Efst : map fst
          (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps) = map fst aps).
        { rewrite map_map. apply map_ext. intros [v rhs]. reflexivity. }
        change (GoDom (Let (Rec (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))
          (deAnnotate p))) in Hdom.
        change ((Forall (fun q => GoodLocalVar (fst q))
            (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps) /\
          NoDup (map varUnique (map fst
            (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))) /\
          Forall' (fun q => WellScoped (snd q)
            (extendVarSetList (extendVarSetList isvsp captured)
              (map fst (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))))
            (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps)) /\
          WellScoped (deAnnotate p)
            (extendVarSetList (extendVarSetList isvsp captured)
              (map fst (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps)))) in HWS.
        rewrite Efst in HWS.
        destruct HWS as [[Hgood [Hnodup Hrhss]] Hbody].
        rewrite Forall_map, Forall_forall in Hgood.
        rewrite Forall'_Forall, Forall_map, Forall_forall in Hrhss.
        inversion Hdom; subst.
        * assert (Hjoin : isJoinId (Tuple.fst (Err.head aps)) = true).
          { eapply GoDom_JoinPair_head_isJoinId with (erase := @deAnnotate Var FVAnn).
            - intro Hnil. subst aps. apply H2. reflexivity.
            - exact H1. }
          rewrite Hjoin. eapply RevStateInvariant_bind.
          -- apply RevStateInvariant_forM2 with
               (R := fun q q' => fst q = fst q' /\
                 WellScoped (snd q') (extendVarSetList
                   (extendVarSetList isvsp' captured) (map fst aps))).
             intros [j rhs] HIn.
             rewrite Forall_map, Forall_forall in H1.
             specialize (H1 _ HIn). simpl in H1. inversion H1; subst.
             erewrite idJoinArity_join by eassumption.
             pose proof (collectNAnnBndrs_mkLams_collectNBinders _ _ _ H) as HC.
             unfold CoreBndr, Id in *.
             destruct (collectNAnnBndrs (length params) rhs) as [ps body] eqn:HE.
             simpl in HC. destruct HC as [Eps Ebody]. subst ps.
             eapply RevStateInvariant_bind.
             ++ apply IH.
                ** rewrite Ebody. assumption.
                ** rewrite Ebody. eapply CoreLT_let_pairs_mkLam with (vs := params).
                   rewrite in_map_iff. exists (j,rhs).
                   split; [simpl; f_equal; symmetry; exact H|exact HIn].
                ** rewrite !Forall_app. split; [exact Hcapt|]. split.
                   --- rewrite Forall_map, Forall_forall. intros [v rhs'] Hin.
                       exact (Hgood _ Hin).
                   --- specialize (Hrhss _ HIn). simpl in Hrhss.
                       rewrite <- H, WellScoped_mkLams in Hrhss. exact (proj1 Hrhss).
                ** rewrite Ebody, !extendVarSetList_append.
                   specialize (Hrhss _ HIn). simpl in Hrhss.
                   rewrite <- H, WellScoped_mkLams in Hrhss. exact (proj2 Hrhss).
             ++ intros rhs'. apply RevStateInvariant_return. intros Hr.
                simpl. split; [reflexivity|]. rewrite WellScoped_mkLams.
                split.
                ** specialize (Hrhss _ HIn). simpl in Hrhss.
                   rewrite <- H, WellScoped_mkLams in Hrhss. exact (proj1 Hrhss).
                ** rewrite !extendVarSetList_append in Hr. exact Hr.
          -- intros ps. eapply RevStateInvariant_bind.
             ++ apply IH.
                ** assumption.
                ** Core_termination.
                ** rewrite Forall_app. split; [exact Hcapt|].
                   rewrite Forall_map, Forall_forall. intros [v rhs'] Hin. exact (Hgood _ Hin).
                ** rewrite extendVarSetList_append. exact Hbody.
             ++ intros body'. apply RevStateInvariant_return. intros Hb Hps.
                apply Forall2_and in Hps. destruct Hps as [Hfst Hps].
                apply Forall2_const_Forall in Hps.
                eapply Forall2_eq with (f := fst) (g := fst) in Hfst.
                simpl. rewrite bindersOf_Rec_cleanup.
                cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
                rewrite <- Hfst.
                split; [split; [|split]|].
                ** rewrite <- Forall_map, <- Hfst, Forall_map, Forall_forall.
                   intros [v rhs'] Hin. exact (Hgood _ Hin).
                ** exact Hnodup.
                ** rewrite Forall'_Forall. exact Hps.
                ** rewrite extendVarSetList_append in Hb. exact Hb.
        * assert (Hjoin : isJoinId (Tuple.fst (Err.head aps)) = false).
          { eapply GoDom_Pair_head_not_isJoinId with (erase := @deAnnotate Var FVAnn).
            - intro Hnil. subst aps. apply H2. reflexivity.
            - exact H1. }
          rewrite Hjoin.
          assert (Ebinders : map (fun '(x,_) => x)
            (map (fun '(x,y) => (x,deAnnotate y)) aps) = map fst aps).
          { rewrite map_map. apply map_ext. intros [v rhs]. reflexivity. }
          change (RevStateInvariant (sublistOf exits)
            (go (captured ++ map (fun '(x,_) => x)
                (map (fun '(x,y) => (x,deAnnotate y)) aps)) p >>=
              (fun body' => return_ (Let
                (Rec (map (fun '(x,y) => (x,deAnnotate y)) aps)) body')))
            (fun e' => WellScoped e' (extendVarSetList isvsp' captured))).
          rewrite Ebinders. eapply RevStateInvariant_bind.
          -- apply IH.
             ++ exact H3.
             ++ Core_termination.
             ++ rewrite Forall_app. split; [exact Hcapt|].
                rewrite Forall_map, Forall_forall. intros [v rhs'] Hin. exact (Hgood _ Hin).
             ++ rewrite extendVarSetList_append. exact Hbody.
          -- intros body'. apply RevStateInvariant_return. intro Hb.
             simpl. rewrite bindersOf_Rec_cleanup.
             cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
             rewrite Efst.
             split; [split; [|split]|].
             ++ rewrite Forall_map, Forall_forall. exact Hgood.
             ++ exact Hnodup.
             ++ rewrite Forall'_Forall, Forall_map, Forall_forall.
                intros [v rhs'] Hin.
                assert (Hscope : StrongSubset
                  (extendVarSetList (extendVarSetList isvsp captured) (map fst aps))
                  (extendVarSetList (extendVarSetList isvsp' captured) (map fst aps))).
                { apply StrongSubset_extendVarSetList; try solve [exit_inv].
                  apply isvsp_to_isvsp'_extended. }
                apply (exit_weaken Hscope); try solve [exit_inv].
                exact (Hrhss _ Hin).
             ++ rewrite extendVarSetList_append in Hb. exact Hb.
  Qed.

  Lemma pairs'_WS : Forall (fun p => WellScoped (snd p) isvsp') pairs'.
  Proof using Type pairs_WS pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    unfold pairs', pairs'_exits, ann_pairs, GHC.Prim.rightSection.
    eapply RevStateInvariant_runState with (P := sublistOf exits).
    * rewrite hs_coq_map, forM_map. apply RevStateInvariant_forM.
      intros [v e] HIn.
      assert (Hdom : GoDom_JoinPair v e).
      { eapply isValidJoinPointsPair_GoDom_JoinPair.
        rewrite Forall_forall in pairs_VJPP. exact (pairs_VJPP _ HIn). }
      inversion Hdom; subst.
      simpl. erewrite idJoinArity_join by eassumption.
      rewrite collectNAnnBndrs_freeVars_mkLams.
      pose proof pairs_WS as HW.
      rewrite Forall_forall in HW. specialize (HW _ HIn). simpl in HW.
      rewrite WellScoped_mkLams in HW.
      eapply RevStateInvariant_bind.
      - apply go_res_WellScoped_on.
        + rewrite deAnnotate_freeVars. assumption.
        + exact (proj1 (proj2 HW)).
        + rewrite deAnnotate_freeVars. exact (proj2 (proj2 HW)).
      - intros e'. apply RevStateInvariant_return. intro He'.
        simpl. rewrite WellScoped_mkLams. split; [exact (proj1 (proj2 HW))|exact He'].
    * change (sublistOf exits exits). intros x HIn. exact HIn.
  Qed.

  Lemma map_fst_pairs' : map (@fst CoreBndr CoreExpr) pairs' = fs.
  Proof.
    clear pairs_WS pairs_VJPP pairs_NoDup jps_subset_isvs.
    assert (HR : RevStateInvariant (fun _ => True)
      (Traversable.forM ann_pairs (fun '(x,rhs) =>
        let '(args,body) := collectNAnnBndrs (idJoinArity x) rhs in
        go args body >>= (fun body' => return_ (x,mkLams args body'))))
      (Forall2 (fun p p' => fst p = fst p') ann_pairs)).
    { apply RevStateInvariant_forM2. intros [v rhs] HIn.
      destruct (collectNAnnBndrs (idJoinArity v) rhs) as [args body].
      eapply RevStateInvariant_bind with (Q := fun _ => True).
      - intros s _. split; exact I.
      - intros body'. apply RevStateInvariant_return. intros _. reflexivity. }
    assert (Hrel : Forall2 (fun p p' => fst p = fst p') ann_pairs pairs').
    { unfold pairs', pairs'_exits, GHC.Prim.rightSection.
      eapply RevStateInvariant_runState; [exact HR|exact I]. }
    apply Forall2_eq in Hrel.
    cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
    rewrite <- Hrel.
    unfold ann_pairs, fs. rewrite hs_coq_map, map_map.
    apply map_ext. intros [v rhs]. reflexivity.
  Qed.

  Theorem exitifyRec_WellScoped:
    forall body,
    WellScoped body (extendVarSetList (isvs) fs) ->
    WellScoped (mkLets (exitifyRec (extendInScopeSetList in_scope fs) pairs) body) (isvs).
  Proof using Type pairs_WS pairs_VJPP pairs_NoDup isvs_WF isvs_valid jps_WF jps_valid.
    intros body Hbody.
    cbv beta delta [exitifyRec].
    zeta_with go_exit. zeta_with recursive_calls. zeta_with go. zeta_with ann_pairs.
    fold pairs'_exits. expand_pairs. fold pairs'. fold exits.
    rewrite flat_map_unpack_cons_f.
    change (WellScoped (mkLets
      (map (fun '(v,rhs) => NonRec v rhs) exits ++ [Rec pairs']) body) isvs).
    rewrite mkLets_append, mkLets_cons, mkLets_nil.
    apply mkLets_WellScoped.
    * rewrite WellScoped_MkLet. simpl.
      cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
      pose proof map_fst_pairs' as Hfst.
      cbv beta delta [CoreExpr JoinId Id CoreBndr] in Hfst.
      rewrite bindersOf_Rec_cleanup, Hfst. split; [split; [|split]|].
      - rewrite <- Forall_map, Hfst. unfold fs. rewrite Forall_map.
        eapply Forall_impl; only 2: exact pairs_WS.
        intros [v rhs] H. exact (proj1 H).
      - exact pairs_NoDup.
      - rewrite Forall'_Forall. exact pairs'_WS.
      - apply (exit_weaken isvsp_to_isvsp'); try solve [exit_inv]. exact Hbody.
    * exact all_exits_WellScoped.
  Qed.

  Lemma isJoinId_maybe_uniqAway : forall s v,
    isJoinId_maybe (uniqAway s v) = isJoinId_maybe v.
  Proof.
    intros s v. pose proof (idJoinPointHood_uniqAway s v) as H.
    rewrite !idJoinPointHood_isJoinId_maybe in H.
    destruct (isJoinId_maybe (uniqAway s v)), (isJoinId_maybe v); congruence.
  Qed.

  Lemma isJoinId_maybe_asJoinId : forall v n,
    isJoinId_maybe (asJoinId v n) = Some n.
  Proof. intros [nm u ty w sc d info] n. reflexivity. Qed.

  Lemma addExit_all_joinIds : forall jps0 captured ja e,
    isJoinRHS e ja jps0 = true ->
    StateInvariant (fun xs => forallb (fun '(v,rhs) =>
      isValidJoinPointsPair v rhs jps0) xs = true)
      (addExit (extendInScopeSetList in_scope2 captured) ja e).
  Proof.
    intros jps0 captured ja e He.
    unfold addExit, mkExitJoinId, StateInvariant, SP, State.runState.
    cbn -[asJoinId mkSysLocal uniqAway isValidJoinPointsPair].
    intros floats Hfloats. split; [|exact I].
    rewrite andb_true_iff. split; [|exact Hfloats].
    unfold isValidJoinPointsPair.
    rewrite isJoinId_maybe_uniqAway, isJoinId_maybe_asJoinId. exact He.
  Qed.

  Lemma isJoinPointsValid_picked_aux : forall jps0 captured e vs,
    WF jps0 ->
    isJoinPointsValid e 0 (updJPSs jps0 (captured ++ vs)) = true ->
    let abs_vars := snd (fold_right pick (delVarSetList (exprFreeVars e) vs,[]) captured) in
    forallb (fun x => negb (isJoinId x)) abs_vars = true ->
    isJoinPointsValid e 0 (updJPSs (delVarSetList jps0 abs_vars) vs) = true.
  Proof.
    clear pairs_WS pairs_VJPP pairs_NoDup jps_subset_isvs.
    intros jps0 captured e. induction captured using rev_ind;
      intros vs W Hvalid abs_vars Hnot.
    * subst abs_vars. simpl. rewrite delVarSetList_nil. exact Hvalid.
    * subst abs_vars. rewrite fold_right_app in *. simpl in *.
      destruct_match; simpl.
      + rewrite snd_pick_list in *.
        rewrite forallb_app in Hnot. simpl_bool. destruct Hnot as [Hnot Hnotx].
        simpl in Hnotx. simpl_bool. rewrite negb_true_iff in Hnotx.
        rewrite delVarSetList_app, delVarSetList_cons, delVarSetList_nil.
        erewrite delVarSet_ae by (apply almostEqual_sym; apply zap_ae).
        erewrite isJoinId_ae in Hnotx by (apply almostEqual_sym; apply zap_ae).
        rewrite <- updJPS_not_joinId by exact Hnotx.
        rewrite <- updJPSs_cons.
        assert (E : snd (fold_right pick (delVarSet (delVarSetList (exprFreeVars e) vs) x,[]) captured) =
          snd (fold_right pick (delVarSetList (exprFreeVars e) (x :: vs),[]) captured)).
        { apply snd_m. apply fold_right_m; try solve [solve_varset_inv].
          split; [symmetry; apply delVarSetList_cons2; solve_varset_inv|reflexivity]. }
        rewrite E in *. apply IHcaptured; [exact W| |].
        - rewrite <- app_assoc in Hvalid. exact Hvalid.
        - exact Hnot.
      + apply IHcaptured; [exact W| |].
        - rewrite isJoinPointsValid_fresh_between in Hvalid; try exact W; [exact Hvalid|].
          apply disjointVarSet_mkVarSet; try solve [solve_varset_inv]. constructor; [assumption|constructor].
        - exact Hnot.
  Qed.

  Lemma isJoinPointsValid_picked : forall jps0 captured e,
    WF jps0 ->
    isJoinPointsValid e 0 (updJPSs jps0 captured) = true ->
    let abs_vars := snd (fold_right pick (exprFreeVars e,[]) captured) in
    forallb (fun x => negb (isJoinId x)) abs_vars = true ->
    isJoinPointsValid e 0 (delVarSetList jps0 abs_vars) = true.
  Proof.
    intros jps0 captured e W Hvalid abs_vars Hnot.
    pose proof (isJoinPointsValid_picked_aux jps0 captured e []) as H.
    rewrite app_nil_r, delVarSetList_nil in H.
    specialize (H W Hvalid Hnot). rewrite updJPSs_nil in H. exact H.
  Qed.

  Lemma go_exit_all_ValidJoinPairs captured e :
    isJoinPointsValid e 0 (updJPSs jpsp captured) = true ->
    disjointVarSet (exprFreeVars e) recursive_calls = true ->
    StateInvariant (fun xs => forallb (fun '(v,rhs) =>
      isValidJoinPointsPair v rhs jps) xs = true)
      (go_exit captured e (exprFreeVars e)).
  Proof.
    intros Hvalid Hdisjoint.
    set (P := fun xs => forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps) xs = true).
    cbv beta delta [go_exit]. repeat float_let.
    enough (Hnext : StateInvariant P j_16__).
    { clearbody j_16__; cleardefs. subst _go3.
      destruct (collectArgs _) as [rhs args]. destruct rhs; try exact Hnext.
      destruct (isJoinId i && Foldable.all isCapturedVarArg args);
        [apply StateInvariant_return|exact Hnext]. }
    cleardefs. subst j_16__.
    enough (Hnext : StateInvariant P j_15__).
    { subst _go2. destruct (negb is_interesting); [apply StateInvariant_return|exact Hnext]. }
    cleardefs. subst j_15__.
    enough (Hnext : captures_join_points = false -> StateInvariant P j_14__).
    { destruct captures_join_points; [apply StateInvariant_return|apply Hnext; reflexivity]. }
    cleardefs. subst j_14__. intros Hnot.
    unfold recursive_calls in Hdisjoint. subst captures_join_points.
    rewrite HSUtil.Foldable_any_existsb, existsb_false_iff_forallb in Hnot.
    apply StateInvariant_bind_return. apply addExit_all_joinIds.
    apply isJoinRHS_mkLams.
    * rewrite Forall_forall. rewrite forallb_forall in Hnot.
      intros v Hin. specialize (Hnot _ Hin). rewrite negb_true_iff in Hnot. exact Hnot.
    * apply isJoinPointsValid_picked; [exit_inv| |].
      - unfold jpsp in Hvalid. rewrite <- updJPSs_append in Hvalid.
        erewrite <- isJoinPointsValid_fresh_updJPSs; try solve [exit_inv]; only 1: exact Hvalid.
        eapply disjointVarSet_subVarSet_l with (t := exprFreeVars e); try solve [exit_inv]; only 1: exact Hdisjoint.
        apply subVarSet_delVarSetList; exit_inv.
      - exact Hnot.
  Qed.

  Lemma go_all_ValidJoinPairs_on : forall captured ann_e,
    GoDom (deAnnotate ann_e) ->
    isJoinPointsValid (deAnnotate ann_e) 0 (updJPSs jpsp captured) = true ->
    StateInvariant (fun xs => forallb (fun '(v,rhs) =>
      isValidJoinPointsPair v rhs jps) xs = true) (go captured ann_e).
  Proof.
    clear pairs_WS pairs_VJPP pairs_NoDup jps_subset_isvs.
    refine (go_ind_on (fun captured ann_e r =>
      isJoinPointsValid (deAnnotate ann_e) 0 (updJPSs jpsp captured) = true ->
      StateInvariant (fun xs => forallb (fun '(v,rhs) =>
        isValidJoinPointsPair v rhs jps) xs = true) r) _).
    intros captured ann_e Hdom IH Hvalid.
    cbv beta delta [go_f]. cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
    unfold dVarSetToVarSet.
    destruct (disjointVarSet (exprFreeVars (deAnnotate ann_e)) recursive_calls) eqn:Hd.
    { apply go_exit_all_ValidJoinPairs; assumption. }
    destruct ann_e as [f a]. destruct a; simpl in *;
      try apply StateInvariant_return.
    - simpl_bool. destruct Hvalid as [[Hnot Hscrut] Halts].
      inversion Hdom; subst.
      rewrite hs_coq_map, forallb_forall in Halts.
      rewrite <- Forall_forall, Forall_map, Forall_forall in Halts.
      match goal with H : Forall _ (Base.map _ l) |- _ =>
        rewrite hs_coq_map, Forall_map, Forall_forall in H;
        rename H into Hdomalts end.
      apply StateInvariant_bind_return. apply StateInvariant_forM.
      intros [dc pats rhs] HIn. apply StateInvariant_bind_return. apply IH.
      + exact (Hdomalts _ HIn).
      + eapply CoreLT_case_alts. rewrite hs_coq_map, in_map_iff.
        exists (Mk_AnnAlt dc pats rhs). split; [reflexivity|exact HIn].
      + specialize (Halts _ HIn). simpl in Halts. simpl_bool.
        destruct Halts as [Hpats Hr].
        rewrite updJPSs_append, updJPSs_cons.
        rewrite updJPSs_not_joinId by exact Hpats.
        rewrite negb_true_iff in Hnot. rewrite updJPS_not_joinId by exact Hnot.
        exact Hr.
    - destruct a as [j rhs|aps]; simpl in *.
      + rewrite idJoinPointHood_isJoinId_maybe.
        simpl_bool. destruct Hvalid as [Hpair Hbody].
        fold isJoinPointsValidPair in Hpair.
        inversion Hdom; subst.
        * match goal with H : GoDom_JoinPair _ _ |- _ => inversion H; subst end.
          cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
          rewrite H0. simpl.
          pose proof (collectNAnnBndrs_mkLams_collectNBinders _ _ _ H) as HC.
          cbv beta delta [CoreExpr JoinId Id CoreBndr] in HC.
          destruct (collectNAnnBndrs (length params) rhs) as [ps body] eqn:HE.
          simpl in HC. destruct HC as [Eps Ebody]. subst ps.
          eapply StateInvariant_bind.
          -- apply IH.
             ++ rewrite Ebody. exact H4.
             ++ rewrite Ebody, <- H. Core_termination.
             ++ rewrite Ebody, updJPSs_append.
                rewrite <- H in Hpair.
                rewrite isJoinPointsValidPair_isJoinRHS in Hpair by exact H0.
                exact (proj2 (isJoinRHS_mkLams2 _ _ _ Hpair)).
          -- intros rhs'. apply StateInvariant_bind_return. apply IH.
             ++ exact H3.
             ++ Core_termination.
             ++ rewrite updJPSs_append, updJPSs_cons, updJPSs_nil. exact Hbody.
        * match goal with H : GoDom_Pair _ _ |- _ => inversion H; subst end.
          match goal with H : isJoinId_maybe j = None |- _ => rewrite H end. simpl.
          apply StateInvariant_bind_return. apply IH.
          -- exact H3.
          -- Core_termination.
          -- rewrite updJPSs_append, updJPSs_cons, updJPSs_nil. exact Hbody.
      + repeat rewrite flat_map_unpack_cons_f in *.
        rewrite !hs_coq_map in *.
        simpl_bool. destruct Hvalid as [[Hne Hall] [Hpairs Hbody]].
        fold isJoinPointsValidPair in Hpairs.
        assert (Efst : map fst
          (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps) = map fst aps).
        { rewrite map_map. apply map_ext. intros [v rhs]. reflexivity. }
        change (GoDom (Let (Rec (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))
          (deAnnotate p))) in Hdom.
        inversion Hdom; subst.
        * assert (Hjoin : isJoinId (Tuple.fst (Err.head aps)) = true).
          { eapply GoDom_JoinPair_head_isJoinId with (erase := @deAnnotate Var FVAnn).
            - intro Hnil. subst aps. apply H2. reflexivity.
            - exact H1. }
          rewrite Hjoin. apply StateInvariant_bind.
          -- apply StateInvariant_forM. intros [j rhs] HIn.
             rewrite Forall_map, Forall_forall in H1.
             specialize (H1 _ HIn). simpl in H1. inversion H1; subst.
             erewrite idJoinArity_join by eassumption.
             pose proof (collectNAnnBndrs_mkLams_collectNBinders _ _ _ H) as HC.
             cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
             destruct (collectNAnnBndrs (length params) rhs) as [ps body] eqn:HE.
             simpl in HC. destruct HC as [Eps Ebody]. subst ps.
             apply StateInvariant_bind_return. apply IH.
             ++ rewrite Ebody. assumption.
             ++ rewrite Ebody. eapply CoreLT_let_pairs_mkLam with (vs := params).
                rewrite in_map_iff. exists (j,rhs).
                split; [simpl; f_equal; symmetry; exact H|exact HIn].
             ++ rewrite Ebody, !updJPSs_append.
                rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall in Hpairs.
                specialize (Hpairs _ HIn). simpl in Hpairs.
                change (isJoinPointsValidPair j (deAnnotate rhs)
                  (updJPSs (updJPSs jpsp captured)
                    (map fst (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))) = true) in Hpairs.
                rewrite Efst in Hpairs. rewrite <- H in Hpairs.
                rewrite isJoinPointsValidPair_isJoinRHS in Hpairs by exact H0.
                exact (proj2 (isJoinRHS_mkLams2 _ _ _ Hpairs)).
          -- intros ps. apply StateInvariant_bind_return. apply IH.
             ++ exact H3.
             ++ Core_termination.
             ++ rewrite updJPSs_append.
                change (isJoinPointsValid (deAnnotate p) 0
                  (updJPSs (updJPSs jpsp captured)
                    (map fst (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))) = true) in Hbody.
                rewrite Efst in Hbody. exact Hbody.
        * assert (Hjoin : isJoinId (Tuple.fst (Err.head aps)) = false).
          { eapply GoDom_Pair_head_not_isJoinId with (erase := @deAnnotate Var FVAnn).
            - intro Hnil. subst aps. apply H2. reflexivity.
            - exact H1. }
          rewrite Hjoin. apply StateInvariant_bind_return. apply IH.
          -- exact H3.
          -- Core_termination.
          -- rewrite updJPSs_append. exact Hbody.
  Qed.

  Lemma all_exits_ValidJoinPairs :
    forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps) exits = true.
  Proof using Type pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    unfold exits, pairs'_exits, ann_pairs, GHC.Prim.rightSection.
    rewrite hs_coq_map, forM_map. eapply SP_snd_runState.
    * apply StateInvariant_forM. intros [v e] HIn.
      pose proof pairs_VJPP as HP.
      rewrite Forall_forall in HP. specialize (HP _ HIn). simpl in HP.
      pose proof (isValidJoinPointsPair_GoDom_JoinPair _ _ _ HP) as HD.
      inversion HD; subst. simpl.
      erewrite idJoinArity_join by eassumption.
      rewrite collectNAnnBndrs_freeVars_mkLams.
      apply StateInvariant_bind_return. apply go_all_ValidJoinPairs_on.
      - rewrite deAnnotate_freeVars. assumption.
      - rewrite deAnnotate_freeVars. unfold isValidJoinPointsPair in HP.
         match goal with H : isJoinId_maybe _ = Some _ |- _ => rewrite H in HP end.
         exact (proj2 (isJoinRHS_mkLams2 _ _ _ HP)).
    * reflexivity.
  Qed.

  Lemma all_exits_isJoinId : forallb isJoinId (map fst exits) = true.
  Proof using Type pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall.
    intros [v rhs] Hin. pose proof all_exits_ValidJoinPairs as H.
    rewrite forallb_forall in H. specialize (H _ Hin).
    exact (isValidJoinPointsPair_isJoinId _ _ _ H).
  Qed.

  Lemma jps_to_jps' : StrongSubset jps jps'.
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs isvs_WF isvs_valid jps_WF jps_valid.
    apply StrongSubset_updJPSs_fresh; try solve [exit_inv].
    eapply disjointVarSet_subVarSet_l with (t := isvs); try solve [exit_inv]; [exact disjoint_isvs_exits|exact jps_subset_isvs].
  Qed.

  Lemma jpsp_to_jpsp' : StrongSubset jpsp jpsp'.
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs isvs_WF isvs_valid jps_WF jps_valid.
    apply StrongSubset_updJPSs; try solve [exit_inv]. exact jps_to_jps'.
  Qed.

  Lemma jpsp_to_jpsp'_extended : forall vs,
    StrongSubset (updJPSs jpsp vs) (updJPSs jpsp' vs).
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs isvs_WF isvs_valid jps_WF jps_valid.
    intros vs. apply StrongSubset_updJPSs; try solve [exit_inv]. exact jpsp_to_jpsp'.
  Qed.

  Lemma addExit_isJoinPointsValid : forall captured ja e,
    RevStateInvariant (sublistOf exits)
      (addExit (extendInScopeSetList in_scope2 captured) ja e)
      (fun v => isJoinPointsValid (Mk_Var v) ja (updJPSs jpsp' captured) = true).
  Proof using Type pairs_VJPP isvs_WF isvs_valid jps_WF jps_valid.
    intros captured ja e.
    unfold addExit, mkExitJoinId, RevStateInvariant, State.runState.
    cbn -[asJoinId mkSysLocal uniqAway isJoinPointsValid].
    intros floats Hfloats. set (v := uniqAway _ _) in *.
    apply sublistOf_cons in Hfloats. destruct Hfloats as [Hin Hsub].
    apply in_map with (f := fst) in Hin. simpl in Hin.
    split; [exact Hsub|].
    change (match isJoinId_maybe v with
      | Some ar => (isLocalVar v && (ar <=? ja)) && elemVarSet v (updJPSs jpsp' captured)
      | None => true end = true).
    assert (Hjoin : isJoinId_maybe v = Some ja).
    { subst v. rewrite isJoinId_maybe_uniqAway, isJoinId_maybe_asJoinId. reflexivity. }
    rewrite Hjoin, Nat.leb_refl, andb_true_r. rewrite andb_true_iff. split.
    * subst v. rewrite isLocalVar_uniqAway.
      apply (proj2 (GoodLocalVar_asJoinId_mkSysLocal _ _ _ _ _
        isLocalUnique_initExitJoinUnique)).
    * unfold jpsp', jps'.
      apply elemVarSet_updJPSs_l; try solve [exit_inv]; only 1: (apply elemVarSet_updJPSs_l; try solve [exit_inv]).
      - rewrite updJPSs_joinId by exact all_exits_isJoinId.
        apply elemVarSet_extendVarSetList_r; try solve [exit_inv].
        apply elemVarSet_mkVarset_iff_In. rewrite hs_coq_map. apply in_map. exact Hin.
      - subst v. apply elemVarSet_uniqAway; try solve [exit_inv]. unfold in_scope2.
        rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
        apply subVarSet_extendVarSet; try solve [exit_inv]. apply subVarSet_extendVarSetList_l; try solve [exit_inv].
        apply subVarSet_extendVarSetList_l; try solve [exit_inv]. apply subVarSet_extendVarSetList_r; try solve [exit_inv].
        apply subVarSet_refl; exit_inv.
      - subst v. apply elemVarSet_uniqAway; try solve [exit_inv]. unfold in_scope2.
        rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
        apply subVarSet_extendVarSet; try solve [exit_inv]. apply subVarSet_extendVarSetList_l; try solve [exit_inv].
        apply subVarSet_extendVarSetList_r; try solve [exit_inv]. apply subVarSet_refl; exit_inv.
  Qed.

  Lemma go_exit_res_isJoinPointsValid captured e :
    isJoinPointsValid e 0 (updJPSs jpsp captured) = true ->
    RevStateInvariant (sublistOf exits) (go_exit captured e (exprFreeVars e))
      (fun e' => isJoinPointsValid e' 0 (updJPSs jpsp' captured) = true).
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs isvs_WF isvs_valid jps_WF jps_valid.
    intros Hvalid.
    set (P := fun act => RevStateInvariant (sublistOf exits) act
      (fun e' => isJoinPointsValid e' 0 (updJPSs jpsp' captured) = true)).
    change (P (go_exit captured e (exprFreeVars e))).
    cbv beta delta [go_exit]. repeat float_let.
    assert (Hreturn : P (return_ e)).
    { apply RevStateInvariant_return.
      apply (exit_weakenb (jpsp_to_jpsp'_extended _)); try solve [exit_inv]. exact Hvalid. }
    enough (Hnext : P j_16__).
    { clearbody j_16__; cleardefs. subst _go3.
      destruct (collectArgs _) as [rhs args]. destruct rhs; try exact Hnext.
      destruct (isJoinId i && Foldable.all isCapturedVarArg args); assumption. }
    cleardefs. subst j_16__.
    enough (Hnext : P j_15__).
    { subst _go2. destruct (negb is_interesting); assumption. }
    cleardefs. subst j_15__.
    enough (Hnext : captures_join_points = false -> P j_14__).
    { destruct captures_join_points; [exact Hreturn|apply Hnext; reflexivity]. }
    cleardefs. subst j_14__. intros Hnot.
    subst captures_join_points.
    rewrite HSUtil.Foldable_any_existsb, existsb_false_iff_forallb in Hnot.
    rewrite forallb_forall in Hnot. setoid_rewrite negb_true_iff in Hnot.
    rewrite <- Forall_forall in Hnot.
    subst P. cleardefs.
    eapply RevStateInvariant_bind; only 1: apply addExit_isJoinPointsValid.
    intros v. apply RevStateInvariant_return. intros Hv.
    apply isJoinPointsValid_mkVarApps; [exact Hnot|exact Hv].
  Qed.

  Lemma go_res_isJoinPointsValid_on : forall captured ann_e,
    GoDom (deAnnotate ann_e) ->
    isJoinPointsValid (deAnnotate ann_e) 0 (updJPSs jpsp captured) = true ->
    RevStateInvariant (sublistOf exits) (go captured ann_e)
      (fun e' => isJoinPointsValid e' 0 (updJPSs jpsp' captured) = true).
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs isvs_WF isvs_valid jps_WF jps_valid.
    refine (go_ind_on (fun captured ann_e r =>
      isJoinPointsValid (deAnnotate ann_e) 0 (updJPSs jpsp captured) = true ->
      RevStateInvariant (sublistOf exits) r
        (fun e' => isJoinPointsValid e' 0 (updJPSs jpsp' captured) = true)) _).
    intros captured ann_e Hdom IH Hvalid.
    cbv beta delta [go_f]. cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
    unfold dVarSetToVarSet.
    destruct (disjointVarSet (exprFreeVars (deAnnotate ann_e)) recursive_calls).
    { apply go_exit_res_isJoinPointsValid. exact Hvalid. }
    destruct ann_e as [f a]. destruct a; simpl in *;
      try solve [apply RevStateInvariant_return;
        apply (exit_weakenb (jpsp_to_jpsp'_extended _)); try solve [exit_inv]; exact Hvalid].
    - simpl_bool. destruct Hvalid as [[Hnot Hscrut] Halts].
      inversion Hdom; subst.
      rewrite hs_coq_map, forallb_forall, <- Forall_forall, Forall_map,
        Forall_forall in Halts.
      match goal with H : Forall _ (Base.map _ l) |- _ =>
        rewrite hs_coq_map, Forall_map, Forall_forall in H;
        rename H into Hdomalts end.
      eapply RevStateInvariant_bind.
      + apply RevStateInvariant_forM with
          (R := fun alt => isjoinPointsAlt alt (delVarSet (updJPSs jpsp' captured) v) = true).
        intros [dc pats rhs] HIn.
        pose proof (Halts _ HIn) as Halt. simpl in Halt. simpl_bool.
        destruct Halt as [Hpats Hr].
        eapply RevStateInvariant_bind.
        * apply IH.
          -- exact (Hdomalts _ HIn).
          -- eapply CoreLT_case_alts. rewrite hs_coq_map, in_map_iff.
             exists (Mk_AnnAlt dc pats rhs). split; [reflexivity|exact HIn].
          -- rewrite updJPSs_append, updJPSs_cons.
             rewrite updJPSs_not_joinId by exact Hpats.
             rewrite negb_true_iff in Hnot. rewrite updJPS_not_joinId by exact Hnot.
             exact Hr.
        * intros rhs'. apply RevStateInvariant_return. intros Hr'.
          simpl. rewrite andb_true_iff. split; [exact Hpats|].
          rewrite updJPSs_append, updJPSs_cons in Hr'.
          rewrite updJPSs_not_joinId in Hr' by exact Hpats.
          rewrite negb_true_iff in Hnot. rewrite updJPS_not_joinId in Hr' by exact Hnot.
          exact Hr'.
      + intros alts'. apply RevStateInvariant_return. intros Halts'.
        simpl. rewrite !andb_true_iff. split; [split; assumption|].
        rewrite forallb_forall, <- Forall_forall.
        eapply Forall_impl; only 2: exact Halts'. intros [dc pats rhs] H. exact H.
    - destruct a as [j rhs|aps]; simpl in *.
      + rewrite idJoinPointHood_isJoinId_maybe.
        simpl_bool. destruct Hvalid as [Hpair Hbody].
        fold isJoinPointsValidPair in Hpair.
        inversion Hdom; subst.
        * match goal with H : GoDom_JoinPair _ _ |- _ => inversion H; subst end.
          cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
          rewrite H0. simpl.
          pose proof (collectNAnnBndrs_mkLams_collectNBinders _ _ _ H) as HC.
          cbv beta delta [CoreExpr JoinId Id CoreBndr] in HC.
          destruct (collectNAnnBndrs (length params) rhs) as [ps body] eqn:HE.
          simpl in HC. destruct HC as [Eps Ebody]. subst ps.
          change (isJoinPointsValidPair j (deAnnotate rhs) (updJPSs jpsp captured) = true) in Hpair.
          change (mkLams params rhs0 = deAnnotate rhs) in H.
          rewrite <- H in Hpair.
          rewrite isJoinPointsValidPair_isJoinRHS in Hpair by exact H0.
          destruct (isJoinRHS_mkLams2 _ _ _ Hpair) as [Hnot Hrhs].
          eapply RevStateInvariant_bind.
          -- apply IH.
             ++ rewrite Ebody. exact H4.
             ++ rewrite Ebody.
                change (CoreLT rhs0 (Let (NonRec j (deAnnotate rhs)) (deAnnotate p))).
                rewrite <- H. Core_termination.
             ++ rewrite Ebody, updJPSs_append. exact Hrhs.
          -- intros rhs'. eapply RevStateInvariant_bind.
             ++ apply IH.
                ** exact H3.
                ** Core_termination.
                ** rewrite updJPSs_append, updJPSs_cons, updJPSs_nil. exact Hbody.
             ++ intros body'. apply RevStateInvariant_return. intros Hb Hr.
                simpl. fold isJoinPointsValidPair. rewrite andb_true_iff. split.
                ** rewrite isJoinPointsValidPair_isJoinRHS by exact H0.
                   apply isJoinRHS_mkLams; [exact Hnot|].
                   rewrite updJPSs_append in Hr.
                   rewrite updJPSs_not_joinId in Hr.
                   --- exact Hr.
                   --- rewrite forallb_forall, <- Forall_forall.
                       eapply Forall_impl; only 2: exact Hnot.
                       intros v Hv. rewrite negb_true_iff. exact Hv.
                ** rewrite updJPSs_append, updJPSs_cons, updJPSs_nil in Hb. exact Hb.
        * match goal with H : GoDom_Pair _ _ |- _ => inversion H; subst end.
          match goal with H : isJoinId_maybe j = None |- _ =>
            rename H into Hnon end.
          rewrite Hnon. simpl.
          eapply RevStateInvariant_bind.
          -- apply IH.
             ++ exact H3.
             ++ Core_termination.
             ++ rewrite updJPSs_append, updJPSs_cons, updJPSs_nil. exact Hbody.
          -- intros body'. apply RevStateInvariant_return. intros Hb.
             simpl. fold isJoinPointsValidPair. rewrite andb_true_iff. split.
             ++ rewrite isJoinPointsValidPair_isJoinPointsValid by exact Hnon.
                rewrite isJoinPointsValidPair_isJoinPointsValid in Hpair by exact Hnon.
                exact Hpair.
             ++ rewrite updJPSs_append, updJPSs_cons, updJPSs_nil in Hb. exact Hb.
      + repeat rewrite flat_map_unpack_cons_f in *.
        rewrite !hs_coq_map in *.
        simpl_bool. destruct Hvalid as [[Hne Hall] [Hpairs Hbody]].
        fold isJoinPointsValidPair in Hpairs.
        assert (Efst : map fst
          (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps) = map fst aps).
        { rewrite map_map. apply map_ext. intros [v rhs]. reflexivity. }
        change (GoDom (Let (Rec (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))
          (deAnnotate p))) in Hdom.
        change (isJoinPointsValid (deAnnotate p) 0
          (updJPSs (updJPSs jpsp captured)
            (map fst (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))) = true) in Hbody.
        rewrite Efst in Hbody.
        inversion Hdom; subst.
        * assert (Hjoin : isJoinId (Tuple.fst (Err.head aps)) = true).
          { eapply GoDom_JoinPair_head_isJoinId with (erase := @deAnnotate Var FVAnn).
            - intro Hnil. subst aps. apply H2. reflexivity.
            - exact H1. }
          rewrite Hjoin. eapply RevStateInvariant_bind.
          -- apply RevStateInvariant_forM2 with
               (R := fun q q' => fst q = fst q' /\
                 isValidJoinPointsPair (fst q') (snd q')
                   (updJPSs (updJPSs jpsp' captured) (map fst aps)) = true).
             intros [j rhs] HIn.
             pose proof H1 as HD.
             rewrite Forall_map, Forall_forall in HD.
             specialize (HD _ HIn). simpl in HD. inversion HD; subst.
             erewrite idJoinArity_join by eassumption.
             pose proof (collectNAnnBndrs_mkLams_collectNBinders _ _ _ H) as HC.
             cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
             destruct (collectNAnnBndrs (length params) rhs) as [ps body] eqn:HE.
             simpl in HC. destruct HC as [Eps Ebody]. subst ps.
             rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall in Hpairs.
             specialize (Hpairs _ HIn). simpl in Hpairs.
             change (isJoinPointsValidPair j (deAnnotate rhs)
               (updJPSs (updJPSs jpsp captured)
                 (map fst (map (fun '(v,rhs) => (v,deAnnotate rhs)) aps))) = true) in Hpairs.
             rewrite Efst, <- H in Hpairs.
             rewrite isJoinPointsValidPair_isJoinRHS in Hpairs by exact H0.
             destruct (isJoinRHS_mkLams2 _ _ _ Hpairs) as [Hnot Hr].
             eapply RevStateInvariant_bind.
             ++ apply IH.
                ** rewrite Ebody. assumption.
                ** rewrite Ebody. eapply CoreLT_let_pairs_mkLam with (vs := params).
                   rewrite in_map_iff. exists (j,rhs).
                   split; [simpl; f_equal; symmetry; exact H|exact HIn].
                ** rewrite Ebody, !updJPSs_append. exact Hr.
             ++ intros rhs'. apply RevStateInvariant_return. intros Hr'.
                simpl. split; [reflexivity|]. unfold isValidJoinPointsPair. rewrite H0.
                apply isJoinRHS_mkLams; [exact Hnot|].
                rewrite !updJPSs_append in Hr'.
                rewrite updJPSs_not_joinId in Hr'.
                ** exact Hr'.
                ** rewrite forallb_forall, <- Forall_forall.
                   eapply Forall_impl; only 2: exact Hnot.
                   intros v Hv. rewrite negb_true_iff. exact Hv.
          -- intros ps. eapply RevStateInvariant_bind.
             ++ apply IH.
                ** exact H3.
                ** Core_termination.
                ** rewrite updJPSs_append. exact Hbody.
             ++ intros body'. apply RevStateInvariant_return. intros Hb Hps.
                apply Forall2_and in Hps. destruct Hps as [Hfst Hps].
                apply Forall2_const_Forall in Hps.
                eapply Forall2_eq with (f := fst) (g := fst) in Hfst.
                simpl. cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
                rewrite <- Hfst. simpl_bool. repeat split.
                ** destruct aps; [simpl in H2; contradiction|].
                   destruct ps; [simpl in Hfst; discriminate|reflexivity].
                ** rewrite orb_true_iff. right.
                   rewrite forallb_forall. intros [v rhs'] Hin.
                   rewrite Forall_forall in Hps. specialize (Hps _ Hin).
                   exact (isValidJoinPointsPair_isJoinId _ _ _ Hps).
                ** rewrite forallb_forall. intros [v rhs'] Hin.
                   rewrite Forall_forall in Hps. specialize (Hps _ Hin).
                   apply isValidJoinPointsPair_isJoinPointsValidPair. exact Hps.
                ** rewrite updJPSs_append in Hb. exact Hb.
        * assert (Hjoin : isJoinId (Tuple.fst (Err.head aps)) = false).
          { eapply GoDom_Pair_head_not_isJoinId with (erase := @deAnnotate Var FVAnn).
            - intro Hnil. subst aps. apply H2. reflexivity.
            - exact H1. }
          rewrite Hjoin.
          assert (Ebinders : map (fun '(x,_) => x)
            (map (fun '(x,y) => (x,deAnnotate y)) aps) = map fst aps).
          { rewrite map_map. apply map_ext. intros [v rhs]. reflexivity. }
          change (RevStateInvariant (sublistOf exits)
            (go (captured ++ map (fun '(x,_) => x)
                (map (fun '(x,y) => (x,deAnnotate y)) aps)) p >>=
              (fun body' => return_ (Let
                (Rec (map (fun '(x,y) => (x,deAnnotate y)) aps)) body')))
            (fun e' => isJoinPointsValid e' 0 (updJPSs jpsp' captured) = true)).
          rewrite Ebinders. eapply RevStateInvariant_bind.
          -- apply IH.
             ++ exact H3.
             ++ Core_termination.
             ++ rewrite updJPSs_append. exact Hbody.
          -- intros body'. apply RevStateInvariant_return. intros Hb.
             simpl. cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
             rewrite Efst. simpl_bool. repeat split.
             ++ destruct aps; [simpl in H2; contradiction|reflexivity].
             ++ rewrite orb_true_iff. left.
                rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall.
                intros [v rhs'] Hin.
                rewrite Forall_map, Forall_forall in H1. specialize (H1 _ Hin).
                 simpl in H1. inversion H1; subst.
                 rewrite isJoinId_eq. simpl.
                match goal with H : isJoinId_maybe _ = None |- _ => rewrite H end.
                reflexivity.
             ++ rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall.
                intros [v rhs'] Hin.
                rewrite Forall_map, Forall_forall in H1. specialize (H1 _ Hin).
                simpl in H1. inversion H1; subst.
                match goal with H : isJoinId_maybe v = None |- _ => rename H into Hnon end.
                fold isJoinPointsValidPair.
                rewrite isJoinPointsValidPair_isJoinPointsValid by exact Hnon.
                rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall in Hpairs.
                specialize (Hpairs _ Hin). simpl in Hpairs.
                rewrite isJoinPointsValidPair_isJoinPointsValid in Hpairs by exact Hnon.
                exact Hpairs.
             ++ rewrite updJPSs_append in Hb. exact Hb.
  Qed.

  Lemma pairs'_JPV :
    Forall (fun '(v,rhs) => isValidJoinPointsPair v rhs jpsp' = true) pairs'.
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs isvs_WF isvs_valid jps_WF jps_valid.
    unfold pairs', pairs'_exits, ann_pairs, GHC.Prim.rightSection.
    eapply RevStateInvariant_runState with (P := sublistOf exits).
    * rewrite hs_coq_map, forM_map. apply RevStateInvariant_forM.
      intros [v e] HIn.
      pose proof pairs_VJPP as HP.
      rewrite Forall_forall in HP. specialize (HP _ HIn). simpl in HP.
      pose proof (isValidJoinPointsPair_GoDom_JoinPair _ _ _ HP) as HD.
      inversion HD; subst. simpl.
      erewrite idJoinArity_join by eassumption.
      rewrite collectNAnnBndrs_freeVars_mkLams.
      unfold isValidJoinPointsPair in HP.
      match goal with H : isJoinId_maybe _ = Some _ |- _ =>
        rename H into Hjoin; rewrite Hjoin in HP end.
      destruct (isJoinRHS_mkLams2 _ _ _ HP) as [Hnot Hr].
      eapply RevStateInvariant_bind.
      - apply go_res_isJoinPointsValid_on.
        + rewrite deAnnotate_freeVars. assumption.
        + rewrite deAnnotate_freeVars. exact Hr.
      - intros rhs'. apply RevStateInvariant_return. intros Hr'.
        simpl. unfold isValidJoinPointsPair. rewrite Hjoin.
        apply isJoinRHS_mkLams; [exact Hnot|].
        rewrite updJPSs_not_joinId in Hr'.
        + exact Hr'.
        + rewrite forallb_forall, <- Forall_forall.
          eapply Forall_impl; only 2: exact Hnot.
          intros x Hx. rewrite negb_true_iff. exact Hx.
    * change (sublistOf exits exits). intros x Hin. exact Hin.
  Qed.

  Lemma mkLets_JPI : forall floats e jps0,
    WF jps0 -> ValidVarSet jps0 ->
    disjointVarSet jps0 (mkVarSet (map fst floats)) = true ->
    isJoinPointsValid e 0 (updJPSs jps0 (map fst floats)) = true ->
    forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps0) floats = true ->
    isJoinPointsValid (mkLets (map (fun '(v,rhs) => NonRec v rhs) floats) e) 0 jps0 = true.
  Proof.
    clear pairs_WS pairs_VJPP pairs_NoDup jps_subset_isvs.
    intros floats. induction floats as [|[v rhs] floats IH] using rev_ind;
      intros e jps0 W V Hdisjoint Hbase Hpairs.
    * simpl. unfold Base.id. exact Hbase.
    * rewrite forallb_app in Hpairs. simpl in Hpairs.
      rewrite andb_true_r, andb_true_iff in Hpairs. destruct Hpairs as [Hpairs Hpair].
      rewrite map_app in Hdisjoint.
      rewrite fold_is_true in Hdisjoint.
      rewrite disjointVarSet_mkVarSet_append in Hdisjoint by assumption.
      unfold is_true in Hdisjoint.
      destruct Hdisjoint as [Hdisjoint _].
      rewrite map_app, mkLets_append. simpl.
      rewrite mkLets_cons, mkLets_nil. apply IH; [exact W|exact V| | |].
      - exact Hdisjoint.
      - simpl. fold isJoinPointsValidPair. rewrite andb_true_iff. split.
        + apply isValidJoinPointsPair_isJoinPointsValidPair.
          apply (exit_weakenb (StrongSubset_updJPSs_fresh _ _ W V Hdisjoint)); try solve [exit_inv]. exact Hpair.
        + rewrite map_app in Hbase. simpl in Hbase.
          rewrite updJPSs_append, updJPSs_cons, updJPSs_nil in Hbase. exact Hbase.
      - exact Hpairs.
  Qed.

  Theorem exitifyRec_JPI:
    forall body n,
    pairs <> [] ->
    let jps' := updJPSs jps fs in
    isJoinPointsValid body 0 jps' = true ->
    isJoinPointsValid (mkLets (exitifyRec (extendInScopeSetList in_scope fs) pairs) body) n jps = true.
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs isvs_WF isvs_valid jps_WF jps_valid.
    intros body n Hne jps0 Hbody.
    cbv beta delta [exitifyRec].
    zeta_with go_exit. zeta_with recursive_calls. zeta_with go. zeta_with ann_pairs.
    fold pairs'_exits. expand_pairs. fold pairs'. fold exits.
    rewrite flat_map_unpack_cons_f.
    change (isJoinPointsValid (mkLets
      (map (fun '(v,rhs) => NonRec v rhs) exits ++ [Rec pairs']) body) n jps = true).
    rewrite mkLets_append, mkLets_cons, mkLets_nil.
    apply isJoinPointsValid_more_args with (n := 0); only 1: lia.
    apply mkLets_JPI; try solve [exit_inv].
    * eapply disjointVarSet_subVarSet_l with (t := isvs); try solve [exit_inv]; [exact disjoint_isvs_exits|exact jps_subset_isvs].
    * rewrite isJoinPointsValid_MkLet_Rec.
      subst jps0. float_let. subst _go jps'0.
      pose proof map_fst_pairs' as Hfst.
      cbv beta delta [CoreExpr JoinId Id CoreBndr] in *.
      rewrite Hfst. simpl_bool. repeat split.
      - rewrite orb_true_iff. right.
        rewrite forallb_forall. intros [v rhs] Hin.
        pose proof pairs'_JPV as HP. rewrite Forall_forall in HP.
        specialize (HP _ Hin). exact (isValidJoinPointsPair_isJoinId _ _ _ HP).
      - rewrite forallb_forall. intros [v rhs] Hin.
        pose proof pairs'_JPV as HP. rewrite Forall_forall in HP.
        specialize (HP _ Hin). apply isValidJoinPointsPair_isJoinPointsValidPair. exact HP.
      - apply (exit_weakenb jpsp_to_jpsp'); try solve [exit_inv]. exact Hbody.
    * exact all_exits_ValidJoinPairs.
  Qed.

End in_exitifyRec.

Set Default Proof Using "Type".

(** This concludes the proofs about [exitifyRec]. We can sum up all the above 
    in a single lemma.
    I also introduces an equality for fst_pairs for easier application.
    I also groups all assumptions about [pairs] in one big Forall.
*)
Lemma exitifyRec_WellScoped_JPI:
  forall (in_scope : InScopeSet) (pairs : list (CoreBndr * CoreExpr)) fst_pairs n jps,
  WF (isvs in_scope) -> ValidVarSet (isvs in_scope) ->
  WF jps -> ValidVarSet jps ->
  fst_pairs = map fst pairs ->
  subVarSet jps (isvs in_scope) = true ->
  NoDup (map varUnique fst_pairs) ->
  pairs <> [] ->
  Forall (fun '(v,rhs) =>
     GoodLocalVar v /\
     WellScoped rhs (extendVarSetList (isvs in_scope) fst_pairs) /\
     isValidJoinPointsPair v rhs (updJPSs jps fst_pairs) = true
  ) pairs ->
  forall body : CoreExpr,
  WellScoped body (extendVarSetList (isvs in_scope) fst_pairs) ->
  isJoinPointsValid body 0 (updJPSs jps fst_pairs) = true ->
  WellScoped
    (mkLets (exitifyRec (extendInScopeSetList in_scope fst_pairs) pairs) body)
    (isvs in_scope) /\
  isJoinPointsValid
    (mkLets (exitifyRec (extendInScopeSetList in_scope fst_pairs) pairs) body) n jps = true.
Proof.
  intros in_scope0 pairs0 fst_pairs0 n0 jps0 W V T U Hfst Hjps_sub Hnodup Hne Hpairs body Hbody_WS Hbody_JPI.
  subst fst_pairs0.
  split.
  - eapply (exitifyRec_WellScoped in_scope0 pairs0 jps0); auto.
    + rewrite Forall_forall in *. intros [v rhs] HIn.
      specialize (Hpairs _ HIn). simpl in *. tauto.
    + rewrite Forall_forall in *. intros [v rhs] HIn.
      specialize (Hpairs _ HIn). simpl in *. tauto.
  - eapply (exitifyRec_JPI in_scope0 pairs0 jps0); auto.
    + rewrite Forall_forall in *. intros [v rhs] HIn.
      specialize (Hpairs _ HIn). simpl in *. tauto.
    + rewrite Forall_forall in *. intros [v rhs] HIn.
      specialize (Hpairs _ HIn). simpl in *. tauto.
Qed.

(** ** Verification of [go] in [exitifyProgram] *)

(** For the rest of the module, we deal with well-scopedness and join-point-validity
    simultaneously. We need always both anyways, because the join-point-validity
    implies that the expression in is in the domain of 

    We extract the local [go] from [exitifyProgram], and use induction
    to show that it preserves both invariants.
*)

Definition top_go := ltac:(
  let rhs := eval cbv beta delta [exitifyProgram] in (exitifyProgram []) in
  lazymatch rhs with | (let x := ?rhs in ?body) => 
    exact rhs
  end).

Lemma mapSnd_map:
  forall {a b c} (f : b -> c) (xs : list (a * b)),
  Util.mapSnd f xs = map (fun x => (fst x, f (snd x))) xs.
Proof. intros. induction xs. reflexivity. simpl. destruct a0. rewrite <- IHxs.  reflexivity. Qed.

Lemma top_go_mkLams:
  forall in_scope body vs,
  top_go in_scope (mkLams vs body) =
  mkLams vs (top_go (extendInScopeSetList in_scope vs) body).
Proof.
  intros in_scope0 body vs.
  revert in_scope0 body.
  induction vs as [|v vs' IH]; intros.
  - simpl. rewrite extendInScopeSetList_nil. reflexivity.
  - change (mkLams (v :: vs') body) with (Lam v (mkLams vs' body)).
    change (mkLams (v :: vs') (top_go (extendInScopeSetList in_scope0 (v :: vs')) body))
      with (Lam v (mkLams vs' (top_go (extendInScopeSetList in_scope0 (v :: vs')) body))).
    simpl top_go at 1.
    rewrite extendInScopeSetList_cons.
    f_equal.
    apply IH.
Qed.

Ltac top_inv :=
  unfold isvs in *;
  rewrite ?getInScopeVars_extendInScopeSet, ?getInScopeVars_extendInScopeSetList;
  repeat first [apply updJPSs_WF | apply updJPS_WF | apply updJPSs_valid | apply updJPS_valid];
  solve_varset_inv.

Ltac solve_subVarSet :=
  unfold isvs;
  rewrite ?getInScopeVars_extendInScopeSet;
  rewrite ?getInScopeVars_extendInScopeSetList;
  rewrite ?extendVarSetList_append;
  rewrite ?extendVarSetList_cons;
  rewrite ?extendVarSetList_nil;
  rewrite ?updJPSs_append;
  rewrite ?updJPSs_cons;
  rewrite ?updJPSs_nil;
  repeat first [ solve [top_inv]
               | apply subVarSet_updJPSs_extendVarSetList
               | apply subVarSet_updJPS_extendVarSet
               | apply subVarSet_delVarSetList_extendVarSetList
               | apply subVarSet_delVarSet_extendVarSet
               ];
  first [ assumption
        | apply subVarSet_emptyVarSet
        ].

(**
Nothing really interesting is happening here, just lots oftaking the
conjunction between the invariants apart and combining them again, and 
lots of shifting around [VarSet]s and [InScopeSets], and eventually a call to
[exififyRec]. This really should be simpler.
*)

Program Fixpoint top_go_WellScoped_JPI
  e in_scope n jps {measure e (CoreLT)} :
  WellScoped e (getInScopeVars in_scope)->
  isJoinPointsValid e n jps = true ->
  subVarSet jps (isvs in_scope) = true ->
  WF (getInScopeVars in_scope) -> ValidVarSet (getInScopeVars in_scope) ->
  WF jps -> ValidVarSet jps ->
  WellScoped (top_go in_scope e) (getInScopeVars in_scope) /\
  isJoinPointsValid (top_go in_scope e) n jps = true
  := _.
Next Obligation.
  rename top_go_WellScoped_JPI into IH.
  rename H into HWS. rename H0 into HJPV. rename H1 into Hsubset.
  rename H2 into Wscope. rename H3 into Vscope.
  rename H4 into Wjps. rename H5 into Vjps.
  Ltac step WS JP :=
    lazymatch goal with IH : forall e', _ |- _ =>
    refine (IH _ _ _ _ _ WS JP _ _ _ _ _);
      [Core_termination || (unfold CoreLT; simpl; lia)
      |solve_subVarSet|top_inv|top_inv|top_inv|top_inv] end.
  destruct e; simpl in HJPV; simpl_bool; simpl.
  * split; assumption.
  * split; trivial.
  * inversion HWS as [HWSe1 HWSe2].
    inversion HJPV as [HJPVe1 HJPVe2].
    epose proof ltac:(step HWSe1 HJPVe1).
    epose proof ltac:(step HWSe2 HJPVe2). intuition.
  * inversion HWS as [HGoodVar HWSe].
    simpl in HJPV. simpl_bool. destruct HJPV as [Hnot_join HJPVe].
    rewrite <- getInScopeVars_extendInScopeSet.
    rewrite <- getInScopeVars_extendInScopeSet in HWSe.
    epose proof ltac:(step HWSe HJPVe) as IHe.
    split; (split; [assumption|apply IHe]).
  * destruct HWS as [HBind HWSe].
    destruct b as [v rhs|pairs]; simpl in *.
    + destruct HBind as [HGoodVar Hrhs].
      simpl_bool. destruct HJPV as [HJPV_pair HJPVe].
      fold isJoinPointsValidPair in HJPV_pair.
      fold isJoinPointsValidPair.
      destruct (isJoinId_maybe v) eqn:HiJI.
      ** eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in HJPV_pair;
           only 2: apply HiJI.
         destruct (isJoinRHS_mkLams3 _ _ _ HJPV_pair) as [body [vs [Heq1 Heq2]]]. subst.
         destruct (isJoinRHS_mkLams2 _ _ _ HJPV_pair) as [Hnot_join_params HJPVbody].
         rewrite WellScoped_mkLams in Hrhs.
         destruct Hrhs as [HGoodVars HWSbody].
         rewrite <- getInScopeVars_extendInScopeSetList.
         rewrite <- getInScopeVars_extendInScopeSetList in HWSbody.
         epose proof ltac:(step HWSbody HJPVbody) as IHbody.
         rewrite <- getInScopeVars_extendInScopeSetList in HWSe.
         epose proof ltac:(step HWSe HJPVe) as IHe.
         rewrite top_go_mkLams. split.
         -- split; only 1: split.
            - assumption.
            - rewrite WellScoped_mkLams. split; [assumption|].
              rewrite <- getInScopeVars_extendInScopeSetList. apply IHbody.
            - apply IHe.
         -- split.
            - erewrite isJoinPointsValidPair_isJoinRHS by eassumption.
              apply isJoinRHS_mkLams; only 1: apply Hnot_join_params.
              rewrite <- updJPSs_not_joinId.
              2: { rewrite forallb_forall.
                   rewrite Forall_forall in Hnot_join_params.
                   intros v' HIn. rewrite negb_true_iff.
                   apply Hnot_join_params. assumption. }
              apply IHbody.
            - apply IHe.
      ** eapply isJoinPointsValidPair_isJoinPointsValid in HJPV_pair;
           only 2: apply HiJI.
         epose proof ltac:(step Hrhs HJPV_pair) as IHrhs.
         rewrite <- getInScopeVars_extendInScopeSetList,
           extendInScopeSetList_cons, extendInScopeSetList_nil in HWSe.
         rewrite <- getInScopeVars_extendInScopeSetList,
           extendInScopeSetList_cons, extendInScopeSetList_nil.
         epose proof ltac:(step HWSe HJPVe) as IHe.
         split.
         -- split; only 1: split; [assumption|apply IHrhs|apply IHe].
         -- split; [rewrite isJoinPointsValidPair_isJoinPointsValid by assumption;
                    apply IHrhs|apply IHe].
    + destruct HBind as [HGoodVars [HNoDup Hpairs]].
      simpl_bool. destruct HJPV as [[Hnot_null Hall_or_none] [HJPVpairs HJPVe]].
      fold isJoinPointsValidPair in HJPVpairs.
      destruct_match.
      - rewrite HSUtil.Foldable_any_existsb in Heq.
        rewrite existsb_morgan in Heq. rewrite negb_true_iff in Heq.
        rewrite orb_true_iff in Hall_or_none.
        destruct Hall_or_none as [Hnone|Hall].
        1: { exfalso. apply (eq_true_false_abs _ Hnone Heq). }
        rewrite bindersOf_Rec_cleanup in *.
        eapply exitifyRec_WellScoped_JPI; try solve [top_inv].
        ** rewrite mapSnd_map, map_map. apply map_ext. intros. reflexivity.
        ** assumption.
        ** assumption.
        ** rewrite mapSnd_map. destruct pairs; simpl in *; congruence.
        ** rewrite Forall'_Forall in Hpairs.
           rewrite mapSnd_map, Forall_map. rewrite Forall_forall in *.
           intros [v rhs] HIn. simpl.
           rewrite forallb_forall in HJPVpairs.
           specialize (Hpairs _ HIn). specialize (HJPVpairs _ HIn).
           rewrite forallb_forall in Hall. specialize (Hall _ HIn). simpl in Hall.
           simpl in HJPVpairs. specialize (HGoodVars _ HIn).
           split; only 1: assumption.
           destruct (isJoinId_maybe v) eqn:HiJI.
           2: { exfalso. rewrite isJoinId_eq in Hall. rewrite HiJI in Hall. congruence. }
           rewrite isJoinPointsValidPair_isJoinRHS in HJPVpairs by apply HiJI.
           unfold isValidJoinPointsPair; rewrite HiJI.
           destruct (isJoinRHS_mkLams3 _ _ _ HJPVpairs) as [body [vs [Heq1 Heq2]]]. subst.
           destruct (isJoinRHS_mkLams2 _ _ _ HJPVpairs) as [Hnot_join_params HJPVbody].
           simpl in Hpairs. rewrite WellScoped_mkLams in Hpairs.
           clear HGoodVars. destruct Hpairs as [HGoodVars HWSbody].
           rewrite <- !getInScopeVars_extendInScopeSetList in HWSbody.
           rewrite <- !getInScopeVars_extendInScopeSetList.
           epose proof ltac:(step HWSbody HJPVbody).
           rewrite top_go_mkLams. split.
           -- rewrite WellScoped_mkLams. split; [assumption|].
              rewrite <- getInScopeVars_extendInScopeSetList. apply H.
           -- apply isJoinRHS_mkLams; only 1: apply Hnot_join_params.
              rewrite <- updJPSs_not_joinId.
              2: { rewrite forallb_forall. rewrite Forall_forall in Hnot_join_params.
                   intros. rewrite negb_true_iff. apply Hnot_join_params. assumption. }
              apply H.
        ** rewrite <- getInScopeVars_extendInScopeSetList in HWSe.
           rewrite <- getInScopeVars_extendInScopeSetList.
           epose proof ltac:(step HWSe HJPVe). apply H.
        ** rewrite <- getInScopeVars_extendInScopeSetList in HWSe.
           epose proof ltac:(step HWSe HJPVe). apply H.
      - rewrite HSUtil.Foldable_any_existsb in Heq.
        rewrite existsb_morgan in Heq. rewrite negb_false_iff in Heq.
        simpl. simpl_bool.
        eassert (_ /\ _) as HWS_JPI; swap 1 2.
        repeat apply conj.
        ** rewrite mapSnd_map, Forall_map.
           eapply Forall_impl; only 2: apply HGoodVars. simpl.
           intros [v rhs] HGoodVar. apply HGoodVar.
        ** rewrite mapSnd_map. repeat rewrite map_map.
           rewrite map_map in HNoDup. apply HNoDup.
        ** eapply (proj1 HWS_JPI).
        ** rewrite !bindersOf_Rec_cleanup in *.
           rewrite mapSnd_map, map_map. simpl.
           rewrite <- getInScopeVars_extendInScopeSetList.
           rewrite <- getInScopeVars_extendInScopeSetList in *.
           epose proof ltac:(step HWSe HJPVe). apply H.
        ** destruct pairs; simpl in *; congruence.
        ** simpl_bool. left. rewrite bindersOf_Rec_cleanup in *.
           rewrite mapSnd_map.
           rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall.
           intros [v rhs] HIn. rewrite forallb_forall in Heq.
           specialize (Heq _ HIn). simpl in *. assumption.
        ** eapply (proj2 HWS_JPI).
        ** rewrite !bindersOf_Rec_cleanup in *.
           rewrite mapSnd_map, map_map. simpl.
           rewrite <- getInScopeVars_extendInScopeSetList in *.
           epose proof ltac:(step HWSe HJPVe). apply H.
        ** rewrite Forall'_Forall, forallb_forall, <- Forall_forall, Forall_and.
           clear HWSe HJPVe. rewrite ?bindersOf_Rec_cleanup in *.
           rewrite mapSnd_map, !Forall_map, Forall_forall.
           fold isJoinPointsValidPair. intros [v rhs] HIn.
           rewrite Forall'_Forall, Forall_forall in Hpairs.
           rewrite forallb_forall in HJPVpairs.
           specialize (Hpairs _ HIn). specialize (HJPVpairs _ HIn). simpl in *.
           rewrite <- getInScopeVars_extendInScopeSetList, map_map. simpl.
           rewrite <- getInScopeVars_extendInScopeSetList in Hpairs.
           destruct (isJoinId_maybe v) eqn:HiJI.
           1: { exfalso. rewrite forallb_forall in Heq. specialize (Heq _ HIn).
                simpl in Heq. rewrite isJoinId_eq, HiJI in Heq. simpl in Heq. congruence. }
           rewrite isJoinPointsValidPair_isJoinPointsValid in * by apply HiJI.
           epose proof ltac:(step Hpairs HJPVpairs). apply H.
  * destruct HWS as [HWSscrut [HGoodVar HWSalts]].
    rewrite Forall'_Forall in *.
    destruct HJPV as [[Hnot_join HJPVscrut] HJPValts].
    epose proof ltac:(step HWSscrut HJPVscrut) as IHe.
    eassert (_ /\ _) as HWS_JPI; swap 1 2.
    simpl_bool.
    split; [split; only 2: split|split; only 1: split].
    + apply IHe.
    + assumption.
    + eapply (proj1 HWS_JPI).
    + apply Hnot_join.
    + apply IHe.
    + eapply (proj2 HWS_JPI).
    + clear IHe. unfold Base.map.
      rewrite forallb_forall, <- Forall_forall, !Forall_map. simpl.
      rewrite Forall_and. rewrite Forall_forall in *.
      intros [dc pats rhs] HIn.
      specialize (HWSalts _ HIn). simpl in HWSalts.
      rewrite forallb_forall in HJPValts. specialize (HJPValts _ HIn). simpl in HJPValts.
      simpl_bool. destruct HWSalts as [HGoodVars HWSrhs].
      destruct HJPValts as [Hnot_joins HJPVrhs].
      rewrite extendVarSetList_cons.
      rewrite <- getInScopeVars_extendInScopeSet, <- getInScopeVars_extendInScopeSetList.
      rewrite <- !extendInScopeSetList_cons.
      rewrite <- getInScopeVars_extendInScopeSetList in HWSrhs.
      epose proof ltac:(step HWSrhs HJPVrhs) as IHrhs.
      split; split; [apply HGoodVars|apply IHrhs|apply Hnot_joins|apply IHrhs].
  * simpl in *.
    epose proof ltac:(step HWS HJPV). assumption.
  * intuition.
  * intuition.
Unshelve.
  all: top_inv || Core_termination || (unfold CoreLT; simpl; lia).
Qed.

Lemma Forall_flattenBinds:
  forall {b} P (binds : list (Bind b)),
  Forall P (flattenBinds binds) <->
  Forall (fun bind => Forall P (flattenBinds [bind])) binds.
Proof.
  intros b P binds.
  induction binds as [|bind binds' IH].
  - simpl. split; constructor.
  - destruct bind as [v rhs | pairs].
    + simpl. split; intro H.
      * inversion H; subst. constructor.
        -- constructor; [assumption | constructor].
        -- apply IH. assumption.
      * inversion H; subst. inversion H2; subst.
        constructor; [assumption | apply IH; assumption].
    + simpl. split; intro H.
      * apply Forall_app in H. destruct H as [H1 H2].
        constructor; [|apply IH; assumption].
        rewrite Forall_app. split; [assumption | constructor].
      * inversion H; subst.
        apply Forall_app. split.
        -- rewrite Forall_app in H2. destruct H2. assumption.
        -- apply IH. assumption.
Qed.

Lemma bindersOfBinds_cons:
  forall bind (pgm : CoreProgram),
  bindersOfBinds (bind :: pgm) = bindersOf bind ++ bindersOfBinds pgm.
Proof.
  intros bind pgm.
  unfold bindersOfBinds.
  rewrite Foldable.hs_coq_foldr_list.
  simpl. reflexivity.
Qed.

(** ** Verification of [exitifyProgram] *)

(** Local definitions extracted from [exitifyProgram] for proof use. *)

Definition ep_in_scope (pgm : CoreProgram) :=
  CoreUtils.extendInScopeSetBndrs emptyInScopeSet pgm.

Definition ep_goTopLvl (in_scope : InScopeSet) (bind : CoreBind) :=
  match bind with
  | NonRec v e => NonRec v (top_go in_scope e)
  | Rec pairs => Rec (GHC.Base.map (Data.Bifunctor.second (top_go in_scope)) pairs)
  end.

Lemma exitifyProgram_eq pgm :
  exitifyProgram pgm = GHC.Base.map (ep_goTopLvl (ep_in_scope pgm)) pgm.
Proof. unfold exitifyProgram, ep_goTopLvl, ep_in_scope. f_equal. Qed.

Lemma bindersOf_ep_goTopLvl :
  forall in_scope bind, bindersOf (ep_goTopLvl in_scope bind) = bindersOf bind.
Proof.
  intros. unfold ep_goTopLvl. destruct bind.
  - reflexivity.
  - simpl. rewrite !bindersOf_Rec_cleanup.
    rewrite hs_coq_map. rewrite map_map.
    apply map_ext. intros [v rhs]. reflexivity.
Qed.

Lemma bindersOfBinds_ep_goTopLvl :
  forall in_scope pgm,
  bindersOfBinds (GHC.Base.map (ep_goTopLvl in_scope) pgm) = bindersOfBinds pgm.
Proof.
  intros. induction pgm as [|bind pgm' IH].
  - reflexivity.
  - rewrite hs_coq_map. simpl.
    rewrite !bindersOfBinds_cons.
    rewrite <- hs_coq_map. rewrite IH. f_equal.
    apply bindersOf_ep_goTopLvl.
Qed.

(* Each bind: foldBindersOfBindStrict = foldl' over bindersOf *)
Lemma foldBindersOfBindStrict_bindersOf :
  forall (s : VarSet) (bind : CoreBind),
  foldBindersOfBindStrict extendVarSet s bind =
  Data.Foldable.foldl' extendVarSet s (bindersOf bind).
Proof.
  intros s [v rhs | pairs0].
  - (* NonRec *)
    simpl. rewrite Foldable_foldl'_cons. rewrite Foldable_foldl'_nil. reflexivity.
  - (* Rec *)
    simpl. f_equal. symmetry. apply bindersOf_Rec_cleanup.
Qed.

(* Generalized: folding bind-by-bind = folding over flat binder list *)
Lemma foldBindersOfBindsStrict_bindersOfBinds :
  forall (s : VarSet) (pgm : CoreProgram),
  foldBindersOfBindsStrict extendVarSet s pgm =
  Data.Foldable.foldl' extendVarSet s (bindersOfBinds pgm).
Proof.
  intros s pgm. revert s.
  induction pgm as [|bind rest IH]; intro s.
  - (* nil *)
    unfold foldBindersOfBindsStrict. rewrite Foldable_foldl'_nil.
    replace (bindersOfBinds (@nil CoreBind)) with (@nil Var) by reflexivity.
    rewrite Foldable_foldl'_nil. reflexivity.
  - (* cons *)
    unfold foldBindersOfBindsStrict.
    rewrite Foldable_foldl'_cons.
    rewrite bindersOfBinds_cons.
    rewrite Foldable_foldl'_app.
    change (Data.Foldable.foldl' (foldBindersOfBindStrict extendVarSet)
              (foldBindersOfBindStrict extendVarSet s bind) rest)
      with (foldBindersOfBindsStrict extendVarSet
              (foldBindersOfBindStrict extendVarSet s bind) rest).
    rewrite IH.
    f_equal.
    apply foldBindersOfBindStrict_bindersOf.
Qed.

Lemma getInScopeVars_ep_in_scope pgm :
  getInScopeVars (ep_in_scope pgm) = mkVarSet (bindersOfBinds pgm).
Proof.
  unfold ep_in_scope, CoreUtils.extendInScopeSetBndrs, emptyInScopeSet.
  simpl.
  unfold mkVarSet, UniqSet.mkUniqSet, emptyVarSet, extendVarSet.
  rewrite foldBindersOfBindsStrict_bindersOfBinds.
  reflexivity.
Qed.

  Lemma ep_in_scope_WF pgm : WF (getInScopeVars (ep_in_scope pgm)).
Proof. rewrite getInScopeVars_ep_in_scope. apply mkVarSet_WF. Qed.

Lemma ep_in_scope_valid pgm : ValidVarSet (getInScopeVars (ep_in_scope pgm)).
Proof. rewrite getInScopeVars_ep_in_scope. apply mkVarSet_valid. Qed.

(** At last, the final result. *)

Theorem exitifyProgram_WellScoped_JPV:
  forall pgm,
  WellScopedProgram pgm ->
  isJoinPointsValidProgram pgm ->
  WellScopedProgram (exitifyProgram pgm) /\
  isJoinPointsValidProgram (exitifyProgram pgm).
Proof.
  intros pgm HWS HJPV.
  rewrite exitifyProgram_eq.

  destruct HWS as [HNoDup HWS].
  rewrite Forall'_Forall in HWS.
  unfold isJoinPointsValidProgram in HJPV.

  (* Helper: each bind individually preserves both invariants *)
  assert (Hbind: forall bind,
    Forall (fun p => WellScoped (snd p) (mkVarSet (bindersOfBinds pgm)))
           (flattenBinds [bind]) ->
    Forall (fun '(v,e) => isJoinId v = false /\
            isJoinPointsValid e 0 emptyVarSet = true) (flattenBinds [bind]) ->
    Forall (fun p => WellScoped (snd p) (mkVarSet (bindersOfBinds pgm)))
           (flattenBinds [ep_goTopLvl (ep_in_scope pgm) bind]) /\
    Forall (fun '(v,e) => isJoinId v = false /\
            isJoinPointsValid e 0 emptyVarSet = true)
           (flattenBinds [ep_goTopLvl (ep_in_scope pgm) bind])).
  { intros bind HbWS HbJPV.
    destruct bind as [v rhs | pairs0].
    - (* NonRec *)
      simpl in *.
      inversion_clear HbWS as [|?? Hws _].
      inversion_clear HbJPV as [|?? Hjpv _].
      simpl in Hjpv. destruct Hjpv as [HisJoinId Hjpv_rhs].
      pose proof (top_go_WellScoped_JPI rhs (ep_in_scope pgm) 0 emptyVarSet) as [HtgWS HtgJPV].
      { rewrite getInScopeVars_ep_in_scope. exact Hws. }
      { exact Hjpv_rhs. }
      { apply subVarSet_emptyVarSet. apply ep_in_scope_WF. }
      { apply ep_in_scope_WF. }
      { apply ep_in_scope_valid. }
      { apply emptyVarSet_WF. }
      { apply emptyVarSet_valid. }
      split; (constructor; [|constructor]).
      + simpl. rewrite <- getInScopeVars_ep_in_scope. exact HtgWS.
      + simpl. exact (conj HisJoinId HtgJPV).
    - (* Rec *)
      simpl in *.
      rewrite app_nil_r in *.
      split.
      + rewrite hs_coq_map. rewrite Forall_map.
        rewrite Forall_forall. intros [v' e'] HIn'.
        rewrite Forall_forall in HbWS, HbJPV.
        specialize (HbWS _ HIn'). specialize (HbJPV _ HIn').
        simpl in *. destruct HbJPV as [? ?].
        pose proof (top_go_WellScoped_JPI e' (ep_in_scope pgm) 0 emptyVarSet) as [HtgWS HtgJPV].
        { rewrite getInScopeVars_ep_in_scope. exact HbWS. }
        { exact H0. }
        { apply subVarSet_emptyVarSet. apply ep_in_scope_WF. }
        { apply ep_in_scope_WF. }
        { apply ep_in_scope_valid. }
        { apply emptyVarSet_WF. }
        { apply emptyVarSet_valid. }
        simpl. rewrite <- getInScopeVars_ep_in_scope. exact HtgWS.
      + rewrite hs_coq_map. rewrite Forall_map.
        rewrite Forall_forall. intros [v' e'] HIn'.
        rewrite Forall_forall in HbWS, HbJPV.
        specialize (HbWS _ HIn'). specialize (HbJPV _ HIn').
        simpl in *. destruct HbJPV as [? ?].
        pose proof (top_go_WellScoped_JPI e' (ep_in_scope pgm) 0 emptyVarSet) as [_ HtgJPV].
        { rewrite getInScopeVars_ep_in_scope. exact HbWS. }
        { exact H0. }
        { apply subVarSet_emptyVarSet. apply ep_in_scope_WF. }
        { apply ep_in_scope_WF. }
        { apply ep_in_scope_valid. }
        { apply emptyVarSet_WF. }
        { apply emptyVarSet_valid. }
        split; [exact H | exact HtgJPV].
  }

  split.
  - (* WellScopedProgram *)
    unfold WellScopedProgram.
    rewrite bindersOfBinds_ep_goTopLvl.
    split; [exact HNoDup|].
    rewrite Forall'_Forall.
    rewrite Forall_flattenBinds in *.
    rewrite hs_coq_map. rewrite Forall_map.
    rewrite Forall_forall in *.
    intros bind HIn.
    exact (proj1 (Hbind bind (HWS bind HIn) (HJPV bind HIn))).
  - (* isJoinPointsValidProgram *)
    unfold isJoinPointsValidProgram.
    rewrite Forall_flattenBinds in *.
    rewrite hs_coq_map. rewrite Forall_map.
    rewrite Forall_forall in *.
    intros bind HIn.
    exact (proj2 (Hbind bind (HWS bind HIn) (HJPV bind HIn))).
Qed.

Print Assumptions exitifyProgram_WellScoped_JPV.
