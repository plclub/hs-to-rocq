(* Premise-aware contracts for the raw VarSet representation. *)
Require Import Coq.NArith.BinNat Coq.Lists.List.
Require Import Core IntMapProofs Proofs.Axioms.
Require Import IntMapUnionProofs.

Local Notation key := (fun v : Var => Unique.getWordKey (Unique.getUnique v)).

Lemma Var_eq_key x y :
  GHC.Base.op_zeze__ x y = N.eqb (key x) (key y).
Proof.
  destruct x as [nx [ux] tx mx sx dx ix].
  destruct y as [ny [uy] ty my sy dy iy]. reflexivity.
Qed.

Lemma lookupVarSet_IntMap s v :
  lookupVarSet s v = Data.IntMap.Internal.lookup (key v) (VarSet_IntMap s).
Proof. destruct s as [[m]]. reflexivity. Qed.

Lemma elemVarSet_lookup s v :
  WF (VarSet_IntMap s) ->
  elemVarSet v s = match lookupVarSet s v with Some _ => true | None => false end.
Proof.
  destruct s as [[m]]. intros [f H].
  change (Data.IntMap.Internal.member (key v) m =
    match Data.IntMap.Internal.lookup (key v) m with Some _ => true | None => false end).
  rewrite (member_Sem H), (lookup_Sem H). destruct (f (key v)); reflexivity.
Qed.

Lemma extendVarSetList_nil s : extendVarSetList s nil = s.
Proof. reflexivity. Qed.

Lemma extendVarSetList_cons s v vs :
  extendVarSetList s (v :: vs) = extendVarSetList (extendVarSet s v) vs.
Proof. reflexivity. Qed.

Lemma delVarSetList_nil s : delVarSetList s nil = s.
Proof. destruct s as [[m]]. reflexivity. Qed.

Lemma delVarSetList_cons s v vs :
  delVarSetList s (v :: vs) = delVarSetList (delVarSet s v) vs.
Proof. destruct s as [[m]]. reflexivity. Qed.

Lemma elemVarSet_lookup_some s v :
  WF (VarSet_IntMap s) -> elemVarSet v s = true ->
  exists w, lookupVarSet s v = Some w.
Proof.
  intros W H. rewrite (elemVarSet_lookup s v W) in H.
  destruct (lookupVarSet s v) as [w|]; [eauto | discriminate].
Qed.

Lemma lookupVarSet_member s v w :
  WF (VarSet_IntMap s) -> lookupVarSet s v = Some w -> elemVarSet v s = true.
Proof. intros W H. rewrite (elemVarSet_lookup s v W), H. reflexivity. Qed.

Lemma emptyVarSet_WF : WF (VarSet_IntMap emptyVarSet).
Proof. apply empty_WF. Qed.

Lemma emptyVarSet_valid : ValidVarSet emptyVarSet.
Proof. intros v w H. discriminate H. Qed.

Lemma extendVarSet_WF s v :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap (extendVarSet s v)).
Proof. destruct s as [[m]]. apply insert_WF. Qed.

Lemma lookupVarSet_extend s v q :
  WF (VarSet_IntMap s) ->
  lookupVarSet (extendVarSet s v) q =
    if N.eqb (key q) (key v) then Some v else lookupVarSet s q.
Proof.
  destruct s as [[m]]. intros [f H].
  change (Data.IntMap.Internal.lookup (key q) (Data.IntMap.Internal.insert (key v) v m) =
    if N.eqb (key q) (key v) then Some v else Data.IntMap.Internal.lookup (key q) m).
  pose proof (insert_Sem Var (key v) v m f
    (fun i => if N.eqb i (key v) then Some v else f i) H (fun i => eq_refl)) as S.
  rewrite (lookup_Sem S), (lookup_Sem H). reflexivity.
Qed.

Lemma extendVarSet_valid s v :
  WF (VarSet_IntMap s) -> ValidVarSet s -> ValidVarSet (extendVarSet s v).
Proof.
  intros W V q w H. rewrite (lookupVarSet_extend s v q W) in H.
  cbn beta in H. destruct (N.eqb (Unique.getWordKey (Unique.getUnique q))
    (Unique.getWordKey (Unique.getUnique v))) eqn:E.
  - inversion H; subst. rewrite Var_eq_key. exact E.
  - exact (V q w H).
Qed.

Lemma lookupVarSet_extend_same s v :
  WF (VarSet_IntMap s) -> lookupVarSet (extendVarSet s v) v = Some v.
Proof. intro W. rewrite (lookupVarSet_extend s v v W), N.eqb_refl. reflexivity. Qed.

Lemma elemVarSet_extend s v q :
  WF (VarSet_IntMap s) ->
  elemVarSet q (extendVarSet s v) =
    orb (N.eqb (key q) (key v)) (elemVarSet q s).
Proof.
  intro W. rewrite (elemVarSet_lookup _ _ (extendVarSet_WF s v W)),
    (lookupVarSet_extend s v q W), (elemVarSet_lookup s q W).
  cbn beta. destruct (N.eqb (Unique.getWordKey (Unique.getUnique q))
    (Unique.getWordKey (Unique.getUnique v))); reflexivity.
Qed.

Lemma unitVarSet_WF v : WF (VarSet_IntMap (unitVarSet v)).
Proof. apply singleton_WF. Qed.

Lemma unitVarSet_as_extend v : unitVarSet v = extendVarSet emptyVarSet v.
Proof. reflexivity. Qed.

Lemma unitVarSet_valid v : ValidVarSet (unitVarSet v).
Proof. rewrite unitVarSet_as_extend. apply extendVarSet_valid; [apply emptyVarSet_WF | apply emptyVarSet_valid]. Qed.

Lemma delVarSet_WF s v :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap (delVarSet s v)).
Proof. destruct s as [[m]]. apply delete_WF. Qed.

Lemma lookupVarSet_del s v q :
  WF (VarSet_IntMap s) ->
  lookupVarSet (delVarSet s v) q =
    if N.eqb (key q) (key v) then None else lookupVarSet s q.
Proof.
  destruct s as [[m]]. intros [f H].
  change (Data.IntMap.Internal.lookup (key q) (Data.IntMap.Internal.delete (key v) m) =
    if N.eqb (key q) (key v) then None else Data.IntMap.Internal.lookup (key q) m).
  pose proof (delete_Sem (key v) m f
    (fun i => if N.eqb i (key v) then None else f i) H (fun i => eq_refl)) as S.
  rewrite (lookup_Sem S), (lookup_Sem H). reflexivity.
Qed.

Lemma delVarSet_valid s v :
  WF (VarSet_IntMap s) -> ValidVarSet s -> ValidVarSet (delVarSet s v).
Proof.
  intros W V q w H. rewrite (lookupVarSet_del s v q W) in H.
  cbn beta in H. destruct (N.eqb (Unique.getWordKey (Unique.getUnique q))
    (Unique.getWordKey (Unique.getUnique v))); [discriminate | exact (V q w H)].
Qed.

Lemma filterVarSet_WF p s :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap (filterVarSet p s)).
Proof. destruct s as [[m]]. apply filter_WF. Qed.

Lemma lookupVarSet_filter p s q :
  WF (VarSet_IntMap s) ->
  lookupVarSet (filterVarSet p s) q =
    match lookupVarSet s q with Some v => if p v then Some v else None | None => None end.
Proof.
  destruct s as [[m]]. intros [f H].
  change (Data.IntMap.Internal.lookup (key q) (Data.IntMap.Internal.filter p m) =
    match Data.IntMap.Internal.lookup (key q) m with Some v => if p v then Some v else None | None => None end).
  pose proof (filter_Sem p m f
    (fun i => match f i with Some v => if p v then Some v else None | None => None end)
    H (fun i => eq_refl)) as S.
  rewrite (lookup_Sem S), (lookup_Sem H). reflexivity.
Qed.

Lemma filterVarSet_valid p s :
  WF (VarSet_IntMap s) -> ValidVarSet s -> ValidVarSet (filterVarSet p s).
Proof.
  intros W V q w H. rewrite (lookupVarSet_filter p s q W) in H.
  destruct (lookupVarSet s q) as [v|] eqn:E; [|discriminate].
  destruct (p v); [inversion H; subst; exact (V q w E) | discriminate].
Qed.

Lemma extendVarSetList_WF s vs :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap (extendVarSetList s vs)).
Proof.
  revert s. induction vs as [|v vs IH]; intros s W.
  - exact W.
  - rewrite extendVarSetList_cons. apply IH. apply extendVarSet_WF. exact W.
Qed.

Lemma extendVarSetList_valid s vs :
  WF (VarSet_IntMap s) -> ValidVarSet s -> ValidVarSet (extendVarSetList s vs).
Proof.
  revert s. induction vs as [|v vs IH]; intros s W V.
  - exact V.
  - rewrite extendVarSetList_cons. apply IH.
    + apply extendVarSet_WF. exact W.
    + apply extendVarSet_valid; assumption.
Qed.

Lemma mkVarSet_as_extend vs : mkVarSet vs = extendVarSetList emptyVarSet vs.
Proof. reflexivity. Qed.

Lemma mkVarSet_WF vs : WF (VarSet_IntMap (mkVarSet vs)).
Proof. rewrite mkVarSet_as_extend. apply extendVarSetList_WF, emptyVarSet_WF. Qed.

Lemma mkVarSet_valid vs : ValidVarSet (mkVarSet vs).
Proof.
  rewrite mkVarSet_as_extend. apply extendVarSetList_valid;
    [apply emptyVarSet_WF | apply emptyVarSet_valid].
Qed.

Lemma delVarSetList_WF s vs :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap (delVarSetList s vs)).
Proof.
  revert s. induction vs as [|v vs IH]; intros s W.
  - rewrite delVarSetList_nil. exact W.
  - rewrite delVarSetList_cons. apply IH. apply delVarSet_WF. exact W.
Qed.

Lemma delVarSetList_valid s vs :
  WF (VarSet_IntMap s) -> ValidVarSet s -> ValidVarSet (delVarSetList s vs).
Proof.
  revert s. induction vs as [|v vs IH]; intros s W V.
  - rewrite delVarSetList_nil. exact V.
  - rewrite delVarSetList_cons. apply IH.
    + apply delVarSet_WF. exact W.
    + apply delVarSet_valid; assumption.
Qed.

Lemma elemVarSet_del s v q :
  WF (VarSet_IntMap s) ->
  elemVarSet q (delVarSet s v) =
    andb (negb (N.eqb (key q) (key v))) (elemVarSet q s).
Proof.
  intro W. rewrite (elemVarSet_lookup _ _ (delVarSet_WF s v W)),
    (lookupVarSet_del s v q W), (elemVarSet_lookup s q W).
  cbn beta. destruct (N.eqb (Unique.getWordKey (Unique.getUnique q))
    (Unique.getWordKey (Unique.getUnique v))); reflexivity.
Qed.

Lemma lookupVarSet_filter_some p s q w :
  WF (VarSet_IntMap s) ->
  (lookupVarSet (filterVarSet p s) q = Some w <->
   lookupVarSet s q = Some w /\ p w = true).
Proof.
  intro W. rewrite (lookupVarSet_filter p s q W).
  destruct (lookupVarSet s q) as [v|] eqn:E.
  - destruct (p v) eqn:P; split; intro H.
    + inversion H; subst. auto.
    + destruct H as [H _]. exact H.
    + discriminate.
    + destruct H as [H Hpw]. inversion H; subst. congruence.
  - split; [discriminate | intros [H _]; discriminate].
Qed.

Lemma elemVarSet_filter_forward p s q :
  WF (VarSet_IntMap s) -> elemVarSet q (filterVarSet p s) = true ->
  elemVarSet q s = true /\ exists w, lookupVarSet s q = Some w /\ p w = true.
Proof.
  intros W M.
  destruct (elemVarSet_lookup_some _ _ (filterVarSet_WF p s W) M) as [w H].
  apply (proj1 (lookupVarSet_filter_some p s q w W)) in H.
  split.
  - eapply lookupVarSet_member; [exact W | exact (proj1 H)].
  - exists w. exact H.
Qed.

Lemma lookupVarSet_extend_neq s v q :
  WF (VarSet_IntMap s) -> GHC.Base.op_zeze__ q v = false ->
  lookupVarSet (extendVarSet s v) q = lookupVarSet s q.
Proof.
  intros W E. rewrite Var_eq_key in E.
  rewrite (lookupVarSet_extend s v q W), E. reflexivity.
Qed.

Lemma elemVarSet_extend_eq s v q :
  WF (VarSet_IntMap s) ->
  elemVarSet q (extendVarSet s v) =
    orb (GHC.Base.op_zeze__ q v) (elemVarSet q s).
Proof. intro W. rewrite Var_eq_key. apply elemVarSet_extend. exact W. Qed.

Lemma lookupVarSet_valid s q w :
  ValidVarSet s -> lookupVarSet s q = Some w -> GHC.Base.op_zeze__ q w = true.
Proof. intros V H. exact (V q w H). Qed.

Lemma elemVarSet_empty v : elemVarSet v emptyVarSet = false.
Proof. reflexivity. Qed.

Lemma lookupVarSet_empty v : lookupVarSet emptyVarSet v = None.
Proof. reflexivity. Qed.

Lemma elemVarSet_unit v q :
  elemVarSet q (unitVarSet v) = GHC.Base.op_zeze__ q v.
Proof.
  rewrite unitVarSet_as_extend, (elemVarSet_extend_eq _ _ _ emptyVarSet_WF),
    elemVarSet_empty. apply Bool.orb_false_r.
Qed.

(* These audits deliberately do not use any unrestricted raw-set adapter. *)
Print Assumptions mkVarSet_WF.
Print Assumptions mkVarSet_valid.
Print Assumptions delVarSetList_valid.
Print Assumptions filterVarSet_valid.
Print Assumptions elemVarSet_extend.

Lemma unionVarSet_WF s t :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  WF (VarSet_IntMap (unionVarSet s t)).
Proof.
  destruct s as [[m]], t as [[n]]. intros W X.
  apply IntMapUnionProofs.union_WF; assumption.
Qed.

Lemma lookupVarSet_union s t q :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  lookupVarSet (unionVarSet s t) q =
    match lookupVarSet t q with Some v => Some v | None => lookupVarSet s q end.
Proof.
  destruct s as [[m]], t as [[n]]. intros [f S] [g T].
  change (Data.IntMap.Internal.lookup (key q) (Data.IntMap.Internal.union n m) =
    match Data.IntMap.Internal.lookup (key q) n with
    | Some v => Some v | None => Data.IntMap.Internal.lookup (key q) m end).
  rewrite (lookup_Sem (IntMapUnionProofs.union_Sem n g m f T S)),
    (lookup_Sem S), (lookup_Sem T). destruct (g (key q)); reflexivity.
Qed.

Lemma unionVarSet_valid s t :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  ValidVarSet s -> ValidVarSet t -> ValidVarSet (unionVarSet s t).
Proof.
  intros W X V U q w H. rewrite (lookupVarSet_union s t q W X) in H.
  destruct (lookupVarSet t q) as [v|] eqn:E.
  - inversion H; subst. exact (U q w E).
  - exact (V q w H).
Qed.

Lemma elemVarSet_union s t q :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  elemVarSet q (unionVarSet s t) = orb (elemVarSet q s) (elemVarSet q t).
Proof.
  intros W X. rewrite (elemVarSet_lookup _ _ (unionVarSet_WF s t W X)),
    (lookupVarSet_union s t q W X), (elemVarSet_lookup s q W),
    (elemVarSet_lookup t q X).
  destruct (lookupVarSet s q), (lookupVarSet t q); reflexivity.
Qed.

Lemma minusVarSet_WF s t :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  WF (VarSet_IntMap (minusVarSet s t)).
Proof. destruct s as [[m]], t as [[n]]. apply IntMapUnionProofs.difference_WF. Qed.

Lemma lookupVarSet_minus s t q :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  lookupVarSet (minusVarSet s t) q =
    match lookupVarSet t q with Some _ => None | None => lookupVarSet s q end.
Proof.
  destruct s as [[m]], t as [[n]]. intros [f S] [g T].
  change (Data.IntMap.Internal.lookup (key q) (Data.IntMap.Internal.difference m n) =
    match Data.IntMap.Internal.lookup (key q) n with
    | Some _ => None | None => Data.IntMap.Internal.lookup (key q) m end).
  rewrite (lookup_Sem (IntMapUnionProofs.difference_Sem m f n g S T)),
    (lookup_Sem S), (lookup_Sem T). reflexivity.
Qed.

Lemma minusVarSet_valid s t :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  ValidVarSet s -> ValidVarSet (minusVarSet s t).
Proof.
  intros W X V q w H. rewrite (lookupVarSet_minus s t q W X) in H.
  destruct (lookupVarSet t q); [discriminate | exact (V q w H)].
Qed.

Lemma elemVarSet_minus s t q :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  elemVarSet q (minusVarSet s t) = andb (elemVarSet q s) (negb (elemVarSet q t)).
Proof.
  intros W X. rewrite (elemVarSet_lookup _ _ (minusVarSet_WF s t W X)),
    (lookupVarSet_minus s t q W X), (elemVarSet_lookup s q W),
    (elemVarSet_lookup t q X).
  destruct (lookupVarSet s q), (lookupVarSet t q); reflexivity.
Qed.

Lemma ValidVarSet_lookup_key s :
  ValidVarSet s -> forall k v,
  Data.IntMap.Internal.lookup k (VarSet_IntMap s) = Some v -> key v = k.
Proof.
  intros V k [n [u] t mult sc d i] H.
  destruct s as [[m]].
  pose proof (V (Mk_Id n (Unique.MkUnique k) t mult sc d i)
    (Mk_Id n (Unique.MkUnique u) t mult sc d i) H) as E.
  change (N.eqb k u = true) in E.
  change (u = k). symmetry. apply N.eqb_eq. exact E.
Qed.

Lemma isEmptyVarSet_spec s :
  WF (VarSet_IntMap s) ->
  (isEmptyVarSet s = true <-> forall v, elemVarSet v s = false).
Proof.
  intros W. split.
  - destruct s as [[m]]. destruct W as [f S]. intro E.
    change (Data.IntMap.Internal.null m = true) in E.
    pose proof (proj1 (IntMapProofs.null_Sem S) E) as Empty. intro v.
    change (Data.IntMap.Internal.member (key v) m = false).
    rewrite (member_Sem S), Empty. reflexivity.
  - intro E. destruct s as [[m]]. destruct W as [f S].
    change (Data.IntMap.Internal.null m = true). apply (proj2 (IntMapProofs.null_Sem S)).
    intro k. destruct (f k) as [v|] eqn:F; [|reflexivity].
    (* Rekey a stored value to query k, irrespective of its payload unique. *)
    specialize (E (setVarUnique v (Unique.MkUnique k))).
    destruct v.
    change (Data.IntMap.Internal.member k m = false) in E.
    rewrite (member_Sem S), F in E. discriminate.
Qed.

Lemma subVarSet_spec s t :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  (subVarSet s t = true <->
   forall v, elemVarSet v s = true -> elemVarSet v t = true).
Proof.
  intros W X. unfold subVarSet.
  rewrite (isEmptyVarSet_spec _ (minusVarSet_WF s t W X)).
  split; intros H v; specialize (H v).
  - rewrite (elemVarSet_minus s t v W X) in H.
    destruct (elemVarSet v s), (elemVarSet v t); simpl in *; congruence.
  - rewrite (elemVarSet_minus s t v W X).
    destruct (elemVarSet v s), (elemVarSet v t); simpl in *; try reflexivity.
    specialize (H eq_refl). discriminate.
Qed.

Lemma fold_unionVarSet_WF ss s :
  (forall t, In t ss -> WF (VarSet_IntMap t)) -> WF (VarSet_IntMap s) ->
  WF (VarSet_IntMap (fold_right unionVarSet s ss)).
Proof.
  intros H W. induction ss as [|t ts IH]; simpl; [exact W|].
  apply unionVarSet_WF.
  - apply H. left. reflexivity.
  - apply IH. intros u U. apply H. right. exact U.
Qed.

Lemma fold_unionVarSet_valid ss s :
  (forall t, In t ss -> WF (VarSet_IntMap t)) ->
  (forall t, In t ss -> ValidVarSet t) ->
  WF (VarSet_IntMap s) -> ValidVarSet s ->
  ValidVarSet (fold_right unionVarSet s ss).
Proof.
  intros H V W U. induction ss as [|t ts IH]; simpl; [exact U|].
  apply unionVarSet_valid.
  - apply H. left. reflexivity.
  - apply fold_unionVarSet_WF; [intros u Hu; apply H; right; exact Hu|exact W].
  - apply V. left. reflexivity.
  - apply IH.
    + intros u Hu. apply H. right. exact Hu.
    + intros u Hu. apply V. right. exact Hu.
Qed.

Lemma unionVarSets_WF ss :
  (forall s, In s ss -> WF (VarSet_IntMap s)) ->
  WF (VarSet_IntMap (unionVarSets ss)).
Proof.
  destruct ss as [|s ss]; intro H; [apply emptyVarSet_WF|].
  change (WF (VarSet_IntMap (fold_right unionVarSet s ss))).
  apply fold_unionVarSet_WF.
  - intros t T. apply H. right. exact T.
  - apply H. left. reflexivity.
Qed.

Lemma unionVarSets_valid ss :
  (forall s, In s ss -> WF (VarSet_IntMap s)) ->
  (forall s, In s ss -> ValidVarSet s) -> ValidVarSet (unionVarSets ss).
Proof.
  destruct ss as [|s ss]; intros H V; [apply emptyVarSet_valid|].
  change (ValidVarSet (fold_right unionVarSet s ss)).
  apply fold_unionVarSet_valid.
  - intros t T. apply H. right. exact T.
  - intros t T. apply V. right. exact T.
  - apply H. left. reflexivity.
  - apply V. left. reflexivity.
Qed.

Lemma mapUnionVarSet_WF {a} (f : a -> VarSet) xs :
  (forall x, In x xs -> WF (VarSet_IntMap (f x))) ->
  WF (VarSet_IntMap (mapUnionVarSet f xs)).
Proof.
  intro H. induction xs as [|x xs IH]; [apply emptyVarSet_WF|].
  change (WF (VarSet_IntMap (unionVarSet (f x) (mapUnionVarSet f xs)))).
  apply unionVarSet_WF.
  - apply H. left. reflexivity.
  - apply IH. intros y Y. apply H. right. exact Y.
Qed.

Lemma mapUnionVarSet_valid {a} (f : a -> VarSet) xs :
  (forall x, In x xs -> WF (VarSet_IntMap (f x))) ->
  (forall x, In x xs -> ValidVarSet (f x)) -> ValidVarSet (mapUnionVarSet f xs).
Proof.
  intros H V. induction xs as [|x xs IH]; [apply emptyVarSet_valid|].
  change (ValidVarSet (unionVarSet (f x) (mapUnionVarSet f xs))).
  apply unionVarSet_valid.
  - apply H. left. reflexivity.
  - apply mapUnionVarSet_WF. intros y Y. apply H. right. exact Y.
  - apply V. left. reflexivity.
  - apply IH.
    + intros y Y. apply H. right. exact Y.
    + intros y Y. apply V. right. exact Y.
Qed.

Create HintDb varset_invariant.
#[export] Hint Resolve emptyVarSet_WF emptyVarSet_valid unitVarSet_WF unitVarSet_valid
  extendVarSet_WF extendVarSet_valid extendVarSetList_WF extendVarSetList_valid
  mkVarSet_WF mkVarSet_valid delVarSet_WF delVarSet_valid
  delVarSetList_WF delVarSetList_valid filterVarSet_WF filterVarSet_valid
  unionVarSet_WF unionVarSet_valid minusVarSet_WF minusVarSet_valid
  unionVarSets_WF unionVarSets_valid mapUnionVarSet_WF mapUnionVarSet_valid
  : varset_invariant.

Print Assumptions unionVarSet_valid.
Print Assumptions minusVarSet_valid.
Print Assumptions isEmptyVarSet_spec.
Print Assumptions subVarSet_spec.
Print Assumptions unionVarSets_valid.
Print Assumptions mapUnionVarSet_valid.

Lemma intersectVarSet_WF s t :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  WF (VarSet_IntMap (intersectVarSet s t)).
Proof. destruct s as [[m]], t as [[n]]. apply IntMapUnionProofs.intersection_WF. Qed.

Lemma lookupVarSet_intersect s t q :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  lookupVarSet (intersectVarSet s t) q =
    match lookupVarSet t q with Some _ => lookupVarSet s q | None => None end.
Proof.
  destruct s as [[m]], t as [[n]].
  apply IntMapUnionProofs.intersection_lookup.
Qed.

Lemma intersectVarSet_valid s t :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  ValidVarSet s -> ValidVarSet (intersectVarSet s t).
Proof.
  intros W X V q w H. rewrite (lookupVarSet_intersect s t q W X) in H.
  destruct (lookupVarSet t q); [exact (V q w H)|discriminate].
Qed.

Lemma elemVarSet_intersect s t q :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  elemVarSet q (intersectVarSet s t) = andb (elemVarSet q s) (elemVarSet q t).
Proof.
  intros W X. rewrite (elemVarSet_lookup _ _ (intersectVarSet_WF s t W X)),
    (lookupVarSet_intersect s t q W X), (elemVarSet_lookup s q W),
    (elemVarSet_lookup t q X).
  destruct (lookupVarSet s q), (lookupVarSet t q); reflexivity.
Qed.

Lemma disjointVarSet_spec s t :
  WF (VarSet_IntMap s) -> WF (VarSet_IntMap t) ->
  (disjointVarSet s t = true <->
   forall v, elemVarSet v s = true -> elemVarSet v t = false).
Proof.
  intros W X. destruct s as [[m]], t as [[n]].
  unfold disjointVarSet, UniqSet.getUniqSet, UniqFM.disjointUFM.
  rewrite (IntMapUnionProofs.disjoint_spec m n W X).
  split.
  - intros H v M. specialize (H (key v)).
    rewrite (elemVarSet_lookup _ _ W) in M.
    rewrite (elemVarSet_lookup _ _ X).
    rewrite !lookupVarSet_IntMap in *.
    cbn beta in H, M |- *. cbn [VarSet_IntMap] in M |- *.
    destruct H as [H|H]; [rewrite H in M; discriminate|rewrite H; reflexivity].
  - intros H k.
    destruct (Data.IntMap.Internal.lookup k m) as [v|] eqn:L; [|left; reflexivity].
    right.
    pose (q := setVarUnique v (Unique.MkUnique k)).
    assert (K : key q = k) by (unfold q; destruct v; reflexivity).
    assert (M : elemVarSet q (UniqSet.Mk_UniqSet (UniqFM.UFM m)) = true).
    { rewrite (elemVarSet_lookup _ _ W), lookupVarSet_IntMap.
      cbn [VarSet_IntMap]. cbn beta. rewrite K, L. reflexivity. }
    specialize (H q M). rewrite (elemVarSet_lookup _ _ X), lookupVarSet_IntMap in H.
    cbn [VarSet_IntMap] in H. cbn beta in H. rewrite K in H.
    destruct (Data.IntMap.Internal.lookup k n); [discriminate|reflexivity].
Qed.

#[export] Hint Resolve intersectVarSet_WF intersectVarSet_valid : varset_invariant.

Print Assumptions intersectVarSet_valid.
Print Assumptions disjointVarSet_spec.

(* The fold visits stored values, not arbitrary representatives with the same
   unique. Membership-only specifications therefore need predicate respect. *)
Local Definition fold_values {a b} (f : a -> b -> b) (z : b)
  (m : Data.IntMap.Internal.IntMap a) : b :=
  let fix go z' m' :=
    match z', m' with
    | z'', Data.IntMap.Internal.Nil => z''
    | z'', Data.IntMap.Internal.Tip _ v => f v z''
    | z'', Data.IntMap.Internal.Bin _ _ l r => go (go z'' r) l
    end in go z m.

Local Lemma foldr_values {a b} (f : a -> b -> b) z m :
  Data.IntMap.Internal.foldr f z m = fold_values f z m.
Proof. destruct m as [pr [|mask] l r|k v|]; reflexivity. Qed.

Local Lemma fold_all_values {a} (p : a -> bool) m z :
  fold_values (fun v b => andb (p v) b) z m = true <->
  z = true /\ forall k v, ContainerProofs.tree_elem_kv k v m -> p v = true.
Proof.
  revert z. induction m as [pr mask l IHl r IHr|k v|]; intro z.
  - cbn [fold_values]. rewrite IHl, IHr.
    cbn [ContainerProofs.tree_elem_kv]. firstorder.
  - cbn [fold_values ContainerProofs.tree_elem_kv]. rewrite Bool.andb_true_iff.
    split.
    + intros [P Z]. split; [exact Z|]. intros k' v' [E F]. subst. exact P.
    + intros [Z P]. split; [apply (P k v); auto|exact Z].
  - cbn [fold_values ContainerProofs.tree_elem_kv]. firstorder.
Qed.

Local Lemma fold_any_values {a} (p : a -> bool) m z :
  fold_values (fun v b => orb (p v) b) z m = true <->
  z = true \/ exists k v, ContainerProofs.tree_elem_kv k v m /\ p v = true.
Proof.
  revert z. induction m as [pr mask l IHl r IHr|k v|]; intro z.
  - cbn [fold_values]. rewrite IHl, IHr.
    cbn [ContainerProofs.tree_elem_kv]. firstorder.
  - cbn [fold_values ContainerProofs.tree_elem_kv]. rewrite Bool.orb_true_iff.
    split.
    + intros [P|Z]; [right; exists k, v; auto|left; exact Z].
    + intros [Z|[k' [v' [[E F] P]]]]; [right; exact Z|]. subst. left. exact P.
  - cbn [fold_values ContainerProofs.tree_elem_kv]. firstorder.
Qed.

Lemma allVarSet_lookup_spec p s :
  WF (VarSet_IntMap s) -> ValidVarSet s ->
  (allVarSet p s = true <->
   forall q v, lookupVarSet s q = Some v -> p v = true).
Proof.
  intros W V. destruct s as [[m]].
  change (Data.IntMap.Internal.foldr (fun v b => andb (p v) b) true m = true <->
    forall q v, lookupVarSet (UniqSet.Mk_UniqSet (UniqFM.UFM m)) q = Some v -> p v = true).
  rewrite foldr_values, fold_all_values. split.
  - intros [_ H] q v L. apply (H (key q) v).
    apply ContainerProofs.lookup_tree_elem_kv. exact L.
  - intro H. split; [reflexivity|]. intros k v T.
    pose proof (ContainerProofs.tree_elem_kv_lookup _ k v m W T) as L.
    pose proof (ValidVarSet_lookup_key _ V k v L) as K.
    apply (H v v). rewrite lookupVarSet_IntMap.
    cbn [VarSet_IntMap]. cbn beta in K |- *. rewrite K. exact L.
Qed.

Lemma anyVarSet_lookup_spec p s :
  WF (VarSet_IntMap s) -> ValidVarSet s ->
  (anyVarSet p s = true <->
   exists q v, lookupVarSet s q = Some v /\ p v = true).
Proof.
  intros W V. destruct s as [[m]].
  change (Data.IntMap.Internal.foldr (fun v b => orb (p v) b) false m = true <->
    exists q v, lookupVarSet (UniqSet.Mk_UniqSet (UniqFM.UFM m)) q = Some v /\ p v = true).
  rewrite foldr_values, fold_any_values. split.
  - intros [E|[k [v [T P]]]]; [discriminate|].
    pose proof (ContainerProofs.tree_elem_kv_lookup _ k v m W T) as L.
    pose proof (ValidVarSet_lookup_key _ V k v L) as K.
    exists v, v. split; [|exact P]. rewrite lookupVarSet_IntMap.
    cbn [VarSet_IntMap]. cbn beta in K |- *. rewrite K. exact L.
  - intros [q [v [L P]]]. right. exists (key q), v. split; [|exact P].
    apply ContainerProofs.lookup_tree_elem_kv. exact L.
Qed.

Lemma lookupVarSet_eq_query s q v :
  GHC.Base.op_zeze__ q v = true -> lookupVarSet s q = lookupVarSet s v.
Proof.
  rewrite Var_eq_key. intro E. apply N.eqb_eq in E.
  rewrite !lookupVarSet_IntMap. cbn beta in E |- *. rewrite E. reflexivity.
Qed.

Lemma lookupVarSet_stored_self s q v :
  ValidVarSet s -> lookupVarSet s q = Some v -> lookupVarSet s v = Some v.
Proof.
  intros V L. rewrite <- (lookupVarSet_eq_query s q v (V q v L)). exact L.
Qed.

Lemma allVarSet_spec p s :
  WF (VarSet_IntMap s) -> ValidVarSet s ->
  (forall x y, GHC.Base.op_zeze__ x y = true -> p x = p y) ->
  (allVarSet p s = true <-> forall v, elemVarSet v s = true -> p v = true).
Proof.
  intros W V R. rewrite (allVarSet_lookup_spec p s W V). split.
  - intros H q M. destruct (elemVarSet_lookup_some s q W M) as [v L].
    rewrite (R q v (V q v L)). exact (H q v L).
  - intros H q v L. apply H.
    eapply lookupVarSet_member; [exact W|].
    exact (lookupVarSet_stored_self s q v V L).
Qed.

Lemma anyVarSet_spec p s :
  WF (VarSet_IntMap s) -> ValidVarSet s ->
  (forall x y, GHC.Base.op_zeze__ x y = true -> p x = p y) ->
  (anyVarSet p s = true <-> exists v, elemVarSet v s = true /\ p v = true).
Proof.
  intros W V R. rewrite (anyVarSet_lookup_spec p s W V). split.
  - intros [q [v [L P]]]. exists v. split; [|exact P].
    eapply lookupVarSet_member; [exact W|].
    exact (lookupVarSet_stored_self s q v V L).
  - intros [q [M P]]. destruct (elemVarSet_lookup_some s q W M) as [v L].
    exists q, v. split; [exact L|].
    rewrite <- (R q v (V q v L)). exact P.
Qed.

Lemma elemVarSet_filter p s q :
  WF (VarSet_IntMap s) -> ValidVarSet s ->
  (forall x y, GHC.Base.op_zeze__ x y = true -> p x = p y) ->
  elemVarSet q (filterVarSet p s) = andb (elemVarSet q s) (p q).
Proof.
  intros W V R. rewrite (elemVarSet_lookup _ _ (filterVarSet_WF p s W)),
    (lookupVarSet_filter p s q W), (elemVarSet_lookup s q W).
  destruct (lookupVarSet s q) as [v|] eqn:L; [|reflexivity].
  rewrite (R q v (V q v L)). destruct (p v); reflexivity.
Qed.

Print Assumptions allVarSet_spec.
Print Assumptions anyVarSet_spec.
Print Assumptions elemVarSet_filter.
