From Stdlib Require Import Lists.List Bool.Bool Sorting.Sorted micromega.Lia Strings.String Arith.Wf_nat ZArith.ZArith.
Require Import FingerTreeProofs.IntervalModel FingerTreeProofs.CoreModel
  FingerTreeProofs.CoreOperations FingerTreeProofs.CoreSearch FingerTreeProofs.CoreSize
  FingerTreeProofs.CoreTraversal FingerTreeProofs.ApplicativeValidity.
Import ListNotations.
Set Implicit Arguments.

Section Operations.
Context {K : Type} `{GHC.Base.Ord K} (laws : EndpointOrderLaws).
Local Abbreviation le := GHC.Base.op_zlze__.
Local Abbreviation MU A := (@Data.FingerTree.measure (IM.IntInterval K) (IM.Node K A)
  IM.Semigroup__IntInterval IM.Monoid__IntInterval IM.Measured__IntInterval__Node).
Local Ltac monoid_laws := first [exact (intervalUnion_assoc laws)|
  exact intervalUnion_left_id|exact intervalUnion_right_id].

Lemma low_spec (lo hi : K) : IM.low (IM.MkInterval lo hi) = lo.
Proof. reflexivity. Qed.
Lemma high_spec (lo hi : K) : IM.high (IM.MkInterval lo hi) = hi.
Proof. reflexivity. Qed.
Lemma point_spec k : IM.low (IM.point k) = k /\ IM.high (IM.point k) = k /\ closed (IM.point k).
Proof. repeat split; try reflexivity; apply endpoint_refl; exact laws. Qed.

Lemma empty_spec {A} : entries (@IM.empty K A _ _) = [] /\ valid (@IM.empty K A _ _).
Proof.
  split; [reflexivity|]. split; [exact laws|]. split; [exact I|].
  split; constructor.
Qed.
Lemma singleton_spec {A} i (a : A) :
  entries (IM.singleton i a) = [(i,a)] /\ (valid (IM.singleton i a) <-> closed i).
Proof.
  split; [reflexivity|]; split.
  - intros [_ [_ [C _]]]; inversion C; assumption.
  - intro C; split; [exact laws|]. split; [exact I|]. split.
    + constructor; [exact C|constructor].
    + constructor; constructor.
Qed.
Lemma insert_reversed {A} lo hi (a : A) m : le lo hi = false ->
  IM.insert (IM.MkInterval lo hi) a m = m.
Proof. intro E; cbn [IM.insert]; rewrite endpoint_gt, E by exact laws; reflexivity. Qed.

(* The fallback argument is used only in this specification. Original error
   branches remain untouched. CoreSearch proves equality by inspecting only
   actual nonempty-prefix applications, not by postulating p mempty. *)
Lemma split_summary_safe {A} (t : Data.FingerTree.FingerTree (IM.IntInterval K) (IM.Node K A))
  (p q : IM.IntInterval K -> bool) :
  validity IM.Measured__IntInterval__Node t ->
  (forall i h, p (IM.MkIntInterval i h) = q (IM.MkIntInterval i h)) ->
  Data.FingerTree.split p t = Data.FingerTree.split q t.
Proof.
  intros V E; eapply split_parametric_on_nonempty_prefixes; try monoid_laws; [exact V|].
  intros w D; destruct (prefix_summary_nonempty D) as [i [h ->]]; apply E.
Qed.

Lemma atleast_split_safe {A} k fallback (m : IM.IntervalMap K A) : cacheValid m ->
  Data.FingerTree.split (IM.atleast k) (rawTree m) =
  Data.FingerTree.split (fun w => match w with
    | IM.NoInterval => fallback | IM.MkIntInterval _ h => le k h end) (rawTree m).
Proof. intro V; apply split_summary_safe; [exact V|reflexivity]. Qed.

Lemma greater_split_safe {A} k fallback (m : IM.IntervalMap K A) : cacheValid m ->
  Data.FingerTree.split (IM.greater k) (rawTree m) =
  Data.FingerTree.split (summaryTest (fun i => GHC.Base.op_zg__ (IM.low i) k) fallback) (rawTree m).
Proof. intro V; apply split_summary_safe; [exact V|reflexivity]. Qed.

Lemma larger_split_safe {A} i fallback (m : IM.IntervalMap K A) : cacheValid m ->
  Data.FingerTree.split (fun w => match w with
    | IM.NoInterval => GHC.Err.error (GHC.Base.hs_string__ "larger NoInterval")
    | IM.MkIntInterval j _ => GHC.Base.op_zgze__ j i end) (rawTree m) =
  Data.FingerTree.split (summaryTest (fun j => GHC.Base.op_zgze__ j i) fallback) (rawTree m).
Proof. intro V; apply split_summary_safe; [exact V|reflexivity]. Qed.

Lemma strict_larger_split_safe {A} i fallback (m : IM.IntervalMap K A) : cacheValid m ->
  Data.FingerTree.split (fun w => match w with
    | IM.NoInterval => GHC.Err.error (GHC.Base.hs_string__ "larger NoInterval")
    | IM.MkIntInterval j _ => GHC.Base.op_zg__ j i end) (rawTree m) =
  Data.FingerTree.split (summaryTest (fun j => GHC.Base.op_zg__ j i) fallback) (rawTree m).
Proof. intro V; apply split_summary_safe; [exact V|reflexivity]. Qed.

Lemma interval_split_domain {A} p (m : IM.IntervalMap K A) : cacheValid m ->
  match rawTree m with
  | Data.FingerTree.Empty => True
  | _ => (exists i h, Data.FingerTree.measure (rawTree m) = IM.MkIntInterval i h) /\
    splitCalls IM.Measured__IntInterval__Node
      (nonemptyPrefixDomain (MU A) (contents (rawTree m))) p GHC.Base.mempty (rawTree m)
  end.
Proof.
  intro V.
  (* Parametricity above gives semantic error unreachability; the original
     prefix-domain certificate additionally records all internal tests. *)
  pose proof (@split_domain_certificate (IM.IntInterval K) IM.Semigroup__IntInterval
    IM.Monoid__IntInterval (intervalUnion_assoc laws) intervalUnion_left_id intervalUnion_right_id
    _ IM.Measured__IntInterval__Node p (rawTree m) V) as C.
  destruct (rawTree m) as [|x|c pr mid sf] eqn:T; [exact I|..];
    destruct C as [Total Calls]; split.
  - exact (prefix_summary_nonempty Total).
  - exact Calls.
  - exact (prefix_summary_nonempty Total).
  - exact Calls.
Qed.

Lemma leastView_spec {A} (m : IM.IntervalMap K A) : valid m ->
  match IM.leastView m with
  | None => entries m = []
  | Some (e,r) => entries m = e :: entries r /\ valid r
  end.
Proof.
  destruct m as [t]; intros [L [V [C S]]].
  pose proof (@viewl_contentsWith (IM.IntInterval K) IM.Semigroup__IntInterval
    IM.Monoid__IntInterval _ t IM.Measured__IntInterval__Node
    _ (fun x => [x])) as E.
  pose proof (@viewl_validityWith (IM.IntInterval K) IM.Semigroup__IntInterval
    IM.Monoid__IntInterval (intervalUnion_assoc laws) intervalUnion_right_id
    _ t IM.Measured__IntInterval__Node (fun _ => True) V) as Vr.
  unfold IM.leastView; destruct (Data.FingerTree.viewl t) as [|[i a] r] eqn:T.
  - unfold entries, rawTree, contents; rewrite E; reflexivity.
  - assert (EE : entries (IM.MkIntervalMap t) = (i,a) :: entries (IM.MkIntervalMap r)).
    { unfold entries, rawTree, contents; rewrite E; reflexivity. }
    split; [exact EE|]. split; [exact L|]. split; [exact (proj1 (proj2 Vr))|].
    rewrite EE in C, S; inversion C; inversion S; subst; split; assumption.
Qed.

Lemma leastView_none_iff {A} (m : IM.IntervalMap K A) : valid m ->
  (IM.leastView m = None <-> entries m = []).
Proof.
  intro V; pose proof (leastView_spec V) as S; destruct (IM.leastView m) as [[e r]|];
    cbn in S; [destruct S as [E _]; rewrite E; split; discriminate|tauto].
Qed.

Lemma bounds_none_iff {A} (m : IM.IntervalMap K A) : cacheValid m ->
  (IM.bounds m = None <-> entries m = []).
Proof.
  destruct m as [t]; intro V.
  pose proof (measure_entries laws (IM.MkIntervalMap t) V) as M.
  pose proof (@viewl_contentsWith (IM.IntInterval K) IM.Semigroup__IntInterval
    IM.Monoid__IntInterval _ t IM.Measured__IntInterval__Node _ (fun x => [x])) as E.
  unfold IM.bounds; change (Data.FingerTree.measure t = summary (entries (IM.MkIntervalMap t))) in M.
  rewrite M; destruct (summary (entries (IM.MkIntervalMap t))) as [|i h] eqn:Sm.
  - apply summary_empty_iff in Sm; tauto.
  - destruct (Data.FingerTree.viewl t) as [|[[lo hi] a] r] eqn:T.
    + assert (Z : entries (IM.MkIntervalMap t) = []) by (unfold entries, rawTree, contents; rewrite E; reflexivity).
      rewrite Z in Sm; discriminate.
    + split; [discriminate|intro Z; rewrite Z in Sm; discriminate].
Qed.

Lemma bounds_endpoints {A} (m : IM.IntervalMap K A) b : cacheValid m ->
  IM.bounds m = Some b ->
  exists i a rest, entries m = (i,a) :: rest /\ IM.low b = IM.low i /\
    (exists e, In e (entries m) /\ IM.high (fst e) = IM.high b) /\
    (forall e, In e (entries m) -> le (IM.high (fst e)) (IM.high b) = true) /\
    (forall z, (forall e, In e (entries m) -> le (IM.high (fst e)) z = true) ->
      le (IM.high b) z = true).
Proof.
  destruct m as [t]; intro V.
  pose proof (measure_entries laws (IM.MkIntervalMap t) V) as M.
  pose proof (@viewl_contentsWith (IM.IntInterval K) IM.Semigroup__IntInterval
    IM.Monoid__IntInterval _ t IM.Measured__IntInterval__Node _ (fun x => [x])) as E.
  unfold IM.bounds; change (Data.FingerTree.measure t = summary (entries (IM.MkIntervalMap t))) in M.
  rewrite M; destruct (summary (entries (IM.MkIntervalMap t))) as [|j h] eqn:Sm; [discriminate|].
  destruct (Data.FingerTree.viewl t) as [|[[lo hi] a] r]; [discriminate|].
  intro Out; injection Out as Eb; subst b.
  exists (IM.MkInterval lo hi), a, (entries (IM.MkIntervalMap r)); split.
  - unfold entries, rawTree, contents; rewrite E; reflexivity.
  - split; [reflexivity|].
    exact (proj2 (summary_endpoints laws _ Sm)).
Qed.

Definition encloses (outer inner : IM.Interval K) : Prop :=
  le (IM.low outer) (IM.low inner) = true /\ le (IM.high inner) (IM.high outer) = true.

Lemma bounds_enclosing {A} (m : IM.IntervalMap K A) b : valid m -> IM.bounds m = Some b ->
  closed b /\ Forall (fun e => encloses b (fst e)) (entries m) /\
  (forall c, Forall (fun e => encloses c (fst e)) (entries m) -> encloses c b).
Proof.
  intros [L [V [C S]]] Out.
  destruct (bounds_endpoints m V Out) as [i [a [rest [E [Low [Att [Upper Least]]]]]]].
  rewrite E in C, S; inversion C as [|? ? Ci Cr]; subst.
  inversion S as [|? ? Sr All]; subst.
  assert (Lower : forall e, In e (entries m) -> le (IM.low b) (IM.low (fst e)) = true).
  { intros e InE; rewrite E in InE; rewrite Low.
    destruct InE as [<-|InE]; [apply endpoint_refl; exact laws|].
    rewrite Forall_forall in All; exact (proj1 (All e InE)). }
  split.
  - unfold closed in *; rewrite Low; eapply endpoint_trans; [exact laws|exact Ci|].
    apply (Upper (i,a)); rewrite E; left; reflexivity.
  - split.
    + apply Forall_forall; intros e He; split; [apply Lower|apply Upper]; exact He.
    + intros c Fc; rewrite Forall_forall in Fc; split.
      * rewrite Low; exact (proj1 (Fc (i,a) ltac:(rewrite E; left; reflexivity))).
      * apply Least; intros e He; exact (proj2 (Fc e He)).
Qed.

Fixpoint breakNodes {A} (f : IM.Interval K -> bool) (ns : list (IM.Node K A)) :
  list (IM.Node K A) * list (IM.Node K A) :=
  match ns with
  | [] => ([],[])
  | IM.MkNode i a as n :: ns' =>
    if f i then ([],ns) else
      let '(l,r) := breakNodes f ns' in (n::l,r)
  end.

Lemma splitList_summaryTest {A} f fallback (ns : list (IM.Node K A)) acc :
  splitListFrom (MU A) (summaryTest f fallback) acc ns = breakNodes f ns.
Proof.
  revert acc; induction ns as [|[i a] ns IH]; intro acc; [reflexivity|].
  cbn [splitListFrom breakNodes].
  assert (E : summaryTest f fallback (GHC.Base.mappend acc ((MU A) (IM.MkNode i a))) = f i).
  { destruct acc; reflexivity. }
  rewrite E; destruct (f i); [reflexivity|]. rewrite IH; reflexivity.
Qed.

Lemma sorted_firstn {T} (R : T -> T -> Prop) n xs :
  StronglySorted R xs -> StronglySorted R (List.firstn n xs).
Proof.
  intro Sorted; revert n; induction Sorted as [|x xs S IH All]; intros [|n]; cbn; try constructor.
  - apply IH.
  - apply Forall_forall; intros y Hy; rewrite Forall_forall in All; apply All.
    rewrite <- (firstn_skipn n xs); apply in_or_app; left; exact Hy.
Qed.

Lemma in_firstn_mono {T} (x : T) i j xs : i <= j -> In x (firstn i xs) -> In x (firstn j xs).
Proof.
  revert i j; induction xs as [|a xs IH]; intros [|i] [|j] B InE; cbn in *;
    try contradiction; try lia.
  destruct InE as [<-|InE]; [left; reflexivity|right; apply (IH i j); [lia|exact InE]].
Qed.

Lemma summaryTest_prefixMonotone {A} f fallback (ns : list (IM.Node K A)) :
  (forall i j, intervalLE i j -> f i = true -> f j = true) ->
  StronglySorted entryLE (List.map fullEntry ns) ->
  prefixMonotone (MU A) (summaryTest f fallback) ns.
Proof.
  intros Up Sorted i j Pos B Len Ti.
  rewrite summary_listMeasure in Ti |- *.
  assert (Ni : List.map fullEntry (firstn i ns) <> []).
  { intro E; apply map_eq_nil in E; destruct ns; cbn in *; [lia|]. destruct i; [lia|discriminate]. }
  assert (Nj : List.map fullEntry (firstn j ns) <> []).
  { intro E; apply map_eq_nil in E; destruct ns; cbn in *; [lia|]. destruct j; [lia|discriminate]. }
  assert (Si : StronglySorted entryLE (List.map fullEntry (firstn i ns))).
  { rewrite <- firstn_map; apply sorted_firstn; exact Sorted. }
  assert (Sj : StronglySorted entryLE (List.map fullEntry (firstn j ns))).
  { rewrite <- firstn_map; apply sorted_firstn; exact Sorted. }
  apply (proj2 (summary_test_exists laws f fallback Up Sj Nj)).
  destruct (proj1 (summary_test_exists laws f fallback Up Si Ni) Ti) as [e [He Fe]].
  exists e; split; [|exact Fe]. rewrite <- firstn_map in He |- *.
  eapply in_firstn_mono; eassumption.
Qed.

Lemma split_ordered_test {A} f fallback (m : IM.IntervalMap K A) l r :
  valid m -> (forall i j, intervalLE i j -> f i = true -> f j = true) ->
  Data.FingerTree.split (summaryTest f fallback) (rawTree m) = (l,r) ->
  breakNodes f (contents (rawTree m)) = (contents l, contents r) /\
  validity IM.Measured__IntInterval__Node l /\ validity IM.Measured__IntInterval__Node r.
Proof.
  intros [_ [V [_ Sorted]]] Up E; split.
  - rewrite <- (splitList_summaryTest f fallback _ GHC.Base.mempty).
    eapply split_correct; try monoid_laws; [exact V| |exact E].
    apply summaryTest_prefixMonotone; assumption.
  - pose proof (@split_validityWith (IM.IntInterval K) IM.Semigroup__IntInterval
      IM.Monoid__IntInterval (intervalUnion_assoc laws) intervalUnion_left_id intervalUnion_right_id
      _ IM.Measured__IntInterval__Node (fun _ => True) (summaryTest f fallback) (rawTree m) V) as C.
    rewrite E in C; exact C.
Qed.

Lemma filter_all_true {T} (p : T -> bool) xs : Forall (fun x => p x = true) xs ->
  Stdlib.Lists.List.filter p xs = xs /\ Stdlib.Lists.List.filter (fun x => negb (p x)) xs = [].
Proof.
  induction 1 as [|x xs E All [I J]]; cbn; [auto|rewrite E; cbn; rewrite I,J; auto].
Qed.

Lemma sorted_filter {T} (R : T -> T -> Prop) (p : T -> bool) xs :
  StronglySorted R xs -> StronglySorted R (Stdlib.Lists.List.filter p xs).
Proof.
  induction 1 as [|x xs S IH All]; cbn; [constructor|].
  destruct (p x); [constructor; [exact IH|]|exact IH].
  rewrite Forall_forall in *; intros y Hy; apply All.
  pose proof (proj1 (@List.filter_In T p y xs) Hy) as HH; tauto.
Qed.

Lemma breakNodes_filters {A} f (ns : list (IM.Node K A)) :
  (forall i j, intervalLE i j -> f i = true -> f j = true) ->
  StronglySorted entryLE (List.map fullEntry ns) ->
  List.map fullEntry (fst (breakNodes f ns)) =
    Stdlib.Lists.List.filter (fun e => negb (f (fst e))) (List.map fullEntry ns) /\
  List.map fullEntry (snd (breakNodes f ns)) =
    Stdlib.Lists.List.filter (fun e => f (fst e)) (List.map fullEntry ns).
Proof.
  intros Up; induction ns as [|[i a] ns IH]; intro S; [auto|].
  inversion S as [|? ? Sr All]; subst.
  cbn [breakNodes]; destruct (f i) eqn:F.
  - assert (Flags : Forall (fun e => f (fst e) = true) (List.map fullEntry ns)).
    { rewrite Forall_forall in *; intros e He; apply (Up i (fst e)); [apply All; exact He|exact F]. }
    destruct (filter_all_true (fun e => f (fst e)) Flags) as [Yes No].
    cbn [fst snd List.map fullEntry Stdlib.Lists.List.filter]; rewrite F; cbn; rewrite Yes, No; auto.
  - specialize (IH Sr); destruct (breakNodes f ns) as [l r]; cbn [fst snd] in IH.
    destruct IH as [E1 E2]; cbn [fst snd List.map fullEntry Stdlib.Lists.List.filter]; rewrite F;
      cbn; rewrite E1, E2; auto.
Qed.

Lemma split_ordered_filters {A} f fallback (m : IM.IntervalMap K A) l r :
  valid m -> (forall i j, intervalLE i j -> f i = true -> f j = true) ->
  Data.FingerTree.split (summaryTest f fallback) (rawTree m) = (l,r) ->
  entries (IM.MkIntervalMap l) = Stdlib.Lists.List.filter (fun e => negb (f (fst e))) (entries m) /\
  entries (IM.MkIntervalMap r) = Stdlib.Lists.List.filter (fun e => f (fst e)) (entries m) /\
  valid (IM.MkIntervalMap l) /\ valid (IM.MkIntervalMap r).
Proof.
  intros V Up E; destruct (split_ordered_test f fallback V Up E) as [B [Vl Vr]].
  destruct V as [L [Vm [Closed Sorted]]].
  destruct (breakNodes_filters f (contents (rawTree m)) Up Sorted) as [Bl Br]; rewrite B in Bl, Br.
  cbn [fst snd] in Bl, Br.
  split; [exact Bl|]; split; [exact Br|]; split; (split; [exact L|]);
    split; try assumption; split.
  - change (Forall (fun e => closed (fst e)) (List.map fullEntry (contents l))).
    rewrite Bl; apply Forall_forall; intros e He; apply List.filter_In in He.
    rewrite Forall_forall in Closed; apply Closed; tauto.
  - change (StronglySorted entryLE (List.map fullEntry (contents l))).
    rewrite Bl; apply sorted_filter; exact Sorted.
  - change (Forall (fun e => closed (fst e)) (List.map fullEntry (contents r))).
    rewrite Br; apply Forall_forall; intros e He; apply List.filter_In in He.
    rewrite Forall_forall in Closed; apply Closed; tauto.
  - change (StronglySorted entryLE (List.map fullEntry (contents r))).
    rewrite Br; apply sorted_filter; exact Sorted.
Qed.

Lemma greater_upward k i j : intervalLE i j ->
  GHC.Base.op_zg__ (IM.low i) k = true -> GHC.Base.op_zg__ (IM.low j) k = true.
Proof.
  intros [IJ _]; rewrite !endpoint_gt by exact laws.
  intros F; apply negb_true_iff in F; apply negb_true_iff.
  destruct (le (IM.low j) k) eqn:J; [|reflexivity].
  pose proof (@endpoint_trans K H H0 laws _ _ _ IJ J); congruence.
Qed.

Lemma splitAfter_spec {A} k (m : IM.IntervalMap K A) : valid m ->
  let '(l,r) := IM.splitAfter k m in
  valid l /\ valid r /\
  entries l = Stdlib.Lists.List.filter (fun e => le (IM.low (fst e)) k) (entries m) /\
  entries r = Stdlib.Lists.List.filter (fun e => GHC.Base.op_zg__ (IM.low (fst e)) k) (entries m).
Proof.
  intro V; destruct m as [t]; unfold IM.splitAfter.
  pose proof (@greater_split_safe A k false (IM.MkIntervalMap t) (proj1 (proj2 V))) as Safe.
  cbn [rawTree] in Safe; rewrite Safe.
  destruct (Data.FingerTree.split
    (summaryTest (fun i => GHC.Base.op_zg__ (IM.low i) k) false) t) as [l r] eqn:E.
  destruct (split_ordered_filters (fun i => GHC.Base.op_zg__ (IM.low i) k) false
    V (@greater_upward k) E)
    as [L [R [Vl Vr]]].
  split; [exact Vl|]; split; [exact Vr|]; split; [|exact R].
  rewrite L; apply Stdlib.Lists.List.filter_ext; intros [i a]; cbn.
  rewrite endpoint_gt, negb_involutive by exact laws; reflexivity.
Qed.

Fixpoint insertEntries {A} (e : IM.Interval K * A) (xs : list (IM.Interval K * A)) :=
  match xs with
  | [] => [e]
  | x :: xs' => if GHC.Base.op_zgze__ (fst x) (fst e) then e :: xs
    else x :: insertEntries e xs'
  end.

Lemma insertEntries_before_equals {A} i (a b : A) xs :
  insertEntries (i,a) ((i,b)::xs) = (i,a)::(i,b)::xs.
Proof.
  cbn [insertEntries fst]; assert (E : GHC.Base.op_zgze__ i i = true).
  { apply (proj2 (interval_ge_iff laws i i)); apply intervalLE_refl; exact laws. }
  now rewrite E.
Qed.

Lemma insertEntries_Forall {A} (P : IM.Interval K * A -> Prop) e xs :
  P e -> Forall P xs -> Forall P (insertEntries e xs).
Proof.
  intros Pe; induction 1 as [|x xs Px All IH]; cbn [insertEntries];
    [constructor; [exact Pe|constructor]|].
  destruct (GHC.Base.op_zgze__ (fst x) (fst e)); constructor; auto; constructor; auto.
Qed.

Lemma insertEntries_sorted {A} (e : IM.Interval K * A) xs :
  StronglySorted entryLE xs -> StronglySorted entryLE (insertEntries e xs).
Proof.
  induction 1 as [|x xs S IH All]; cbn [insertEntries]; [constructor; constructor|].
  destruct (GHC.Base.op_zgze__ (fst x) (fst e)) eqn:C.
  - apply (proj1 (interval_ge_iff laws _ _)) in C.
    constructor; [constructor; assumption|]. constructor; [exact C|].
    rewrite Forall_forall in *; intros y Hy; eapply intervalLE_trans; [exact laws|exact C|apply All; exact Hy].
  - assert (Xe : intervalLE (fst x) (fst e)).
    { destruct (intervalLE_total laws (fst x) (fst e)) as [E|E]; [exact E|].
      apply (proj2 (interval_ge_iff laws _ _)) in E; congruence. }
    constructor; [exact IH|apply insertEntries_Forall; assumption].
Qed.

Lemma breakNodes_insertEntries {A} i (a : A) ns :
  let '(l,r) := breakNodes (fun j => GHC.Base.op_zgze__ j i) ns in
  List.map fullEntry l ++ (i,a) :: List.map fullEntry r = insertEntries (i,a) (List.map fullEntry ns).
Proof.
  induction ns as [|[j b] ns IH]; [reflexivity|].
  cbn [breakNodes insertEntries List.map fullEntry fst].
  destruct (GHC.Base.op_zgze__ j i); [reflexivity|].
  destruct (breakNodes (fun j => GHC.Base.op_zgze__ j i) ns) as [l r].
  cbn [List.map List.app]; f_equal; exact IH.
Qed.

Lemma larger_upward i j k : intervalLE j k -> GHC.Base.op_zgze__ j i = true ->
  GHC.Base.op_zgze__ k i = true.
Proof.
  intros J F; apply (proj2 (interval_ge_iff laws _ _));
    eapply intervalLE_trans; [exact laws|apply (proj1 (interval_ge_iff laws _ _)); exact F|exact J].
Qed.

Lemma insert_spec {A} i (a : A) m : valid m -> closed i ->
  entries (IM.insert i a m) = insertEntries (i,a) (entries m) /\ valid (IM.insert i a m).
Proof.
  intros V Ci; destruct m as [t]; destruct i as [lo hi].
  unfold closed in Ci; cbn [IM.low IM.high] in Ci.
  unfold IM.insert; rewrite endpoint_gt, Ci by exact laws; cbn [negb].
  pose proof (@larger_split_safe A (IM.MkInterval lo hi) false (IM.MkIntervalMap t)
    (proj1 (proj2 V))) as Safe; cbn [rawTree] in Safe; rewrite Safe.
  destruct (Data.FingerTree.split
    (summaryTest (fun j => GHC.Base.op_zgze__ j (IM.MkInterval lo hi)) false) t) as [l r] eqn:E.
  destruct (split_ordered_test _ false V (@larger_upward (IM.MkInterval lo hi)) E) as [B [Vl Vr]].
  cbn [rawTree] in B.
  pose proof (@breakNodes_insertEntries A (IM.MkInterval lo hi) a (contents t)) as Ref.
  rewrite B in Ref.
  assert (Out : entries (IM.MkIntervalMap (Data.FingerTree.op_zgzl__ l
    (Data.FingerTree.consTree (IM.MkNode (IM.MkInterval lo hi) a) r))) =
    insertEntries (IM.MkInterval lo hi,a) (entries (IM.MkIntervalMap t))).
  { unfold entries, rawTree; rewrite append_contents, consTree_contents, List.map_app; exact Ref. }
  split; [exact Out|].
  destruct V as [L [Vm [C S]]]; split; [exact L|]; split.
  - unfold cacheValid, rawTree; apply append_validityWith; try monoid_laws; [exact Vl|].
    apply consTree_validityWith; try monoid_laws; [exact I|exact Vr].
  - rewrite Out; split; [apply insertEntries_Forall; [exact Ci|exact C]|].
    apply insertEntries_sorted; exact S.
Qed.

Lemma atleast_prefixMonotone {A} k (ns : list (IM.Node K A)) :
  prefixMonotone (MU A) (atleastTest k) ns.
Proof.
  intros i j Pos B Bound E; rewrite summary_listMeasure, summary_atleast in E |- * by exact laws.
  apply existsb_exists in E; destruct E as [e [He Fe]].
  apply existsb_exists; exists e; split; [|exact Fe].
  rewrite <- firstn_map in He |- *; eapply in_firstn_mono; eassumption.
Qed.

Lemma splitList_atleast {A} k (ns : list (IM.Node K A)) acc : atleastTest k acc = false ->
  splitListFrom (MU A) (atleastTest k) acc ns =
    breakNodes (fun i => le k (IM.high i)) ns.
Proof.
  revert acc; induction ns as [|[i a] ns IH]; intros acc F; [reflexivity|].
  cbn [splitListFrom breakNodes].
  assert (Test : atleastTest k (GHC.Base.mappend acc ((MU A) (IM.MkNode i a))) = le k (IM.high i)).
  { change (atleastTest k (IM.intervalUnion acc (IM.MkIntInterval i (IM.high i))) = le k (IM.high i)).
    rewrite (atleastTest_union laws), F; reflexivity. }
  rewrite Test; destruct (le k (IM.high i)) eqn:E; [reflexivity|].
  rewrite IH; [reflexivity|now rewrite Test].
Qed.

Lemma breakNodes_reconstruct {A} f (ns : list (IM.Node K A)) :
  ns = fst (breakNodes f ns) ++ snd (breakNodes f ns).
Proof.
  induction ns as [|[i a] ns IH]; [reflexivity|].
  cbn [breakNodes]; destruct (f i); [reflexivity|].
  destruct (breakNodes f ns) as [l r]; cbn [fst snd List.app] in *; now rewrite <- IH.
Qed.
Lemma breakNodes_filter_suffix {A} f (ns : list (IM.Node K A)) :
  Stdlib.Lists.List.filter (fun e => f (fst e)) (List.map fullEntry ns) =
    Stdlib.Lists.List.filter (fun e => f (fst e)) (List.map fullEntry (snd (breakNodes f ns))).
Proof.
  induction ns as [|[i a] ns IH]; [reflexivity|].
  cbn [breakNodes]; destruct (f i) eqn:E; [reflexivity|].
  destruct (breakNodes f ns) as [l r]; cbn [fst snd] in *.
  cbn [List.map fullEntry Stdlib.Lists.List.filter fst]; rewrite ?E; exact IH.
Qed.
Lemma breakNodes_head {A} f (ns : list (IM.Node K A)) i a rs :
  snd (breakNodes f ns) = IM.MkNode i a :: rs -> f i = true.
Proof.
  induction ns as [|[j b] ns IH]; cbn [breakNodes]; [discriminate|].
  destruct (f j) eqn:F; [cbn [snd]; intro E; injection E as E1 E2 E3; subst; exact F|].
  destruct (breakNodes f ns); cbn [snd] in *; apply IH.
Qed.

Lemma sorted_suffix {T} (R : T -> T -> Prop) pre xs :
  StronglySorted R (pre ++ xs) -> StronglySorted R xs.
Proof. induction pre; cbn; [auto|intro S; inversion S; auto]. Qed.

Lemma valid_suffix {A} (m r : IM.IntervalMap K A) pre : valid m -> cacheValid r ->
  entries m = pre ++ entries r -> valid r.
Proof.
  intros [L [V [C S]]] Vr E; split; [exact L|]; split; [exact Vr|]; split.
  - rewrite E, Forall_app in C; tauto.
  - rewrite E in S; eapply sorted_suffix; exact S.
Qed.

Lemma dropUntil_atleast_step {A} k (m : IM.IntervalMap K A) : valid m ->
  match Data.FingerTree.viewl (Data.FingerTree.dropUntil (IM.atleast k) (rawTree m)) with
  | Data.FingerTree.EmptyL =>
      Stdlib.Lists.List.filter (fun e => le k (IM.high (fst e))) (entries m) = []
  | Data.FingerTree.op_ZCzl__ (IM.MkNode i a) r =>
      Stdlib.Lists.List.filter (fun e => le k (IM.high (fst e))) (entries m) =
        (i,a) :: Stdlib.Lists.List.filter (fun e => le k (IM.high (fst e))) (entries (IM.MkIntervalMap r)) /\
      valid (IM.MkIntervalMap r)
  end.
Proof.
  intro V; pose proof (proj1 (proj2 V)) as Vm.
  assert (Safe : Data.FingerTree.split (IM.atleast k) (rawTree m) =
    Data.FingerTree.split (atleastTest k) (rawTree m)).
  { apply split_summary_safe; [exact Vm|reflexivity]. }
  assert (Cut : contents (Data.FingerTree.dropUntil (IM.atleast k) (rawTree m)) =
    snd (breakNodes (fun i => le k (IM.high i)) (contents (rawTree m)))).
  { unfold Data.FingerTree.dropUntil, GHC.Base.op_z2218U__, Data.Tuple.snd; rewrite Safe.
    destruct (Data.FingerTree.split (atleastTest k) (rawTree m)) as [l r] eqn:E.
    pose proof (@split_correct (IM.IntInterval K) IM.Semigroup__IntInterval IM.Monoid__IntInterval
      (intervalUnion_assoc laws) intervalUnion_left_id intervalUnion_right_id _
      IM.Measured__IntInterval__Node (atleastTest k) (rawTree m) l r Vm (atleast_prefixMonotone k _) E) as C.
    unfold splitReference in C; rewrite splitList_atleast in C by reflexivity.
    rewrite C; reflexivity. }
  pose proof (breakNodes_filter_suffix (fun i => le k (IM.high i)) (contents (rawTree m))) as F.
  rewrite <- Cut in F.
  pose proof (breakNodes_reconstruct (fun i => le k (IM.high i)) (contents (rawTree m))) as Recon.
  rewrite <- Cut in Recon.
  pose proof (@viewl_contentsWith (IM.IntInterval K) IM.Semigroup__IntInterval IM.Monoid__IntInterval _
    (Data.FingerTree.dropUntil (IM.atleast k) (rawTree m)) IM.Measured__IntInterval__Node _ (fun x => [x])) as View.
  assert (VD : validity IM.Measured__IntInterval__Node (Data.FingerTree.dropUntil (IM.atleast k) (rawTree m))).
  { unfold Data.FingerTree.dropUntil, GHC.Base.op_z2218U__, Data.Tuple.snd.
    pose proof (@split_validityWith (IM.IntInterval K) IM.Semigroup__IntInterval IM.Monoid__IntInterval
      (intervalUnion_assoc laws) intervalUnion_left_id intervalUnion_right_id _
      IM.Measured__IntInterval__Node (fun _ => True) (IM.atleast k) (rawTree m) Vm) as C.
    destruct (Data.FingerTree.split (IM.atleast k) (rawTree m)); exact (proj2 C). }
  pose proof (@viewl_validityWith (IM.IntInterval K) IM.Semigroup__IntInterval IM.Monoid__IntInterval
    (intervalUnion_assoc laws) intervalUnion_right_id _
    (Data.FingerTree.dropUntil (IM.atleast k) (rawTree m)) IM.Measured__IntInterval__Node (fun _ => True) VD) as VR.
  destruct (Data.FingerTree.viewl (Data.FingerTree.dropUntil (IM.atleast k) (rawTree m))) as [|[i a] r] eqn:ViewE.
  - unfold entries; unfold contents in F; rewrite View in F; exact F.
  - assert (Trigger : le k (IM.high i) = true).
    { apply (@breakNodes_head A (fun i => le k (IM.high i)) (contents (rawTree m)) i a (contents r)).
      rewrite <- Cut; exact View. }
    split.
    + unfold entries; unfold contents in F; rewrite View in F.
      cbn [List.app List.map fullEntry Stdlib.Lists.List.filter fst] in F; rewrite Trigger in F; exact F.
    + apply (valid_suffix (m := m) (IM.MkIntervalMap r) (List.map fullEntry
        (fst (breakNodes (fun i => le k (IM.high i)) (contents (rawTree m)))) ++ [(i,a)]));
        [exact V|exact (proj1 (proj2 VR))|].
      unfold entries, rawTree; rewrite Recon at 1; rewrite List.map_app; unfold contents.
      rewrite View; cbn [List.app List.map fullEntry]; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma takeUntil_greater_spec {A} k (m : IM.IntervalMap K A) : valid m ->
  valid (IM.MkIntervalMap (Data.FingerTree.takeUntil (IM.greater k) (rawTree m))) /\
  entries (IM.MkIntervalMap (Data.FingerTree.takeUntil (IM.greater k) (rawTree m))) =
    Stdlib.Lists.List.filter (fun e => le (IM.low (fst e)) k) (entries m).
Proof.
  intro V; pose proof (splitAfter_spec k V) as S.
  destruct m as [t]; unfold IM.splitAfter in S.
  unfold Data.FingerTree.takeUntil, GHC.Base.op_z2218U__, Data.Tuple.fst; cbn [rawTree].
  destruct (Data.FingerTree.split (IM.greater k) t) as [l r]; cbn in S.
  split; [exact (proj1 S)|exact (proj1 (proj2 (proj2 S)))].
Qed.

Lemma filter_two {T} (p q : T -> bool) xs :
  Stdlib.Lists.List.filter p (Stdlib.Lists.List.filter q xs) =
  Stdlib.Lists.List.filter (fun x => andb (q x) (p x)) xs.
Proof. induction xs as [|x xs IH]; cbn; [reflexivity|].
  destruct (q x) eqn:Q, (p x) eqn:P; cbn; rewrite ?P, IH; reflexivity. Qed.

(* Only the library's proved WF equation is used here. It introduces the
   explicitly permitted dependent functional extensionality, not operation or
   recursion assumptions. The local worker is extracted from the actual body. *)
Lemma inRange_spec {A} lo hi (m : IM.IntervalMap K A) : valid m ->
  IM.inRange lo hi m = Stdlib.Lists.List.filter
    (fun e => andb (le (IM.low (fst e)) hi) (le lo (IM.high (fst e)))) (entries m).
Proof.
  intro V; destruct m as [t].
  destruct (takeUntil_greater_spec hi V) as [VT ET].
  unfold IM.inRange.
  match goal with |- context [HsToRocq.Wf.wfFix1 ?R ?rank ?WF ?body] =>
    set (worker := HsToRocq.Wf.wfFix1 R rank WF body);
    assert (Worker : forall xs, valid (IM.MkIntervalMap xs) ->
      worker xs = Stdlib.Lists.List.filter (fun e => le lo (IM.high (fst e)))
        (entries (IM.MkIntervalMap xs)))
  end.
  - intro xs; remember (size xs) as n eqn:N; revert xs N.
    induction n as [n IH] using lt_wf_ind; intros xs N VX.
    pose proof (dropUntil_atleast_step lo VX) as Step.
    cbn [rawTree] in Step.
    unfold worker at 1; rewrite HsToRocq.Wf.wfFix1_eq.
    fold worker; cbn beta zeta; cbn [proj1_sig].
    destruct (Data.FingerTree.viewl (Data.FingerTree.dropUntil (IM.atleast lo) xs)) as [|[i a] r] eqn:D.
    + symmetry; exact Step.
    + destruct Step as [F VR]; rewrite F; f_equal.
      apply (IH (size r)); [|reflexivity|exact VR].
      pose proof (viewl_size_lt IM.Measured__IntInterval__Node
        (Data.FingerTree.dropUntil (IM.atleast lo) xs) (IM.MkNode i a) r D) as ViewBound.
      pose proof (dropUntil_size_le intervalUnion_right_id IM.Measured__IntInterval__Node (IM.atleast lo) xs) as DropBound.
      lia.
  - rewrite Worker by exact VT.
    cbn [rawTree] in ET; rewrite ET, filter_two; reflexivity.
Qed.

Lemma search_spec {A} p (m : IM.IntervalMap K A) : valid m ->
  IM.search p m = Stdlib.Lists.List.filter
    (fun e => andb (le (IM.low (fst e)) p) (le p (IM.high (fst e)))) (entries m).
Proof. apply inRange_spec. Qed.
Lemma intersections_spec {A} q (m : IM.IntervalMap K A) : valid m -> closed q ->
  IM.intersections q m = Stdlib.Lists.List.filter
    (fun e => andb (le (IM.low (fst e)) (IM.high q)) (le (IM.low q) (IM.high (fst e)))) (entries m).
Proof. intros V _; apply inRange_spec; exact V. Qed.
Lemma dominators_spec {A} q (m : IM.IntervalMap K A) : valid m -> closed q ->
  IM.dominators q m = Stdlib.Lists.List.filter
    (fun e => andb (le (IM.low (fst e)) (IM.low q)) (le (IM.high q) (IM.high (fst e)))) (entries m).
Proof. intros V _; apply inRange_spec; exact V. Qed.

Definition mapEntry {A B} (f : A -> B) (e : IM.Interval K * A) : IM.Interval K * B :=
  (fst e, f (snd e)).

Lemma fmap_entries {A B} (f : A -> B) (m : IM.IntervalMap K A) :
  entries (GHC.Base.fmap f m) = List.map (mapEntry f) (entries m).
Proof.
  destruct m as [t]; change (List.map fullEntry
    (contents (Data.FingerTree.unsafeFmap (GHC.Base.fmap f) t)) =
    List.map (mapEntry f) (List.map fullEntry (contents t))).
  rewrite unsafeFmap_contents, !List.map_map; apply List.map_ext; intros [i a]; reflexivity.
Qed.

Lemma fmap_node_measure {A B} (f : A -> B) (n : IM.Node K A) :
  (MU B) (GHC.Base.fmap f n) = (MU A) n.
Proof. destruct n; reflexivity. Qed.

Lemma sorted_mapEntry {A B} (f : A -> B) xs :
  StronglySorted entryLE xs -> StronglySorted entryLE (List.map (mapEntry f) xs).
Proof.
  induction 1 as [|x xs S IH All]; cbn; constructor; [exact IH|].
  rewrite Forall_forall in *; intros y Hy; apply in_map_iff in Hy.
  destruct Hy as [z [<- Hz]]; apply All; exact Hz.
Qed.

Lemma fmap_valid {A B} (f : A -> B) (m : IM.IntervalMap K A) :
  valid m -> valid (GHC.Base.fmap f m).
Proof.
  intros [L [V [C S]]]; split; [exact L|]; split.
  - destruct m as [t]; change (validity IM.Measured__IntInterval__Node
      (Data.FingerTree.unsafeFmap (GHC.Base.fmap f) t)).
    eapply unsafeFmap_validityWith; [|exact V].
    intros [i a] _; split; reflexivity.
  - rewrite fmap_entries; split.
    + rewrite Forall_forall in *; intros e He; apply in_map_iff in He.
      destruct He as [[i a] [<- He]]; apply (C (i,a)); exact He.
    + apply sorted_mapEntry; exact S.
Qed.

Lemma fmap_identity_entries {A} (m : IM.IntervalMap K A) : entries (GHC.Base.fmap (fun x => x) m) = entries m.
Proof. rewrite fmap_entries; rewrite <- (List.map_id (entries m)) at 2.
  apply List.map_ext; intros [i a]; reflexivity. Qed.
Lemma fmap_composition_entries {A B C} (f : A -> B) (g : B -> C) (m : IM.IntervalMap K A) :
  entries (GHC.Base.fmap g (GHC.Base.fmap f m)) = entries (GHC.Base.fmap (fun x => g (f x)) m).
Proof. rewrite !fmap_entries, List.map_map; apply List.map_ext; intros [i a]; reflexivity. Qed.

Lemma replace_entries {A B} (a : A) (m : IM.IntervalMap K B) :
  entries (GHC.Base.op_zlzd__ a m) = List.map (fun e => (fst e,a)) (entries m).
Proof. change (entries (GHC.Base.fmap (fun _ => a) m) = List.map (fun e => (fst e,a)) (entries m)).
  rewrite fmap_entries; apply List.map_ext; intros [i b]; reflexivity. Qed.

Section Foldable.
Context {M : Type} {S : GHC.Base.Semigroup M} {D : GHC.Base.Monoid M}.
Hypothesis assocM : forall x y z : M, GHC.Base.mappend (GHC.Base.mappend x y) z = GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis leftM : forall x : M, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis rightM : forall x : M, GHC.Base.mappend x GHC.Base.mempty = x.
Lemma foldMap_payloads {A} (f : A -> M) (m : IM.IntervalMap K A) :
  Data.Foldable.foldMap f m = List.fold_right
    (fun e acc => GHC.Base.mappend (f (snd e)) acc) GHC.Base.mempty (entries m).
Proof.
  destruct m as [t]; change (Data.Foldable.foldMap (fun n : IM.Node K A => Data.Foldable.foldMap f n) t =
    List.fold_right (fun e acc => GHC.Base.mappend (f (snd e)) acc) GHC.Base.mempty (entries (IM.MkIntervalMap t))).
  rewrite (@foldMap_contents M S D assocM leftM rightM).
  unfold entries, rawTree, listMeasure.
  induction (contents t) as [|[i a] ns IH]; cbn [List.map List.fold_right fullEntry snd]; [reflexivity|].
  rewrite <- IH; reflexivity.
Qed.
End Foldable.

Lemma foldr_payloads {A B} (f : A -> B -> B) z (m : IM.IntervalMap K A) :
  Data.Foldable.foldr f z m = List.fold_right (fun e => f (snd e)) z (entries m).
Proof.
  change (Data.SemigroupInternal.appEndo
    (Data.Foldable.foldMap (fun a => Data.SemigroupInternal.Mk_Endo (f a)) m) z =
    List.fold_right (fun e => f (snd e)) z (entries m)).
  rewrite (@foldMap_payloads (Data.SemigroupInternal.Endo B) _ _
    ltac:(intros [x] [y] [w]; reflexivity) ltac:(intros [x]; reflexivity) ltac:(intros [x]; reflexivity)).
  induction (entries m) as [|[i a] xs IH]; cbn in *; [reflexivity|now rewrite IH].
Qed.

Lemma toList_payloads {A} (m : IM.IntervalMap K A) :
  Data.Foldable.toList m = List.map snd (entries m).
Proof.
  change (Data.Foldable.foldr (@cons A) [] m = List.map snd (entries m)); rewrite foldr_payloads.
  induction (entries m); cbn; congruence.
Qed.

Section Equality.
Context {A} {EA : GHC.Base.Eq_ A}.
Lemma node_equality_full (x y : IM.Node K A) :
  GHC.Base.op_zeze__ x y = GHC.Base.op_zeze__ (fullEntry x) (fullEntry y).
Proof. destruct x,y; reflexivity. Qed.
Lemma entry_list_equality (xs ys : list (IM.Node K A)) :
  GHC.Base.op_zeze__ xs ys = GHC.Base.op_zeze__ (List.map fullEntry xs) (List.map fullEntry ys).
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; try reflexivity.
  change (andb (GHC.Base.op_zeze__ x y) (GHC.Base.op_zeze__ xs ys) =
    andb (GHC.Base.op_zeze__ (fullEntry x) (fullEntry y))
      (GHC.Base.op_zeze__ (List.map fullEntry xs) (List.map fullEntry ys))).
  rewrite node_equality_full, IH; reflexivity.
Qed.
Lemma equality_entries (m n : IM.IntervalMap K A) :
  GHC.Base.op_zeze__ m n = GHC.Base.op_zeze__ (entries m) (entries n).
Proof.
  destruct m as [t], n as [u]; change (GHC.Base.op_zeze__ (Data.Foldable.toList t) (Data.Foldable.toList u) =
    GHC.Base.op_zeze__ (entries (IM.MkIntervalMap t)) (entries (IM.MkIntervalMap u))).
  rewrite !toList_contents; apply entry_list_equality.
Qed.
Lemma inequality_entries (m n : IM.IntervalMap K A) :
  GHC.Base.op_zsze__ m n = negb (GHC.Base.op_zeze__ (entries m) (entries n)).
Proof. change (negb (GHC.Base.op_zeze__ m n) = negb (GHC.Base.op_zeze__ (entries m) (entries n)));
  rewrite equality_entries; reflexivity. Qed.
Context {OA : GHC.Base.Ord A}.
Lemma node_compare_full (x y : IM.Node K A) :
  GHC.Base.compare x y = GHC.Base.compare (fullEntry x) (fullEntry y).
Proof. destruct x,y; reflexivity. Qed.
Lemma entry_list_compare (xs ys : list (IM.Node K A)) :
  GHC.Base.compare xs ys = GHC.Base.compare (List.map fullEntry xs) (List.map fullEntry ys).
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; try reflexivity.
  change (match GHC.Base.compare x y with Eq => GHC.Base.compare xs ys | c => c end =
    match GHC.Base.compare (fullEntry x) (fullEntry y) with
    | Eq => GHC.Base.compare (List.map fullEntry xs) (List.map fullEntry ys) | c => c end).
  rewrite node_compare_full, IH; reflexivity.
Qed.
Lemma compare_entries (m n : IM.IntervalMap K A) :
  GHC.Base.compare m n = GHC.Base.compare (entries m) (entries n).
Proof.
  destruct m as [t], n as [u]; change (GHC.Base.compare (Data.Foldable.toList t) (Data.Foldable.toList u) =
    GHC.Base.compare (entries (IM.MkIntervalMap t)) (entries (IM.MkIntervalMap u))).
  rewrite !toList_contents; apply entry_list_compare.
Qed.
End Equality.

(* Independent ordinary stable list merge. Equality chooses the left head. *)
Fixpoint mergeEntries {A} (xs ys : list (IM.Interval K * A)) {struct xs} : list (IM.Interval K * A) :=
  match xs with
  | [] => ys
  | x :: xs' =>
    (fix scan ys := match ys with
     | [] => xs
     | y :: ys' => if GHC.Base.op_zgze__ (fst y) (fst x)
       then x :: mergeEntries xs' ys else y :: scan ys'
     end) ys
  end.

Lemma mergeEntries_nil_r {A} (xs : list (IM.Interval K * A)) : mergeEntries xs [] = xs.
Proof. destruct xs; reflexivity. Qed.
Lemma mergeEntries_cons {A} (x y : IM.Interval K * A) xs ys :
  mergeEntries (x::xs) (y::ys) = if GHC.Base.op_zgze__ (fst y) (fst x)
    then x :: mergeEntries xs (y::ys) else y :: mergeEntries (x::xs) ys.
Proof. reflexivity. Qed.
Lemma mergeEntries_left_chunk {A} i (a : A) xs ns :
  let '(l,r) := breakNodes (fun j => GHC.Base.op_zgze__ j i) ns in
  mergeEntries ((i,a)::xs) (List.map fullEntry ns) =
    List.map fullEntry l ++ (i,a) :: mergeEntries xs (List.map fullEntry r).
Proof.
  induction ns as [|[j b] ns IH]; [cbn [breakNodes List.map]; rewrite !mergeEntries_nil_r; reflexivity|].
  cbn [breakNodes List.map fullEntry]; rewrite mergeEntries_cons; cbn [fst].
  destruct (GHC.Base.op_zgze__ j i); [reflexivity|].
  destruct (breakNodes (fun j => GHC.Base.op_zgze__ j i) ns) as [l r].
  cbn [List.map List.app]; now rewrite IH.
Qed.
Lemma interval_strict_complement (i j : IM.Interval K) :
  GHC.Base.op_zg__ i j = negb (GHC.Base.op_zgze__ j i).
Proof.
  change (GHC.Base.op_zl__ j i = negb (negb (GHC.Base.op_zl__ j i)));
    symmetry; apply negb_involutive.
Qed.
Lemma mergeEntries_right_chunk {A} i (a : A) ns ys :
  let '(l,r) := breakNodes (fun j => GHC.Base.op_zg__ j i) ns in
  mergeEntries (List.map fullEntry ns) ((i,a)::ys) =
    List.map fullEntry l ++ (i,a) :: mergeEntries (List.map fullEntry r) ys.
Proof.
  induction ns as [|[j b] ns IH]; [reflexivity|].
  cbn [breakNodes List.map fullEntry]; rewrite mergeEntries_cons; cbn [fst].
  rewrite (interval_strict_complement j i); destruct (GHC.Base.op_zgze__ i j); cbv beta iota zeta.
  - destruct (breakNodes (fun j => GHC.Base.op_zg__ j i) ns) as [l r].
    cbn [List.map List.app] in IH |- *.
    rewrite IH; reflexivity.
  - reflexivity.
Qed.

Lemma mergeEntries_Forall {A} (P : IM.Interval K * A -> Prop) xs ys :
  Forall P xs -> Forall P ys -> Forall P (mergeEntries xs ys).
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys SX; [auto|].
  inversion SX as [|? ? Px PX]; subst.
  induction ys as [|y ys IHY]; intro SY; [exact SX|].
  inversion SY as [|? ? Py PY]; subst.
  rewrite mergeEntries_cons; destruct (GHC.Base.op_zgze__ (fst y) (fst x));
    constructor; auto.
Qed.
Lemma mergeEntries_sorted {A} (xs ys : list (IM.Interval K * A)) :
  StronglySorted entryLE xs -> StronglySorted entryLE ys ->
  StronglySorted entryLE (mergeEntries xs ys).
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys SX; [auto|].
  inversion SX as [|? ? SSX AX]; subst.
  induction ys as [|y ys IHY]; intro SY; [exact SX|].
  inversion SY as [|? ? SSY AY]; subst.
  rewrite mergeEntries_cons; destruct (GHC.Base.op_zgze__ (fst y) (fst x)) eqn:C.
  - apply (proj1 (interval_ge_iff laws _ _)) in C.
    constructor; [apply IH; assumption|].
    apply mergeEntries_Forall; [exact AX|]. constructor; [exact C|].
    rewrite Forall_forall in *; intros z Hz; eapply intervalLE_trans; [exact laws|exact C|apply AY; exact Hz].
  - assert (YX : intervalLE (fst y) (fst x)).
    { destruct (intervalLE_total laws (fst x) (fst y)) as [E|E]; [|exact E].
      apply (proj2 (interval_ge_iff laws _ _)) in E; congruence. }
    constructor; [apply IHY; exact SSY|].
    apply mergeEntries_Forall; [|exact AY]. constructor; [exact YX|].
    rewrite Forall_forall in *; intros z Hz; eapply intervalLE_trans; [exact laws|exact YX|apply AX; exact Hz].
Qed.

Lemma strict_larger_upward i j k : intervalLE j k -> GHC.Base.op_zg__ j i = true ->
  GHC.Base.op_zg__ k i = true.
Proof.
  intros JK; rewrite !interval_strict_complement.
  intro C; apply negb_true_iff in C; apply negb_true_iff.
  destruct (GHC.Base.op_zgze__ i k) eqn:KI; [|reflexivity].
  apply (proj1 (interval_ge_iff laws _ _)) in KI.
  assert (JI : intervalLE j i) by (eapply intervalLE_trans; eauto).
  apply (proj2 (interval_ge_iff laws _ _)) in JI; congruence.
Qed.

Lemma interval_viewl_spec {A} (m : IM.IntervalMap K A) : valid m ->
  match Data.FingerTree.viewl (rawTree m) with
  | Data.FingerTree.EmptyL => entries m = []
  | Data.FingerTree.op_ZCzl__ (IM.MkNode i a) r =>
    entries m = (i,a)::entries (IM.MkIntervalMap r) /\ closed i /\ valid (IM.MkIntervalMap r)
  end.
Proof.
  intro V; pose proof (leastView_spec V) as S.
  pose proof (proj1 (proj2 (proj2 V))) as C.
  destruct m as [t]; unfold IM.leastView in S; cbn [rawTree].
  destruct (Data.FingerTree.viewl t) as [|[i a] r]; [exact S|].
  destruct S as [E R]; rewrite E in C; inversion C; auto.
Qed.

Lemma cache_cons {A} i (a : A) t : cacheValid (IM.MkIntervalMap t) ->
  cacheValid (IM.MkIntervalMap (Data.FingerTree.consTree (IM.MkNode i a) t)).
Proof. intro V; unfold cacheValid, rawTree; apply consTree_validityWith; try monoid_laws; auto. Qed.
Lemma cache_append {A} (t u : Data.FingerTree.FingerTree (IM.IntInterval K) (IM.Node K A)) :
  cacheValid (IM.MkIntervalMap t) -> cacheValid (IM.MkIntervalMap u) ->
  cacheValid (IM.MkIntervalMap (Data.FingerTree.op_zgzl__ t u)).
Proof. intros V W; unfold cacheValid, rawTree; apply append_validityWith; try monoid_laws; assumption. Qed.
Lemma entries_cons {A} i (a : A) t :
  entries (IM.MkIntervalMap (Data.FingerTree.consTree (IM.MkNode i a) t)) =
    (i,a)::entries (IM.MkIntervalMap t).
Proof. unfold entries, rawTree; rewrite consTree_contents; reflexivity. Qed.
Lemma entries_append {A} (t u : Data.FingerTree.FingerTree (IM.IntInterval K) (IM.Node K A)) :
  entries (IM.MkIntervalMap (Data.FingerTree.op_zgzl__ t u)) =
    entries (IM.MkIntervalMap t) ++ entries (IM.MkIntervalMap u).
Proof. unfold entries, rawTree; rewrite append_contents, List.map_app; reflexivity. Qed.

Lemma union_spec {A} (m n : IM.IntervalMap K A) : valid m -> valid n ->
  entries (IM.union m n) = mergeEntries (entries m) (entries n) /\ valid (IM.union m n).
Proof.
  intros VM VN; destruct m as [t], n as [u]; unfold IM.union.
  match goal with |- context [HsToRocq.Wf.wfFix2 ?R ?rank ?WF ?body] =>
    set (worker := HsToRocq.Wf.wfFix2 R rank WF body);
    assert (Worker : forall xs ys, valid (IM.MkIntervalMap xs) -> valid (IM.MkIntervalMap ys) ->
      entries (IM.MkIntervalMap (worker xs ys)) =
        mergeEntries (entries (IM.MkIntervalMap xs)) (entries (IM.MkIntervalMap ys)) /\
      cacheValid (IM.MkIntervalMap (worker xs ys)))
  end.
  - intros xs ys; remember (size xs + size ys) as rank eqn:Rank; revert xs ys Rank.
    induction rank as [rank IH] using lt_wf_ind; intros xs ys Rank VX VY.
    pose proof (interval_viewl_spec VX) as XView; cbn [rawTree] in XView.
    unfold worker at 1 2; rewrite !HsToRocq.Wf.wfFix2_eq; fold worker.
    cbn beta zeta; cbn [proj1_sig].
    destruct (Data.FingerTree.viewl xs) as [|[i a] xs'] eqn:EX.
    + rewrite XView; split; [reflexivity|exact (proj1 (proj2 VY))].
    + destruct XView as [XE [Ci VX']].
      match goal with |- context [Data.FingerTree.split ?p ys] =>
        assert (Safe1 : Data.FingerTree.split p ys =
          Data.FingerTree.split (summaryTest (fun j => GHC.Base.op_zgze__ j i) false) ys)
          by (apply split_summary_safe; [exact (proj1 (proj2 VY))|reflexivity])
      end; rewrite Safe1.
      destruct (Data.FingerTree.split (summaryTest (fun j => GHC.Base.op_zgze__ j i) false) ys)
        as [yl yr] eqn:EY.
      destruct (split_ordered_test _ false VY (@larger_upward i) EY) as [BY [Vyl Vyr]].
      destruct (split_ordered_filters _ false VY (@larger_upward i) EY) as [_ [_ [VYL VYR]]].
      cbn [rawTree] in BY.
      pose proof (@mergeEntries_left_chunk A i a (entries (IM.MkIntervalMap xs')) (contents ys)) as First.
      rewrite BY in First.
      change (mergeEntries ((i,a)::entries (IM.MkIntervalMap xs')) (entries (IM.MkIntervalMap ys)) =
        entries (IM.MkIntervalMap yl) ++ (i,a)::mergeEntries (entries (IM.MkIntervalMap xs'))
          (entries (IM.MkIntervalMap yr))) in First.
      pose proof (interval_viewl_spec VYR) as YView; cbn [rawTree] in YView.
      destruct (Data.FingerTree.viewl yr) as [|[j b] yr'] eqn:EYView.
      * rewrite YView, mergeEntries_nil_r in First.
        split.
        -- rewrite entries_append, entries_cons, XE, First; reflexivity.
        -- apply cache_append; [exact Vyl|apply cache_cons; exact (proj1 (proj2 VX'))].
      * destruct YView as [YE [Cj VYR']].
        match goal with |- context [Data.FingerTree.split ?p xs'] =>
          assert (Safe2 : Data.FingerTree.split p xs' =
            Data.FingerTree.split (summaryTest (fun k => GHC.Base.op_zg__ k j) false) xs')
            by (apply split_summary_safe; [exact (proj1 (proj2 VX'))|reflexivity])
        end; rewrite Safe2.
        destruct (Data.FingerTree.split (summaryTest (fun k => GHC.Base.op_zg__ k j) false) xs')
          as [xl xr] eqn:EXSplit.
        destruct (split_ordered_test _ false VX' (@strict_larger_upward j) EXSplit) as [BX [Vxl Vxr]].
        destruct (split_ordered_filters _ false VX' (@strict_larger_upward j) EXSplit) as [_ [_ [VXL VXR]]].
        cbn [rawTree] in BX.
        pose proof (@mergeEntries_right_chunk A j b (contents xs') (entries (IM.MkIntervalMap yr'))) as Second.
        rewrite BX in Second.
        change (mergeEntries (entries (IM.MkIntervalMap xs')) ((j,b)::entries (IM.MkIntervalMap yr')) =
          entries (IM.MkIntervalMap xl) ++ (j,b)::mergeEntries (entries (IM.MkIntervalMap xr))
            (entries (IM.MkIntervalMap yr'))) in Second.
        assert (Decrease : size xr + size yr' < rank).
        { pose proof (viewl_size_lt IM.Measured__IntInterval__Node xs (IM.MkNode i a) xs' EX) as Bx.
          pose proof (viewl_size_lt IM.Measured__IntInterval__Node yr (IM.MkNode j b) yr' EYView) as By.
          pose proof (split_size_bounds intervalUnion_right_id IM.Measured__IntInterval__Node _ ys yl yr EY) as BoundsY.
          pose proof (split_size_bounds intervalUnion_right_id IM.Measured__IntInterval__Node _ xs' xl xr EXSplit) as BoundsX.
          lia. }
        destruct (IH _ Decrease xr yr' eq_refl VXR VYR') as [Rec CR].
        fold worker.
        split.
        -- repeat first [rewrite entries_append|rewrite entries_cons].
           rewrite Rec, XE, First.
           rewrite YE, Second; reflexivity.
        -- apply cache_append; [exact Vyl|apply cache_cons].
           apply cache_append; [exact Vxl|apply cache_cons; exact CR].
  - destruct (Worker t u VM VN) as [E C]; split; [exact E|].
    split; [exact laws|]; split; [exact C|]; rewrite E; split.
    + apply mergeEntries_Forall; [exact (proj1 (proj2 (proj2 VM)))|exact (proj1 (proj2 (proj2 VN)))].
    + apply mergeEntries_sorted; [exact (proj2 (proj2 (proj2 VM)))|exact (proj2 (proj2 (proj2 VN)))].
Qed.

(* A raw shape relation is used only to transport application sortedness through
   payload effects. CoreTraversal supplies the independent effect semantics. *)
Definition digitRel {A B} (R : A -> B -> Prop) (x : Data.FingerTree.Digit A) (y : Data.FingerTree.Digit B) : Prop :=
  match x,y with
  | Data.FingerTree.One a, Data.FingerTree.One b => R a b
  | Data.FingerTree.Two a c, Data.FingerTree.Two b d => R a b /\ R c d
  | Data.FingerTree.Three a c e, Data.FingerTree.Three b d f => R a b /\ R c d /\ R e f
  | Data.FingerTree.Four a c e g, Data.FingerTree.Four b d f h => R a b /\ R c d /\ R e f /\ R g h
  | _,_ => False
  end.
Definition nodeRel {A B} (R : A -> B -> Prop)
  (x : Data.FingerTree.Node (IM.IntInterval K) A) (y : Data.FingerTree.Node (IM.IntInterval K) B) : Prop :=
  match x,y with
  | Data.FingerTree.Node2 c a d, Data.FingerTree.Node2 c' b e => c=c' /\ R a b /\ R d e
  | Data.FingerTree.Node3 c a d f, Data.FingerTree.Node3 c' b e g => c=c' /\ R a b /\ R d e /\ R f g
  | _,_ => False
  end.
Fixpoint treeRel {A} (x : Data.FingerTree.FingerTree (IM.IntInterval K) A) {B}
  (R : A -> B -> Prop) (y : Data.FingerTree.FingerTree (IM.IntInterval K) B) : Prop :=
  match x,y with
  | Data.FingerTree.Empty,Data.FingerTree.Empty => True
  | Data.FingerTree.Single a,Data.FingerTree.Single b => R a b
  | Data.FingerTree.Deep c pr m sf,Data.FingerTree.Deep c' pr' m' sf' =>
      c=c' /\ digitRel R pr pr' /\ treeRel m (nodeRel R) m' /\ digitRel R sf sf'
  | _,_ => False
  end.

Lemma digitRel_contents {A B X} (R : A -> B -> Prop) (f : A -> list X) (g : B -> list X) d e :
  (forall a b, R a b -> f a = g b) -> digitRel R d e -> digitContentsWith f d = digitContentsWith g e.
Proof.
  intros E Rel; destruct d,e; cbn [digitRel digitContentsWith] in *; try contradiction;
    decompose [and] Rel; repeat match goal with H : R ?a ?b |- _ => rewrite (E a b H); clear H end; reflexivity.
Qed.
Lemma nodeRel_contents {A B X} (R : A -> B -> Prop) (f : A -> list X) (g : B -> list X) d e :
  (forall a b, R a b -> f a = g b) -> nodeRel R d e -> nodeContentsWith f d = nodeContentsWith g e.
Proof.
  intros E Rel; destruct d,e; cbn [nodeRel nodeContentsWith] in *; try contradiction;
    decompose [and] Rel; repeat match goal with H : R ?a ?b |- _ => rewrite (E a b H); clear H end; reflexivity.
Qed.
Lemma treeRel_contents : forall A (t : Data.FingerTree.FingerTree (IM.IntInterval K) A) B
  (u : Data.FingerTree.FingerTree (IM.IntInterval K) B) (R : A -> B -> Prop) X
  (f : A -> list X) (g : B -> list X),
  (forall a b, R a b -> f a = g b) -> treeRel t R u -> contentsWith f t = contentsWith g u.
Proof.
  refine (Data.FingerTree.FingerTree_rect (IM.IntInterval K) (fun A t => forall B u R X f g,
    (forall a b, R a b -> f a = g b) -> treeRel t R u -> contentsWith f t = contentsWith g u) _ _ _).
  - intros; destruct u; cbn in *; tauto.
  - intros; destruct u; cbn in *; try contradiction; auto.
  - intros A c pr mid IH sf B u R X f g E Rel; destruct u as [|b|c' pr' mid' sf'];
      cbn [treeRel] in Rel; try contradiction.
    destruct Rel as [CC [Pr [Mid Sf]]]; cbn [contentsWith].
    rewrite (@digitRel_contents A B X R f g pr pr' E Pr), (@digitRel_contents A B X R f g sf sf' E Sf).
    f_equal; f_equal; eapply IH; [|exact Mid]. intros; eapply nodeRel_contents; eauto.
Qed.

Lemma digitRel_measure {A B} (R : A -> B -> Prop) (mu : A -> IM.IntInterval K) (nu : B -> IM.IntInterval K) d e :
  (forall a b, R a b -> mu a = nu b) -> digitRel R d e -> digitMeasure mu d = digitMeasure nu e.
Proof.
  intros E Rel; destruct d,e; cbn [digitRel digitMeasure] in *; try contradiction;
    decompose [and] Rel; repeat match goal with H : R ?a ?b |- _ => rewrite (E a b H); clear H end; reflexivity.
Qed.
Lemma treeRel_cache : forall A (t : Data.FingerTree.FingerTree (IM.IntInterval K) A) B u
  (R : A -> B -> Prop) mu nu,
  (forall a b, R a b -> mu a = nu b) -> treeRel t R u ->
  treeCacheWith mu t = treeCacheWith nu u.
Proof.
  intros A t B u R mu nu E Rel; destruct t,u; cbn [treeRel treeCacheWith] in *;
    try contradiction; intuition.
Qed.
Lemma treeRel_validity : forall A (t : Data.FingerTree.FingerTree (IM.IntInterval K) A) B u
  (R : A -> B -> Prop) mu nu P Q,
  (forall a b, R a b -> mu a = nu b /\ (P a -> Q b)) ->
  treeRel t R u -> validityWith mu P t -> validityWith nu Q u.
Proof.
  refine (Data.FingerTree.FingerTree_rect (IM.IntInterval K) (fun A t => forall B u R mu nu P Q,
    (forall a b, R a b -> mu a = nu b /\ (P a -> Q b)) ->
    treeRel t R u -> validityWith mu P t -> validityWith nu Q u) _ _ _).
  - intros; destruct u; cbn in *; tauto.
  - intros A a B u R mu nu P Q E Rel V; destruct u; cbn in *; try contradiction; eapply E; eauto.
  - intros A c pr mid IH sf B u R mu nu P Q E Rel V; destruct u as [|b|c' pr' mid' sf'];
      cbn [treeRel] in Rel; try contradiction.
    destruct Rel as [CC [Pr [Mid Sf]]]; subst c'.
    destruct V as [Vp [Vm [Vs Ec]]].
    assert (D : forall d e, digitRel R d e -> digitValidity P d -> digitValidity Q e).
    { intros d e RR VV; destruct d,e; cbn [digitRel digitValidity] in *; try contradiction;
        decompose [and] RR; decompose [and] VV; repeat split; eapply E; eassumption. }
    cbn [validityWith]; split; [eapply D; eauto|]; split.
    + eapply IH; [|exact Mid|exact Vm].
      intros n n' RN; destruct n,n'; cbn [nodeRel nodeCache nodeValidity] in *; try contradiction.
      all: decompose [and] RN; subst; split; [reflexivity|].
      all: repeat match goal with HR : ?RR ?a ?b,
        EE : forall a b, ?RR a b -> _ /\ _ |- _ =>
        let EQ := fresh in pose proof (EE a b HR) as EQ; clear HR; destruct EQ end.
      all: intro VV; decompose [and] VV; repeat split; auto; congruence.
    + split; [eapply D; eauto|]. rewrite Ec.
      rewrite (@digitRel_measure A B R mu nu pr pr' ltac:(intros; eapply E; eauto) Pr),
        (@digitRel_measure A B R mu nu sf sf' ltac:(intros; eapply E; eauto) Sf).
      rewrite (@treeRel_cache _ mid _ mid' (nodeRel R) nodeCache nodeCache
        ltac:(intros n n' RR; destruct n,n'; cbn [nodeRel nodeCache] in *; tauto) Mid).
      reflexivity.
Qed.

Section Traversal.
Context {F : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F}.

Local Ltac interval_effect R g Hg :=
  lazymatch goal with
  | |- HoldsF ?Q (GHC.Base.op_zlztzg__ ?ff (g ?x)) =>
    apply (HoldsF_app (R x) Q ff (g x)); [interval_effect R g Hg|apply Hg]
  | |- HoldsF ?Q (GHC.Base.fmap ?h (g ?x)) =>
    apply (HoldsF_fmap (R x) Q h); [intros; cbn [digitRel nodeRel]; auto|apply Hg]
  end.

Lemma traverseDigit_rel {A B} (R : A -> B -> Prop) (g : A -> F B) d :
  (forall a, HoldsF (R a) (g a)) ->
  HoldsF (digitRel R d) (Data.FingerTree.traverseDigit g d).
Proof.
  intro Hg; destruct d; cbn [Data.FingerTree.traverseDigit]; unfold Data.Functor.op_zlzdzg__;
    interval_effect R g Hg.
Qed.
Lemma unsafeTraverseNode_rel {A B} (R : A -> B -> Prop) (g : A -> F B) n :
  (forall a, HoldsF (R a) (g a)) ->
  HoldsF (nodeRel R n) (Data.FingerTree.unsafeTraverseNode g n).
Proof.
  intro Hg; destruct n; cbn [Data.FingerTree.unsafeTraverseNode]; unfold Data.Functor.op_zlzdzg__;
    interval_effect R g Hg.
Qed.
Lemma unsafeTraverse_rel : forall A (t : Data.FingerTree.FingerTree (IM.IntInterval K) A) B
  (R : A -> B -> Prop) (g : A -> F B),
  (forall a, HoldsF (R a) (g a)) -> HoldsF (treeRel t R) (Data.FingerTree.unsafeTraverse g t).
Proof.
  refine (Data.FingerTree.FingerTree_rect (IM.IntInterval K) (fun A t => forall B R g,
    (forall a, HoldsF (R a) (g a)) -> HoldsF (treeRel t R) (Data.FingerTree.unsafeTraverse g t)) _ _ _).
  - intros; apply HoldsF_pure; exact I.
  - intros A a B R g Hg; cbn [Data.FingerTree.unsafeTraverse]; unfold Data.Functor.op_zlzdzg__.
    apply (HoldsF_fmap (R a) (treeRel (Data.FingerTree.Single a) R) Data.FingerTree.Single);
      [intros; assumption|apply Hg].
  - intros A c pr mid IH sf B R g Hg.
    cbn [Data.FingerTree.unsafeTraverse]; unfold Data.Functor.op_zlzdzg__.
    eapply HoldsF_app3 with (P := digitRel R pr) (Q := treeRel mid (nodeRel R)) (R := digitRel R sf).
    + intros p m s Hp Hm Hs; cbn [treeRel]; auto.
    + apply traverseDigit_rel; exact Hg.
    + apply IH; intro n; apply unsafeTraverseNode_rel; exact Hg.
    + apply traverseDigit_rel; exact Hg.
Qed.

Definition payloadRel {A B} (x : IM.Node K A) (y : IM.Node K B) : Prop :=
  fst (fullEntry x) = fst (fullEntry y).

Lemma payloadRel_valid {A B} (m : IM.IntervalMap K A) (t : Data.FingerTree.FingerTree (IM.IntInterval K) (IM.Node K B)) :
  valid m -> treeRel (rawTree m) payloadRel t -> valid (IM.MkIntervalMap t).
Proof.
  intros [L [V [C S]]] Rel.
  assert (Labels : List.map fst (entries m) = List.map fst (entries (IM.MkIntervalMap t))).
  { unfold entries; rewrite !List.map_map.
    rewrite <- !contentsWith_singletons.
    eapply treeRel_contents; [|exact Rel]. intros x y R; cbn; now rewrite R. }
  split; [exact L|]; split.
  - eapply treeRel_validity; [|exact Rel|exact V].
    intros [i a] [j b] R; change (i = j) in R.
    subst j; split; reflexivity.
  - split.
    + rewrite <- Forall_map with (f := @fst (IM.Interval K) B).
      rewrite <- Labels, Forall_map; exact C.
    + (* Sortedness is a relation on intervals only, never on payloads. *)
      assert (Transport : forall xs ys, List.map (@fst (IM.Interval K) A) xs =
          List.map (@fst (IM.Interval K) B) ys -> StronglySorted entryLE xs -> StronglySorted entryLE ys).
      { intros xs; induction xs as [|[i a] xs IH]; intros [|[j b] ys] E Sorted;
          cbn in E; try discriminate; [constructor|].
        injection E as IJ Rest; subst j; inversion Sorted as [|? ? SS All]; subst.
        constructor; [apply IH; assumption|].
        rewrite Forall_forall in *; intros [j b'] Hin.
        assert (Jin : In j (List.map fst xs)).
        { rewrite Rest; apply in_map with (f := @fst (IM.Interval K) B) in Hin; exact Hin. }
        apply in_map_iff in Jin; destruct Jin as [[j' a'] [Eq Hin']]; cbn in Eq; subst j'.
        exact (All (j,a') Hin'). }
      apply (Transport _ _ Labels S).
Qed.

Lemma traverse_valid {A B} (f : A -> F B) (m : IM.IntervalMap K A) :
  valid m -> HoldsF (@valid K H H0 B) (Data.Traversable.traverse f m).
Proof.
  intro V; destruct m as [t].
  change (HoldsF (@valid K H H0 B)
    (GHC.Base.fmap IM.MkIntervalMap (Data.FingerTree.unsafeTraverse (Data.Traversable.traverse f) t))).
  eapply HoldsF_fmap; [intros out Rel; eapply payloadRel_valid; [exact V|exact Rel]|].
  apply unsafeTraverse_rel; intros [i a].
  change (HoldsF (payloadRel (IM.MkNode i a)) (GHC.Base.fmap (IM.MkNode i) (f a))).
  apply (HoldsF_fmap (fun _ => True)); [intros; reflexivity|].
  exists (GHC.Base.fmap (fun b => exist (fun _ => True) b I) (f a)).
  rewrite Proofs.GHC.Base.functor_composition.
  change (GHC.Base.fmap (fun x => x) (f a) = f a); apply Proofs.GHC.Base.functor_identity.
Qed.

Lemma traverse_entries {A B} (f : A -> F B) (m : IM.IntervalMap K A) :
  GHC.Base.fmap entries (Data.Traversable.traverse f m) =
    ApplicativeValidity.traverse_list
      (fun e => GHC.Base.fmap (fun b => (fst e,b)) (f (snd e))) (entries m).
Proof.
  rewrite <- traverse_concat_list; destruct m as [t].
  change (GHC.Base.fmap entries (GHC.Base.fmap IM.MkIntervalMap
    (Data.FingerTree.unsafeTraverse (Data.Traversable.traverse f) t)) =
      traverse_concat (fun e => GHC.Base.fmap (fun x => [x])
        (GHC.Base.fmap (fun b => (fst e,b)) (f (snd e)))) (entries (IM.MkIntervalMap t))).
  rewrite Proofs.GHC.Base.functor_composition.
  assert (Er : (fun u : Data.FingerTree.FingerTree (IM.IntInterval K) (IM.Node K B) =>
    entries (IM.MkIntervalMap u)) = contentsWith (fun n => [fullEntry n])).
  { apply FunctionalExtensionality.functional_extensionality; intro u.
    unfold entries, rawTree; symmetry; apply contentsWith_singletons. }
  change (GHC.Base.fmap (fun u => entries (IM.MkIntervalMap u))
    (Data.FingerTree.unsafeTraverse (Data.Traversable.traverse f) t) =
      traverse_concat (fun e => GHC.Base.fmap (fun x => [x])
        (GHC.Base.fmap (fun b => (fst e,b)) (f (snd e)))) (entries (IM.MkIntervalMap t))).
  rewrite Er; unfold entries, rawTree; rewrite <- contentsWith_singletons.
  apply unsafeTraverse_contentsWith; intros [i a].
  rewrite traverse_concat_singleton.
  change (GHC.Base.fmap (fun n => [fullEntry n]) (GHC.Base.fmap (IM.MkNode i) (f a)) =
    GHC.Base.fmap (fun x => [x]) (GHC.Base.fmap (fun b => (i,b)) (f a))).
  rewrite !Proofs.GHC.Base.functor_composition; reflexivity.
Qed.

Lemma sequenceA_valid {A} (m : IM.IntervalMap K (F A)) :
  valid m -> HoldsF (@valid K H H0 A)
    (@Data.Traversable.sequenceA (IM.IntervalMap K) IM.Functor__IntervalMap IM.Foldable__IntervalMap
      IM.Traversable__IntervalMap F A Functor0 Applicative0 m).
Proof. apply traverse_valid. Qed.
Lemma sequenceA_entries {A} (m : IM.IntervalMap K (F A)) :
  GHC.Base.fmap entries (@Data.Traversable.sequenceA (IM.IntervalMap K) IM.Functor__IntervalMap
    IM.Foldable__IntervalMap IM.Traversable__IntervalMap F A Functor0 Applicative0 m) =
    ApplicativeValidity.traverse_list (fun e => GHC.Base.fmap (fun a => (fst e,a)) (snd e)) (entries m).
Proof. exact (@traverse_entries (F A) A (fun x => x) m). Qed.

Context {MonadF : GHC.Base.Monad F}.
Lemma mapM_valid {A B} (f : A -> F B) (m : IM.IntervalMap K A) :
  valid m -> HoldsF (@valid K H H0 B) (Data.Traversable.mapM f m).
Proof. apply traverse_valid. Qed.
Lemma mapM_entries {A B} (f : A -> F B) (m : IM.IntervalMap K A) :
  GHC.Base.fmap entries (Data.Traversable.mapM f m) =
    ApplicativeValidity.traverse_list
      (fun e => GHC.Base.fmap (fun b => (fst e,b)) (f (snd e))) (entries m).
Proof. apply traverse_entries. Qed.
Lemma sequence_valid {A} (m : IM.IntervalMap K (F A)) :
  valid m -> HoldsF (@valid K H H0 A)
    (@Data.Traversable.sequence (IM.IntervalMap K) IM.Functor__IntervalMap IM.Foldable__IntervalMap
      IM.Traversable__IntervalMap F A Functor0 Applicative0 MonadF m).
Proof. apply sequenceA_valid. Qed.
Lemma sequence_entries {A} (m : IM.IntervalMap K (F A)) :
  GHC.Base.fmap entries (@Data.Traversable.sequence (IM.IntervalMap K) IM.Functor__IntervalMap
    IM.Foldable__IntervalMap IM.Traversable__IntervalMap F A Functor0 Applicative0 MonadF m) =
    ApplicativeValidity.traverse_list (fun e => GHC.Base.fmap (fun a => (fst e,a)) (snd e)) (entries m).
Proof. apply sequenceA_entries. Qed.

End Traversal.
Lemma foldl_payloads {A B} (f : B -> A -> B) z (m : IM.IntervalMap K A) :
  Data.Foldable.foldl f z m = List.fold_left (fun z e => f z (snd e)) (entries m) z.
Proof.
  change (Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
    (Data.Foldable.foldMap (fun x => Data.SemigroupInternal.Mk_Dual
      (Data.SemigroupInternal.Mk_Endo (fun z => f z x))) m)) z =
    List.fold_left (fun z e => f z (snd e)) (entries m) z).
  rewrite (@foldMap_payloads (Data.SemigroupInternal.Dual (Data.SemigroupInternal.Endo B)) _ _
    ltac:(intros [[x]] [[y]] [[w]]; reflexivity) ltac:(intros [[x]]; reflexivity) ltac:(intros [[x]]; reflexivity)).
  revert z; induction (entries m) as [|[i a] xs IH]; intro z; [reflexivity|].
  cbn [List.fold_right List.fold_left snd].
  destruct (List.fold_right _ _ xs) as [[k]] eqn:E; exact (IH (f z a)).
Qed.
Lemma foldl'_payloads {A B} (f : B -> A -> B) z (m : IM.IntervalMap K A) :
  Data.Foldable.foldl' f z m = List.fold_left (fun z e => f z (snd e)) (entries m) z.
Proof.
  change (Data.Foldable.foldr (fun x k z => k (f z x)) (fun z => z) m z =
    List.fold_left (fun z e => f z (snd e)) (entries m) z).
  rewrite foldr_payloads; revert z; induction (entries m); cbn; intros; [reflexivity|apply IHl].
Qed.
Lemma foldr'_payloads {A B} (f : A -> B -> B) z (m : IM.IntervalMap K A) :
  Data.Foldable.foldr' f z m = List.fold_right (fun e => f (snd e)) z (entries m).
Proof.
  change (Data.Foldable.foldl (fun k x z => k (f x z)) (fun z => z) m z =
    List.fold_right (fun e => f (snd e)) z (entries m)).
  rewrite foldl_payloads.
  assert (G : forall (xs : list (IM.Interval K * A)) (k : B -> B) z,
    List.fold_left (fun k e z => k (f (snd e) z)) xs k z =
      k (List.fold_right (fun e => f (snd e)) z xs)).
  { induction xs; cbn; intros; [reflexivity|rewrite IHxs; reflexivity]. }
  apply G.
Qed.
Lemma foldMap'_payloads {A M} {S : GHC.Base.Semigroup M} {D : GHC.Base.Monoid M}
  (f : A -> M) (m : IM.IntervalMap K A) :
  Data.Foldable.foldMap' f m = List.fold_left
    (fun acc e => GHC.Base.op_zlzlzgzg__ acc (f (snd e))) (entries m) GHC.Base.mempty.
Proof.
  change (Data.Foldable.foldl' (fun acc a => GHC.Base.op_zlzlzgzg__ acc (f a)) GHC.Base.mempty m =
    List.fold_left (fun acc e => GHC.Base.op_zlzlzgzg__ acc (f (snd e))) (entries m) GHC.Base.mempty).
  exact (@foldl'_payloads A M (fun acc a => GHC.Base.op_zlzlzgzg__ acc (f a)) GHC.Base.mempty m).
Qed.
Lemma null_payloads {A} (m : IM.IntervalMap K A) :
  Data.Foldable.null m = match entries m with [] => true | _ => false end.
Proof.
  destruct m as [[|n|c pr mid sf]]; try reflexivity.
  destruct pr; reflexivity.
Qed.
Lemma length_payloads {A} (m : IM.IntervalMap K A) :
  Data.Foldable.length m = Z.of_nat (Datatypes.length (entries m)).
Proof.
  change (Data.Foldable.foldl' (fun (z : Z) (_ : A) => (z+1)%Z) 0%Z m =
    Z.of_nat (Datatypes.length (entries m))).
  rewrite foldl'_payloads.
  assert (C : forall xs (z : Z), List.fold_left (fun z (_ : IM.Interval K * A) => (z+1)%Z) xs z =
    (z + Z.of_nat (Datatypes.length xs))%Z).
  { induction xs; cbn; intros; [lia|rewrite IHxs; lia]. }
  rewrite C; lia.
Qed.

(* Methods of the application node, including inherited fold defaults. *)
Lemma node_fmap {A B} (f : A -> B) (i : IM.Interval K) a : GHC.Base.fmap f (IM.MkNode i a) = IM.MkNode i (f a).
Proof. reflexivity. Qed.
Lemma node_replace {A B} (a : A) (i : IM.Interval K) (b : B) : GHC.Base.op_zlzd__ a (IM.MkNode i b) = IM.MkNode i a.
Proof. reflexivity. Qed.
Lemma node_foldMap {A M} {S : GHC.Base.Semigroup M} {D : GHC.Base.Monoid M}
  (f : A -> M) (i : IM.Interval K) a : Data.Foldable.foldMap f (IM.MkNode i a) = f a.
Proof. reflexivity. Qed.
Lemma node_foldr {A B} (f : A -> B -> B) z (i : IM.Interval K) a : Data.Foldable.foldr f z (IM.MkNode i a) = f a z.
Proof. reflexivity. Qed.
Lemma node_foldl {A B} (f : B -> A -> B) z (i : IM.Interval K) a : Data.Foldable.foldl f z (IM.MkNode i a) = f z a.
Proof. reflexivity. Qed.
Lemma node_foldl' {A B} (f : B -> A -> B) z (i : IM.Interval K) a : Data.Foldable.foldl' f z (IM.MkNode i a) = f z a.
Proof. reflexivity. Qed.
Lemma node_foldr' {A B} (f : A -> B -> B) z (i : IM.Interval K) a : Data.Foldable.foldr' f z (IM.MkNode i a) = f a z.
Proof. reflexivity. Qed.
Lemma node_toList {A} (i : IM.Interval K) (a : A) : Data.Foldable.toList (IM.MkNode i a) = [a].
Proof. reflexivity. Qed.
Lemma node_null {A} (i : IM.Interval K) (a : A) : Data.Foldable.null (IM.MkNode i a) = false.
Proof. reflexivity. Qed.
Lemma node_length {A} (i : IM.Interval K) (a : A) : Data.Foldable.length (IM.MkNode i a) = 1%Z.
Proof. reflexivity. Qed.

Lemma mergeEntries_associative {A} (xs ys zs : list (IM.Interval K * A)) :
  mergeEntries (mergeEntries xs ys) zs = mergeEntries xs (mergeEntries ys zs).
Proof.
  remember (Datatypes.length xs + Datatypes.length ys + Datatypes.length zs) as rank eqn:Rank.
  revert xs ys zs Rank; induction rank as [rank IH] using lt_wf_ind.
  intros [|x xs] [|y ys] [|z zs] Rank;
    try (cbn [mergeEntries]; reflexivity);
    try (rewrite !mergeEntries_nil_r; reflexivity).
  destruct (GHC.Base.op_zgze__ (fst y) (fst x)) eqn:XY;
    destruct (GHC.Base.op_zgze__ (fst z) (fst y)) eqn:YZ;
    destruct (GHC.Base.op_zgze__ (fst z) (fst x)) eqn:XZ.
  all: try match goal with
  | XY : GHC.Base.op_zgze__ _ _ = true,
    YZ : GHC.Base.op_zgze__ _ _ = true,
    XZ : GHC.Base.op_zgze__ _ _ = false |- _ =>
      exfalso; apply (proj1 (interval_ge_iff laws _ _)) in XY;
      apply (proj1 (interval_ge_iff laws _ _)) in YZ;
      assert (R : intervalLE (fst x) (fst z)) by (eapply intervalLE_trans; eauto);
      apply (proj2 (interval_ge_iff laws _ _)) in R; congruence
  end.
  all: try match goal with
  | XY : GHC.Base.op_zgze__ _ _ = false,
    YZ : GHC.Base.op_zgze__ _ _ = false,
    XZ : GHC.Base.op_zgze__ _ _ = true |- _ =>
      exfalso; apply (proj1 (interval_ge_iff laws _ _)) in XZ;
      destruct (intervalLE_total laws (fst y) (fst z)) as [R|R];
        [apply (proj2 (interval_ge_iff laws _ _)) in R; congruence|
         assert (R' : intervalLE (fst x) (fst y)) by (eapply intervalLE_trans; eauto);
         apply (proj2 (interval_ge_iff laws _ _)) in R'; congruence]
  end.
  all: repeat (progress (cbn -[GHC.Base.op_zgze__]; rewrite ?XY, ?YZ, ?XZ)).
  all: f_equal.
  all: first [
    pose proof (IH (Datatypes.length xs + Datatypes.length (y::ys) + Datatypes.length (z::zs)) ltac:(cbn in Rank |- *; lia) xs (y::ys) (z::zs) eq_refl) as Rec;
      repeat (progress (cbn -[GHC.Base.op_zgze__] in Rec; rewrite ?XY, ?YZ, ?XZ in Rec)); exact Rec
  | pose proof (IH (Datatypes.length (x::xs) + Datatypes.length ys + Datatypes.length (z::zs)) ltac:(cbn in Rank |- *; lia) (x::xs) ys (z::zs) eq_refl) as Rec;
      repeat (progress (cbn -[GHC.Base.op_zgze__] in Rec; rewrite ?XY, ?YZ, ?XZ in Rec)); exact Rec
  | pose proof (IH (Datatypes.length (x::xs) + Datatypes.length (y::ys) + Datatypes.length zs) ltac:(cbn in Rank |- *; lia) (x::xs) (y::ys) zs eq_refl) as Rec;
      repeat (progress (cbn -[GHC.Base.op_zgze__] in Rec; rewrite ?XY, ?YZ, ?XZ in Rec)); exact Rec ].
Qed.

Lemma semigroup_union {A} (m n : IM.IntervalMap K A) : GHC.Base.op_zlzlzgzg__ m n = IM.union m n.
Proof. reflexivity. Qed.
Lemma monoid_union {A} (m n : IM.IntervalMap K A) : GHC.Base.mappend m n = IM.union m n.
Proof. reflexivity. Qed.
Lemma monoid_empty {A} : (GHC.Base.mempty : IM.IntervalMap K A) = IM.empty.
Proof. reflexivity. Qed.
Lemma monoid_concat {A} (ms : list (IM.IntervalMap K A)) :
  GHC.Base.mconcat ms = List.fold_right IM.union IM.empty ms.
Proof. reflexivity. Qed.
Lemma union_left_identity {A} (m : IM.IntervalMap K A) : valid m -> entries (IM.union IM.empty m) = entries m.
Proof. intro V; rewrite (proj1 (union_spec (proj2 (@empty_spec A)) V)); reflexivity. Qed.
Lemma union_right_identity {A} (m : IM.IntervalMap K A) : valid m -> entries (IM.union m IM.empty) = entries m.
Proof. intro V; rewrite (proj1 (union_spec V (proj2 (@empty_spec A)))); apply mergeEntries_nil_r. Qed.
Lemma union_associative {A} (m n p : IM.IntervalMap K A) : valid m -> valid n -> valid p ->
  entries (IM.union (IM.union m n) p) = entries (IM.union m (IM.union n p)).
Proof.
  intros V W U; destruct (union_spec V W) as [MN VMN], (union_spec W U) as [NP VNP].
  rewrite (proj1 (union_spec VMN U)), (proj1 (union_spec V VNP)), MN, NP.
  apply mergeEntries_associative.
Qed.

Lemma sum_payloads {A} {N : GHC.Num.Num A} (m : IM.IntervalMap K A) :
  Data.Foldable.sum m = List.fold_left (fun z e => GHC.Num.op_zp__ z (snd e))
    (entries m) (GHC.Num.fromInteger 0%Z).
Proof.
  change (Data.SemigroupInternal.getSum (Data.Foldable.foldMap' Data.SemigroupInternal.Mk_Sum m) =
    List.fold_left (fun z e => GHC.Num.op_zp__ z (snd e)) (entries m) (GHC.Num.fromInteger 0%Z)).
  rewrite foldMap'_payloads.
  assert (G : forall xs (z : A), Data.SemigroupInternal.getSum
    (List.fold_left (fun acc (e : IM.Interval K * A) =>
      GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Sum (snd e))) xs
        (Data.SemigroupInternal.Mk_Sum z)) =
    List.fold_left (fun z e => GHC.Num.op_zp__ z (snd e)) xs z).
  { induction xs; cbn; intros; [reflexivity|apply IHxs]. }
  apply G.
Qed.
Lemma product_payloads {A} {N : GHC.Num.Num A} (m : IM.IntervalMap K A) :
  Data.Foldable.product m = List.fold_left (fun z e => GHC.Num.op_zt__ z (snd e))
    (entries m) (GHC.Num.fromInteger 1%Z).
Proof.
  change (Data.SemigroupInternal.getProduct (Data.Foldable.foldMap' Data.SemigroupInternal.Mk_Product m) =
    List.fold_left (fun z e => GHC.Num.op_zt__ z (snd e)) (entries m) (GHC.Num.fromInteger 1%Z)).
  rewrite foldMap'_payloads.
  assert (G : forall xs (z : A), Data.SemigroupInternal.getProduct
    (List.fold_left (fun acc (e : IM.Interval K * A) =>
      GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Product (snd e))) xs
        (Data.SemigroupInternal.Mk_Product z)) =
    List.fold_left (fun z e => GHC.Num.op_zt__ z (snd e)) xs z).
  { induction xs; cbn; intros; [reflexivity|apply IHxs]. }
  apply G.
Qed.

Lemma fold_payloads {M} {S : GHC.Base.Semigroup M} {D : GHC.Base.Monoid M}
  (assoc : forall x y z : M, GHC.Base.mappend (GHC.Base.mappend x y) z = GHC.Base.mappend x (GHC.Base.mappend y z))
  (left : forall x : M, GHC.Base.mappend GHC.Base.mempty x = x)
  (right : forall x : M, GHC.Base.mappend x GHC.Base.mempty = x) (m : IM.IntervalMap K M) :
  Data.Foldable.fold m = List.fold_right (fun e acc => GHC.Base.mappend (snd e) acc) GHC.Base.mempty (entries m).
Proof. exact (foldMap_payloads assoc left right (fun x => x) m). Qed.

Lemma node_fold {M} {S : GHC.Base.Semigroup M} {D : GHC.Base.Monoid M} (i : IM.Interval K) (a : M) :
  Data.Foldable.fold (IM.MkNode i a) = a.
Proof. reflexivity. Qed.
Lemma node_foldMap' {A M} {S : GHC.Base.Semigroup M} {D : GHC.Base.Monoid M}
  (f : A -> M) (i : IM.Interval K) a : Data.Foldable.foldMap' f (IM.MkNode i a) =
    GHC.Base.op_zlzlzgzg__ GHC.Base.mempty (f a).
Proof. reflexivity. Qed.
Lemma node_sum {A} {N : GHC.Num.Num A} (i : IM.Interval K) a :
  Data.Foldable.sum (IM.MkNode i a) = GHC.Num.op_zp__ (GHC.Num.fromInteger 0%Z) a.
Proof. reflexivity. Qed.
Lemma node_product {A} {N : GHC.Num.Num A} (i : IM.Interval K) a :
  Data.Foldable.product (IM.MkNode i a) = GHC.Num.op_zt__ (GHC.Num.fromInteger 1%Z) a.
Proof. reflexivity. Qed.

Section NodeTraversalMethods.
Context {F : Type -> Type} {FunctorF : GHC.Base.Functor F} {ApplicativeF : GHC.Base.Applicative F}.
Lemma node_traverse {A B} (f : A -> F B) (i : IM.Interval K) a :
  Data.Traversable.traverse f (IM.MkNode i a) = GHC.Base.fmap (IM.MkNode i) (f a).
Proof. reflexivity. Qed.
Lemma node_sequenceA {A} (i : IM.Interval K) (fa : F A) :
  (@Data.Traversable.sequenceA (IM.Node K) IM.Functor__Node IM.Foldable__Node IM.Traversable__Node
    F A FunctorF ApplicativeF (IM.MkNode i fa)) = GHC.Base.fmap (IM.MkNode i) fa.
Proof. reflexivity. Qed.
Context {MonadF : GHC.Base.Monad F}.
Lemma node_mapM {A B} (f : A -> F B) (i : IM.Interval K) a :
  Data.Traversable.mapM f (IM.MkNode i a) = GHC.Base.fmap (IM.MkNode i) (f a).
Proof. reflexivity. Qed.
Lemma node_sequence {A} (i : IM.Interval K) (fa : F A) :
  (@Data.Traversable.sequence (IM.Node K) IM.Functor__Node IM.Foldable__Node IM.Traversable__Node
    F A FunctorF ApplicativeF MonadF (IM.MkNode i fa)) = GHC.Base.fmap (IM.MkNode i) fa.
Proof. reflexivity. Qed.
End NodeTraversalMethods.

Lemma interval_equality_full (i j : IM.Interval K) :
  GHC.Base.op_zeze__ i j = GHC.Base.op_zeze__ (IM.low i,IM.high i) (IM.low j,IM.high j).
Proof. destruct i,j; reflexivity. Qed.
Lemma interval_compare_full (i j : IM.Interval K) :
  GHC.Base.compare i j = GHC.Base.compare (IM.low i,IM.high i) (IM.low j,IM.high j).
Proof. destruct i,j; reflexivity. Qed.
Lemma interval_equality_law (i j : IM.Interval K) : GHC.Base.op_zeze__ i j = true <-> i=j.
Proof.
  destruct i as [l h], j as [l' h']; change (andb (GHC.Base.op_zeze__ l l') (GHC.Base.op_zeze__ h h') = true <->
    IM.MkInterval l h = IM.MkInterval l' h').
  rewrite andb_true_iff, !endpoint_eq by exact laws; split; [intros [-> ->]; reflexivity|intro E; injection E; auto].
Qed.

Lemma interval_order_methods (i j : IM.Interval K) :
  (GHC.Base.op_zl__ i j = match GHC.Base.compare (IM.low i) (IM.low j) with
    | Lt => true | Eq => GHC.Base.op_zl__ (IM.high i) (IM.high j) | Gt => false end) /\
  (GHC.Base.op_zlze__ i j = negb (GHC.Base.op_zl__ j i)) /\
  (GHC.Base.op_zg__ i j = GHC.Base.op_zl__ j i) /\
  (GHC.Base.op_zgze__ i j = negb (GHC.Base.op_zl__ i j)) /\
  (GHC.Base.max i j = if GHC.Base.op_zlze__ i j then j else i) /\
  (GHC.Base.min i j = if GHC.Base.op_zlze__ i j then i else j).
Proof. destruct i,j; repeat split; reflexivity. Qed.
Lemma node_order_methods {A} {EA : GHC.Base.Eq_ A} {OA : GHC.Base.Ord A} (i j : IM.Interval K) (a b : A) :
  (GHC.Base.op_zl__ (IM.MkNode i a) (IM.MkNode j b) = match GHC.Base.compare i j with
    | Lt => true | Eq => GHC.Base.op_zl__ a b | Gt => false end) /\
  (GHC.Base.op_zlze__ (IM.MkNode i a) (IM.MkNode j b) = negb (GHC.Base.op_zl__ (IM.MkNode j b) (IM.MkNode i a))) /\
  (GHC.Base.op_zg__ (IM.MkNode i a) (IM.MkNode j b) = GHC.Base.op_zl__ (IM.MkNode j b) (IM.MkNode i a)) /\
  (GHC.Base.op_zgze__ (IM.MkNode i a) (IM.MkNode j b) = negb (GHC.Base.op_zl__ (IM.MkNode i a) (IM.MkNode j b))) /\
  (GHC.Base.max (IM.MkNode i a) (IM.MkNode j b) = if GHC.Base.op_zlze__ (IM.MkNode i a) (IM.MkNode j b) then IM.MkNode j b else IM.MkNode i a) /\
  (GHC.Base.min (IM.MkNode i a) (IM.MkNode j b) = if GHC.Base.op_zlze__ (IM.MkNode i a) (IM.MkNode j b) then IM.MkNode i a else IM.MkNode j b).
Proof. repeat split; reflexivity. Qed.
Lemma map_order_methods {A} {EA : GHC.Base.Eq_ A} {OA : GHC.Base.Ord A} (m n : IM.IntervalMap K A) :
  (GHC.Base.op_zl__ m n = GHC.Base.op_zeze__ (GHC.Base.compare (entries m) (entries n)) Lt) /\
  (GHC.Base.op_zlze__ m n = GHC.Base.op_zsze__ (GHC.Base.compare (entries m) (entries n)) Gt) /\
  (GHC.Base.op_zg__ m n = GHC.Base.op_zeze__ (GHC.Base.compare (entries m) (entries n)) Gt) /\
  (GHC.Base.op_zgze__ m n = GHC.Base.op_zsze__ (GHC.Base.compare (entries m) (entries n)) Lt) /\
  (GHC.Base.max m n = if GHC.Base.op_zlze__ m n then n else m) /\
  (GHC.Base.min m n = if GHC.Base.op_zlze__ m n then m else n).
Proof.
  repeat split; try reflexivity.
  - change (GHC.Base.op_zeze__ (GHC.Base.compare m n) Lt = GHC.Base.op_zeze__ (GHC.Base.compare (entries m) (entries n)) Lt).
    now rewrite compare_entries.
  - change (GHC.Base.op_zsze__ (GHC.Base.compare m n) Gt = GHC.Base.op_zsze__ (GHC.Base.compare (entries m) (entries n)) Gt).
    now rewrite compare_entries.
  - change (GHC.Base.op_zeze__ (GHC.Base.compare m n) Gt = GHC.Base.op_zeze__ (GHC.Base.compare (entries m) (entries n)) Gt).
    now rewrite compare_entries.
  - change (GHC.Base.op_zsze__ (GHC.Base.compare m n) Lt = GHC.Base.op_zsze__ (GHC.Base.compare (entries m) (entries n)) Lt).
    now rewrite compare_entries.
Qed.

Section EqualityLaws.
Context {A} {EA : GHC.Base.Eq_ A} (payload_eq : forall a b : A, GHC.Base.op_zeze__ a b = true <-> a=b).
Lemma full_entry_equality_law (e f : IM.Interval K * A) : GHC.Base.op_zeze__ e f = true <-> e=f.
Proof.
  destruct e as [i a], f as [j b]; change (andb (GHC.Base.op_zeze__ i j) (GHC.Base.op_zeze__ a b) = true <-> (i,a)=(j,b)).
  rewrite andb_true_iff, interval_equality_law, payload_eq.
  split; [intros [-> ->]; reflexivity|intro E; injection E; auto].
Qed.
Lemma node_equality_law (x y : IM.Node K A) : GHC.Base.op_zeze__ x y = true <-> x=y.
Proof.
  destruct x as [i a], y as [j b]; change (andb (GHC.Base.op_zeze__ i j) (GHC.Base.op_zeze__ a b) = true <-> IM.MkNode i a = IM.MkNode j b).
  rewrite andb_true_iff, interval_equality_law, payload_eq.
  split; [intros [-> ->]; reflexivity|intro E; injection E; auto].
Qed.
Lemma full_entries_equality_law (xs ys : list (IM.Interval K * A)) : GHC.Base.op_zeze__ xs ys = true <-> xs=ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; try (split; discriminate); [tauto|].
  change (andb (GHC.Base.op_zeze__ x y) (GHC.Base.op_zeze__ xs ys) = true <-> x::xs=y::ys).
  rewrite andb_true_iff, full_entry_equality_law, IH.
  split; [intros [-> ->]; reflexivity|intro E; injection E; auto].
Qed.
Lemma map_equality_law (m n : IM.IntervalMap K A) : GHC.Base.op_zeze__ m n = true <-> entries m=entries n.
Proof. rewrite equality_entries; apply full_entries_equality_law. Qed.
End EqualityLaws.

Lemma mergeEntries_left_equal {A} i (a b : A) xs ys :
  mergeEntries ((i,a)::xs) ((i,b)::ys) = (i,a)::mergeEntries xs ((i,b)::ys).
Proof.
  rewrite mergeEntries_cons; cbn [fst].
  assert (E : GHC.Base.op_zgze__ i i = true) by (apply (proj2 (interval_ge_iff laws _ _)); apply intervalLE_refl; exact laws).
  now rewrite E.
Qed.
Lemma replace_valid {A B} (a : A) (m : IM.IntervalMap K B) : valid m -> valid (GHC.Base.op_zlzd__ a m).
Proof. apply fmap_valid. Qed.
Lemma node_fmap_identity {A} (n : IM.Node K A) : GHC.Base.fmap (fun x => x) n = n.
Proof. destruct n; reflexivity. Qed.
Lemma node_fmap_composition {A B C} (f : A -> B) (g : B -> C) (n : IM.Node K A) :
  GHC.Base.fmap g (GHC.Base.fmap f n) = GHC.Base.fmap (fun x => g (f x)) n.
Proof. destruct n; reflexivity. Qed.
Lemma interval_inequality (i j : IM.Interval K) :
  GHC.Base.op_zsze__ i j = negb (GHC.Base.op_zeze__ i j).
Proof. reflexivity. Qed.
Lemma node_inequality {A} {EA : GHC.Base.Eq_ A} (x y : IM.Node K A) :
  GHC.Base.op_zsze__ x y = negb (GHC.Base.op_zeze__ x y).
Proof. reflexivity. Qed.

Lemma mconcat_spec {A} (ms : list (IM.IntervalMap K A)) : Forall valid ms ->
  entries (GHC.Base.mconcat ms) = List.fold_right mergeEntries [] (List.map entries ms) /\
  valid (GHC.Base.mconcat ms).
Proof.
  rewrite monoid_concat; intro V; induction V as [|m ms V All [E W]].
  - exact (@empty_spec A).
  - cbn [List.map List.fold_right]. destruct (union_spec V W) as [U Vu].
    split; [rewrite U,E; reflexivity|exact Vu].
Qed.

End Operations.

(* Full types and transitive logical dependencies, including proof helpers. *)
Check @low_spec. Print Assumptions low_spec.
Check @high_spec. Print Assumptions high_spec.
Check @point_spec. Print Assumptions point_spec.
Check @empty_spec. Print Assumptions empty_spec.
Check @singleton_spec. Print Assumptions singleton_spec.
Check @insert_reversed. Print Assumptions insert_reversed.
Check @split_summary_safe. Print Assumptions split_summary_safe.
Check @atleast_split_safe. Print Assumptions atleast_split_safe.
Check @greater_split_safe. Print Assumptions greater_split_safe.
Check @larger_split_safe. Print Assumptions larger_split_safe.
Check @strict_larger_split_safe. Print Assumptions strict_larger_split_safe.
Check @interval_split_domain. Print Assumptions interval_split_domain.
Check @leastView_spec. Print Assumptions leastView_spec.
Check @leastView_none_iff. Print Assumptions leastView_none_iff.
Check @bounds_none_iff. Print Assumptions bounds_none_iff.
Check @bounds_endpoints. Print Assumptions bounds_endpoints.
Check @encloses. Print Assumptions encloses.
Check @bounds_enclosing. Print Assumptions bounds_enclosing.
Check @breakNodes. Print Assumptions breakNodes.
Check @splitList_summaryTest. Print Assumptions splitList_summaryTest.
Check @sorted_firstn. Print Assumptions sorted_firstn.
Check @in_firstn_mono. Print Assumptions in_firstn_mono.
Check @summaryTest_prefixMonotone. Print Assumptions summaryTest_prefixMonotone.
Check @split_ordered_test. Print Assumptions split_ordered_test.
Check @filter_all_true. Print Assumptions filter_all_true.
Check @sorted_filter. Print Assumptions sorted_filter.
Check @breakNodes_filters. Print Assumptions breakNodes_filters.
Check @split_ordered_filters. Print Assumptions split_ordered_filters.
Check @greater_upward. Print Assumptions greater_upward.
Check @splitAfter_spec. Print Assumptions splitAfter_spec.
Check @insertEntries. Print Assumptions insertEntries.
Check @insertEntries_before_equals. Print Assumptions insertEntries_before_equals.
Check @insertEntries_Forall. Print Assumptions insertEntries_Forall.
Check @insertEntries_sorted. Print Assumptions insertEntries_sorted.
Check @breakNodes_insertEntries. Print Assumptions breakNodes_insertEntries.
Check @larger_upward. Print Assumptions larger_upward.
Check @insert_spec. Print Assumptions insert_spec.
Check @atleast_prefixMonotone. Print Assumptions atleast_prefixMonotone.
Check @splitList_atleast. Print Assumptions splitList_atleast.
Check @breakNodes_reconstruct. Print Assumptions breakNodes_reconstruct.
Check @breakNodes_filter_suffix. Print Assumptions breakNodes_filter_suffix.
Check @breakNodes_head. Print Assumptions breakNodes_head.
Check @sorted_suffix. Print Assumptions sorted_suffix.
Check @valid_suffix. Print Assumptions valid_suffix.
Check @dropUntil_atleast_step. Print Assumptions dropUntil_atleast_step.
Check @takeUntil_greater_spec. Print Assumptions takeUntil_greater_spec.
Check @filter_two. Print Assumptions filter_two.
Check @inRange_spec. Print Assumptions inRange_spec.
Check @search_spec. Print Assumptions search_spec.
Check @intersections_spec. Print Assumptions intersections_spec.
Check @dominators_spec. Print Assumptions dominators_spec.
Check @mapEntry. Print Assumptions mapEntry.
Check @fmap_entries. Print Assumptions fmap_entries.
Check @fmap_node_measure. Print Assumptions fmap_node_measure.
Check @sorted_mapEntry. Print Assumptions sorted_mapEntry.
Check @fmap_valid. Print Assumptions fmap_valid.
Check @fmap_identity_entries. Print Assumptions fmap_identity_entries.
Check @fmap_composition_entries. Print Assumptions fmap_composition_entries.
Check @replace_entries. Print Assumptions replace_entries.
Check @foldMap_payloads. Print Assumptions foldMap_payloads.
Check @foldr_payloads. Print Assumptions foldr_payloads.
Check @toList_payloads. Print Assumptions toList_payloads.
Check @node_equality_full. Print Assumptions node_equality_full.
Check @entry_list_equality. Print Assumptions entry_list_equality.
Check @equality_entries. Print Assumptions equality_entries.
Check @inequality_entries. Print Assumptions inequality_entries.
Check @node_compare_full. Print Assumptions node_compare_full.
Check @entry_list_compare. Print Assumptions entry_list_compare.
Check @compare_entries. Print Assumptions compare_entries.
Check @mergeEntries. Print Assumptions mergeEntries.
Check @mergeEntries_nil_r. Print Assumptions mergeEntries_nil_r.
Check @mergeEntries_cons. Print Assumptions mergeEntries_cons.
Check @mergeEntries_left_chunk. Print Assumptions mergeEntries_left_chunk.
Check @interval_strict_complement. Print Assumptions interval_strict_complement.
Check @mergeEntries_right_chunk. Print Assumptions mergeEntries_right_chunk.
Check @mergeEntries_Forall. Print Assumptions mergeEntries_Forall.
Check @mergeEntries_sorted. Print Assumptions mergeEntries_sorted.
Check @strict_larger_upward. Print Assumptions strict_larger_upward.
Check @interval_viewl_spec. Print Assumptions interval_viewl_spec.
Check @cache_cons. Print Assumptions cache_cons.
Check @cache_append. Print Assumptions cache_append.
Check @entries_cons. Print Assumptions entries_cons.
Check @entries_append. Print Assumptions entries_append.
Check @union_spec. Print Assumptions union_spec.
Check @digitRel. Print Assumptions digitRel.
Check @nodeRel. Print Assumptions nodeRel.
Check @treeRel. Print Assumptions treeRel.
Check @digitRel_contents. Print Assumptions digitRel_contents.
Check @nodeRel_contents. Print Assumptions nodeRel_contents.
Check @treeRel_contents. Print Assumptions treeRel_contents.
Check @digitRel_measure. Print Assumptions digitRel_measure.
Check @treeRel_cache. Print Assumptions treeRel_cache.
Check @treeRel_validity. Print Assumptions treeRel_validity.
Check @traverseDigit_rel. Print Assumptions traverseDigit_rel.
Check @unsafeTraverseNode_rel. Print Assumptions unsafeTraverseNode_rel.
Check @unsafeTraverse_rel. Print Assumptions unsafeTraverse_rel.
Check @payloadRel. Print Assumptions payloadRel.
Check @payloadRel_valid. Print Assumptions payloadRel_valid.
Check @traverse_valid. Print Assumptions traverse_valid.
Check @traverse_entries. Print Assumptions traverse_entries.
Check @sequenceA_valid. Print Assumptions sequenceA_valid.
Check @sequenceA_entries. Print Assumptions sequenceA_entries.
Check @mapM_valid. Print Assumptions mapM_valid.
Check @mapM_entries. Print Assumptions mapM_entries.
Check @sequence_valid. Print Assumptions sequence_valid.
Check @sequence_entries. Print Assumptions sequence_entries.
Check @foldl_payloads. Print Assumptions foldl_payloads.
Check @foldl'_payloads. Print Assumptions foldl'_payloads.
Check @foldr'_payloads. Print Assumptions foldr'_payloads.
Check @foldMap'_payloads. Print Assumptions foldMap'_payloads.
Check @null_payloads. Print Assumptions null_payloads.
Check @length_payloads. Print Assumptions length_payloads.
Check @node_fmap. Print Assumptions node_fmap.
Check @node_replace. Print Assumptions node_replace.
Check @node_foldMap. Print Assumptions node_foldMap.
Check @node_foldr. Print Assumptions node_foldr.
Check @node_foldl. Print Assumptions node_foldl.
Check @node_foldl'. Print Assumptions node_foldl'.
Check @node_foldr'. Print Assumptions node_foldr'.
Check @node_toList. Print Assumptions node_toList.
Check @node_null. Print Assumptions node_null.
Check @node_length. Print Assumptions node_length.
Check @mergeEntries_associative. Print Assumptions mergeEntries_associative.
Check @semigroup_union. Print Assumptions semigroup_union.
Check @monoid_union. Print Assumptions monoid_union.
Check @monoid_empty. Print Assumptions monoid_empty.
Check @monoid_concat. Print Assumptions monoid_concat.
Check @union_left_identity. Print Assumptions union_left_identity.
Check @union_right_identity. Print Assumptions union_right_identity.
Check @union_associative. Print Assumptions union_associative.
Check @sum_payloads. Print Assumptions sum_payloads.
Check @product_payloads. Print Assumptions product_payloads.
Check @fold_payloads. Print Assumptions fold_payloads.
Check @node_fold. Print Assumptions node_fold.
Check @node_foldMap'. Print Assumptions node_foldMap'.
Check @node_sum. Print Assumptions node_sum.
Check @node_product. Print Assumptions node_product.
Check @node_traverse. Print Assumptions node_traverse.
Check @node_sequenceA. Print Assumptions node_sequenceA.
Check @node_mapM. Print Assumptions node_mapM.
Check @node_sequence. Print Assumptions node_sequence.
Check @interval_equality_full. Print Assumptions interval_equality_full.
Check @interval_compare_full. Print Assumptions interval_compare_full.
Check @interval_equality_law. Print Assumptions interval_equality_law.
Check @interval_order_methods. Print Assumptions interval_order_methods.
Check @node_order_methods. Print Assumptions node_order_methods.
Check @map_order_methods. Print Assumptions map_order_methods.
Check @full_entry_equality_law. Print Assumptions full_entry_equality_law.
Check @node_equality_law. Print Assumptions node_equality_law.
Check @full_entries_equality_law. Print Assumptions full_entries_equality_law.
Check @map_equality_law. Print Assumptions map_equality_law.
Check @mergeEntries_left_equal. Print Assumptions mergeEntries_left_equal.
Check @replace_valid. Print Assumptions replace_valid.
Check @node_fmap_identity. Print Assumptions node_fmap_identity.
Check @node_fmap_composition. Print Assumptions node_fmap_composition.
Check @interval_inequality. Print Assumptions interval_inequality.
Check @node_inequality. Print Assumptions node_inequality.
Check @mconcat_spec. Print Assumptions mconcat_spec.
