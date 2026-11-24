From Stdlib Require Import Lists.List Bool.Bool Sorting.Sorted micromega.Lia.
Require Import Data.IntervalMap.FingerTree FingerTreeProofs.CoreModel
  FingerTreeProofs.CoreOperations FingerTreeProofs.CoreSearch.
Import ListNotations.
Set Implicit Arguments.
Module IM := Data.IntervalMap.FingerTree.

(* Laws constrain the supplied dictionary; they do not install a replacement
   order or ask for equality on the measurement type. *)
Section EndpointOrder.
Context {K : Type} `{GHC.Base.Ord K}.
Record EndpointOrderLaws : Prop := {
  endpoint_eq : forall x y : K, GHC.Base.op_zeze__ x y = true <-> x = y;
  endpoint_ne : forall x y : K, GHC.Base.op_zsze__ x y = negb (GHC.Base.op_zeze__ x y);
  endpoint_refl : forall x : K, GHC.Base.op_zlze__ x x = true;
  endpoint_trans : forall x y z : K, GHC.Base.op_zlze__ x y = true ->
    GHC.Base.op_zlze__ y z = true -> GHC.Base.op_zlze__ x z = true;
  endpoint_antisym : forall x y : K, GHC.Base.op_zlze__ x y = true ->
    GHC.Base.op_zlze__ y x = true -> x = y;
  endpoint_total : forall x y : K, GHC.Base.op_zlze__ x y = true \/
    GHC.Base.op_zlze__ y x = true;
  endpoint_lt : forall x y : K, GHC.Base.op_zl__ x y = negb (GHC.Base.op_zlze__ y x);
  endpoint_gt : forall x y : K, GHC.Base.op_zg__ x y = negb (GHC.Base.op_zlze__ x y);
  endpoint_ge : forall x y : K, GHC.Base.op_zgze__ x y = GHC.Base.op_zlze__ y x;
  endpoint_compare : forall x y : K, GHC.Base.compare x y =
    if GHC.Base.op_zlze__ x y then
      if GHC.Base.op_zlze__ y x then Eq else Lt else Gt;
  endpoint_max : forall x y : K, GHC.Base.max x y =
    if GHC.Base.op_zlze__ x y then y else x;
  endpoint_min : forall x y : K, GHC.Base.min x y =
    if GHC.Base.op_zlze__ x y then x else y
}.
Context (laws : EndpointOrderLaws).
Local Abbreviation le := GHC.Base.op_zlze__.

Lemma endpoint_reverse_false x y : le x y = false -> le y x = true.
Proof. intro E; destruct (endpoint_total laws x y); congruence. Qed.

Lemma endpoint_max_assoc x y z :
  GHC.Base.max (GHC.Base.max x y) z = GHC.Base.max x (GHC.Base.max y z).
Proof.
  rewrite !endpoint_max by exact laws.
  destruct (le x y) eqn:A, (le y z) eqn:B, (le x z) eqn:C;
    cbn; rewrite ?A, ?B, ?C; try reflexivity.
  - pose proof (endpoint_trans laws A B); congruence.
  - pose proof (endpoint_trans laws C (endpoint_reverse_false B)); congruence.
Qed.

Lemma endpoint_max_upper x y : le x (GHC.Base.max x y) = true /\
  le y (GHC.Base.max x y) = true.
Proof.
  rewrite endpoint_max by exact laws; destruct (le x y) eqn:E;
    split; auto using endpoint_refl, endpoint_reverse_false.
Qed.

Lemma endpoint_max_least x y z : le x z = true -> le y z = true ->
  le (GHC.Base.max x y) z = true.
Proof. rewrite endpoint_max by exact laws; destruct (le x y); auto. Qed.

Lemma intervalUnion_assoc (p q r : IM.IntInterval K) :
  IM.intervalUnion (IM.intervalUnion p q) r = IM.intervalUnion p (IM.intervalUnion q r).
Proof.
  destruct p, q, r; cbn [IM.intervalUnion]; try reflexivity.
  rewrite endpoint_max_assoc; reflexivity.
Qed.
Lemma intervalUnion_left_id (p : IM.IntInterval K) : IM.intervalUnion IM.NoInterval p = p.
Proof. reflexivity. Qed.
Lemma intervalUnion_right_id (p : IM.IntInterval K) : IM.intervalUnion p IM.NoInterval = p.
Proof. destruct p; reflexivity. Qed.
Lemma summary_mappend (p q : IM.IntInterval K) :
  GHC.Base.mappend p q = IM.intervalUnion p q.
Proof. reflexivity. Qed.
Lemma summary_semigroup (p q : IM.IntInterval K) :
  GHC.Base.op_zlzlzgzg__ p q = IM.intervalUnion p q.
Proof. reflexivity. Qed.
Lemma summary_mempty : (GHC.Base.mempty : IM.IntInterval K) = IM.NoInterval.
Proof. reflexivity. Qed.
Lemma summary_mconcat (ps : list (IM.IntInterval K)) :
  GHC.Base.mconcat ps = List.fold_right IM.intervalUnion IM.NoInterval ps.
Proof. reflexivity. Qed.

Definition fullEntry {A} (n : IM.Node K A) : IM.Interval K * A :=
  match n with IM.MkNode i a => (i,a) end.
Definition rawTree {A} (m : IM.IntervalMap K A) :=
  match m with IM.MkIntervalMap t => t end.
Definition entries {A} (m : IM.IntervalMap K A) : list (IM.Interval K * A) :=
  List.map fullEntry (contents (rawTree m)).
Definition closed (i : IM.Interval K) : Prop := le (IM.low i) (IM.high i) = true.
Definition intervalLE (i j : IM.Interval K) : Prop :=
  le (IM.low i) (IM.low j) = true /\
  (IM.low i = IM.low j -> le (IM.high i) (IM.high j) = true).
Definition entryLE {A} (e f : IM.Interval K * A) : Prop := intervalLE (fst e) (fst f).
Definition cacheValid {A} (m : IM.IntervalMap K A) : Prop :=
  validity (IM.Measured__IntInterval__Node) (rawTree m).
Definition valid {A} (m : IM.IntervalMap K A) : Prop :=
  EndpointOrderLaws /\ cacheValid m /\
  List.Forall (fun e => closed (fst e)) (entries m) /\
  StronglySorted entryLE (entries m).
Definition entryMeasure {A} (e : IM.Interval K * A) : IM.IntInterval K :=
  IM.MkIntInterval (fst e) (IM.high (fst e)).
Definition summary {A} (xs : list (IM.Interval K * A)) : IM.IntInterval K :=
  List.fold_right (fun e acc => IM.intervalUnion (entryMeasure e) acc) IM.NoInterval xs.

Lemma node_measure {A} (n : IM.Node K A) : Data.FingerTree.measure n = entryMeasure (fullEntry n).
Proof. destruct n; reflexivity. Qed.
Lemma summary_nil {A} : summary (@nil (IM.Interval K * A)) = IM.NoInterval.
Proof. reflexivity. Qed.
Lemma summary_cons {A} (e : IM.Interval K * A) xs :
  summary (e :: xs) = IM.intervalUnion (entryMeasure e) (summary xs).
Proof. reflexivity. Qed.
Lemma summary_empty_iff {A} (xs : list (IM.Interval K * A)) :
  summary xs = IM.NoInterval <-> xs = [].
Proof.
  destruct xs as [|[i a] xs]; [cbn [summary]; tauto|].
  rewrite summary_cons; destruct (summary xs); cbn [entryMeasure IM.intervalUnion];
    split; discriminate.
Qed.
Lemma summary_nonempty {A} (xs : list (IM.Interval K * A)) : xs <> [] ->
  exists i h, summary xs = IM.MkIntInterval i h.
Proof.
  destruct xs as [|[i a] xs]; [contradiction|].
  rewrite summary_cons; destruct (summary xs); cbn [entryMeasure IM.intervalUnion];
    cbn [IM.intervalUnion]; do 2 eexists; reflexivity.
Qed.
Lemma summary_app {A} (xs ys : list (IM.Interval K * A)) :
  summary (xs ++ ys) = IM.intervalUnion (summary xs) (summary ys).
Proof.
  induction xs as [|e xs IH]; [reflexivity|].
  change (IM.intervalUnion (entryMeasure e) (summary (xs ++ ys)) =
    IM.intervalUnion (IM.intervalUnion (entryMeasure e) (summary xs)) (summary ys)).
  rewrite IH, intervalUnion_assoc; reflexivity.
Qed.
Lemma summary_listMeasure {A} (xs : list (IM.Node K A)) :
  listMeasure (@Data.FingerTree.measure _ _ _ _ IM.Measured__IntInterval__Node) xs =
    summary (List.map fullEntry xs).
Proof. induction xs as [|[i a] xs IH]; cbn [listMeasure List.fold_right summary List.map];
  [reflexivity|change (IM.intervalUnion (IM.MkIntInterval i (IM.high i))
    (listMeasure (@Data.FingerTree.measure _ _ _ _ IM.Measured__IntInterval__Node) xs) =
    IM.intervalUnion (IM.MkIntInterval i (IM.high i)) (summary (List.map fullEntry xs)));
    rewrite IH; reflexivity]. Qed.
Lemma measure_entries {A} (m : IM.IntervalMap K A) : cacheValid m ->
  Data.FingerTree.measure (rawTree m) = summary (entries m).
Proof.
  intro V; unfold entries.
  rewrite (@measure_contents (IM.IntInterval K) IM.Semigroup__IntInterval IM.Monoid__IntInterval intervalUnion_assoc
    intervalUnion_left_id intervalUnion_right_id _
    IM.Measured__IntInterval__Node (rawTree m) V).
  apply summary_listMeasure.
Qed.

(* Exact meaning of a nonempty summary: rightmost full interval, and an
   attained least upper bound of all high endpoints. *)
Lemma summary_endpoints {A} (xs : list (IM.Interval K * A)) i h :
  summary xs = IM.MkIntInterval i h ->
  (exists pre a, xs = pre ++ [(i,a)]) /\
  (exists e, In e xs /\ IM.high (fst e) = h) /\
  (forall e, In e xs -> le (IM.high (fst e)) h = true) /\
  (forall z, (forall e, In e xs -> le (IM.high (fst e)) z = true) -> le h z = true).
Proof.
  revert i h; induction xs as [|[j a] xs IH]; intros i h; [discriminate|].
  rewrite summary_cons; unfold entryMeasure; cbn [fst].
  destruct xs as [|e xs].
  - cbn [summary IM.intervalUnion]; intro E; injection E as Ei Eh; subst i h.
    repeat split.
    + exists [], a; reflexivity.
    + exists (j,a); cbn; auto.
    + intros f [Ef|Ef]; [subst; apply endpoint_refl; exact laws|contradiction].
    + intros z Hz; apply (Hz (j,a)); cbn; auto.
  - destruct (@summary_nonempty A (e :: xs) ltac:(discriminate)) as [k [h' E]].
    rewrite E; cbn [IM.intervalUnion]; intro Out; injection Out as Ei Eh; subst i h.
    destruct (IH _ _ E) as [[pre [b Ep]] [[winner [Win Ew]] [Upper Least]]].
    split; [exists ((j,a)::pre), b; cbn; now rewrite Ep|].
    split.
    + rewrite endpoint_max by exact laws; destruct (le (IM.high j) h') eqn:C.
      * exists winner; split; [right; exact Win|exact Ew].
      * exists (j,a); split; [left; reflexivity|reflexivity].
    + split.
      * intros f [Ef|Ef].
         -- subst f; apply (proj1 (endpoint_max_upper (IM.high j) h')).
        -- eapply endpoint_trans; [exact laws|apply Upper; exact Ef|
             apply (proj2 (endpoint_max_upper (IM.high j) h'))].
      * intros z Hz; apply endpoint_max_least.
        -- apply (Hz (j,a)); left; reflexivity.
        -- apply Least; intros f Hf; apply Hz; right; exact Hf.
Qed.

Lemma prefix_summary_nonempty {A} (xs : list (IM.Node K A)) w :
  nonemptyPrefixDomain (@Data.FingerTree.measure _ _ _ _ IM.Measured__IntInterval__Node) xs w ->
  exists i h, w = IM.MkIntInterval i h.
Proof.
  intros [n [Pos [Bound E]]]; rewrite E, summary_listMeasure.
  apply summary_nonempty; intro Z; apply List.map_eq_nil in Z.
  destruct xs; cbn in *; [lia|]. destruct n; [lia|discriminate].
Qed.

Lemma intervalLE_refl i : intervalLE i i.
Proof. split; intros; apply endpoint_refl; exact laws. Qed.
Lemma intervalLE_trans i j k : intervalLE i j -> intervalLE j k -> intervalLE i k.
Proof.
  intros [A B] [C D]; split; [eapply endpoint_trans; eauto|].
  intro E.
  assert (F : IM.low i = IM.low j).
  { apply (endpoint_antisym laws A); rewrite E; exact C. }
  eapply endpoint_trans; [exact laws|apply B; exact F|apply D; congruence].
Qed.
Lemma interval_ge_iff i j : GHC.Base.op_zgze__ i j = true <-> intervalLE j i.
Proof.
  destruct i as [il ih], j as [jl jh].
  change (negb (match GHC.Base.compare il jl with
    | Lt => true | Eq => GHC.Base.op_zl__ ih jh | Gt => false end) = true <->
    le jl il = true /\ (jl = il -> le jh ih = true)).
  rewrite endpoint_compare, endpoint_lt by exact laws.
  destruct (le il jl) eqn:A, (le jl il) eqn:B; cbn; rewrite ?Bool.negb_involutive.
  - assert (E : il = jl) by (apply (endpoint_antisym laws A B)); subst jl; tauto.
  - split; [discriminate|intros [C _]; discriminate].
  - split; [intro; split; [reflexivity|intros E; subst jl; rewrite endpoint_refl in A by exact laws; discriminate]|auto].
  - destruct (endpoint_total laws il jl); congruence.
Qed.

Definition summaryTest (f : IM.Interval K -> bool) (fallback : bool) (w : IM.IntInterval K) : bool :=
  match w with IM.NoInterval => fallback | IM.MkIntInterval i _ => f i end.

(* Sortedness is relevant only to the last-interval component, not to high
   endpoint maxima. The equivalence retains all occurrences in the list. *)
Lemma summary_test_exists {A} (f : IM.Interval K -> bool) fallback xs :
  (forall i j, intervalLE i j -> f i = true -> f j = true) ->
  StronglySorted (@entryLE A) xs -> xs <> [] ->
  (summaryTest f fallback (summary xs) = true <-> exists e, In e xs /\ f (fst e) = true).
Proof.
  intros Up Sorted NE.
  destruct (summary_nonempty NE) as [i [h E]].
  destruct (summary_endpoints xs E) as [[pre [a Last]] _].
  rewrite E; cbn [summaryTest].
  assert (LastIn : In (i,a) xs) by (rewrite Last; apply in_or_app; right; cbn; auto).
  split; [intro F; exists (i,a); auto|].
  intros [e [He F]].
  assert (Rel : forall ys, StronglySorted (@entryLE A) ys ->
      forall e z, In e ys -> ys = pre ++ [z] -> intervalLE (fst e) (fst z)).
  { clear Last LastIn Sorted NE E He F xs i h a e.
    induction pre as [|p pre IH]; intros ys S e z Hin Ey; subst ys.
    - cbn in Hin; destruct Hin as [<-|[]]; apply intervalLE_refl.
    - inversion S as [|? ? St All]; subst.
      destruct Hin as [<-|Hin].
      + rewrite Forall_forall in All; apply All; apply in_or_app; right; cbn; auto.
      + eapply IH; eauto. }
  apply (Up _ _ (Rel _ Sorted e (i,a) He Last)); exact F.
Qed.

Lemma intervalLE_total i j : intervalLE i j \/ intervalLE j i.
Proof.
  destruct (GHC.Base.op_zlze__ (IM.low i) (IM.low j)) eqn:A;
    destruct (GHC.Base.op_zlze__ (IM.low j) (IM.low i)) eqn:B.
  - assert (E : IM.low i = IM.low j) by (apply (endpoint_antisym laws A B)).
    destruct (endpoint_total laws (IM.high i) (IM.high j)) as [C|C];
      [left|right]; split; auto.
  - left; split; [exact A|intro E; rewrite E, endpoint_refl in B by exact laws; discriminate].
  - right; split; [exact B|intro E; rewrite E, endpoint_refl in A by exact laws; discriminate].
  - destruct (endpoint_total laws (IM.low i) (IM.low j)); congruence.
Qed.

Lemma endpoint_le_max k x y :
  GHC.Base.op_zlze__ k (GHC.Base.max x y) =
    orb (GHC.Base.op_zlze__ k x) (GHC.Base.op_zlze__ k y).
Proof.
  rewrite endpoint_max by exact laws.
  destruct (GHC.Base.op_zlze__ x y) eqn:XY;
    destruct (GHC.Base.op_zlze__ k x) eqn:KX;
    destruct (GHC.Base.op_zlze__ k y) eqn:KY; cbn; try reflexivity.
  - pose proof (endpoint_trans laws KX XY); congruence.
  - pose proof (endpoint_trans laws KY (endpoint_reverse_false XY)); congruence.
Qed.

Definition atleastTest (k : K) (w : IM.IntInterval K) : bool :=
  match w with IM.NoInterval => false | IM.MkIntInterval _ h => GHC.Base.op_zlze__ k h end.
Lemma atleastTest_union k p q :
  atleastTest k (IM.intervalUnion p q) = orb (atleastTest k p) (atleastTest k q).
Proof.
  destruct p, q; cbn [IM.intervalUnion atleastTest];
    rewrite ?Bool.orb_false_r; try reflexivity; apply endpoint_le_max.
Qed.
Lemma summary_atleast {A} k (xs : list (IM.Interval K * A)) :
  atleastTest k (summary xs) = List.existsb (fun e => GHC.Base.op_zlze__ k (IM.high (fst e))) xs.
Proof.
  induction xs as [|e xs IH]; [reflexivity|].
  rewrite summary_cons, atleastTest_union, IH; reflexivity.
Qed.

End EndpointOrder.

(* Complete exported-constant type and transitive-assumption inventory. *)
Check @EndpointOrderLaws. Print Assumptions EndpointOrderLaws.
Check @endpoint_eq. Print Assumptions endpoint_eq.
Check @endpoint_ne. Print Assumptions endpoint_ne.
Check @endpoint_refl. Print Assumptions endpoint_refl.
Check @endpoint_trans. Print Assumptions endpoint_trans.
Check @endpoint_antisym. Print Assumptions endpoint_antisym.
Check @endpoint_total. Print Assumptions endpoint_total.
Check @endpoint_lt. Print Assumptions endpoint_lt.
Check @endpoint_gt. Print Assumptions endpoint_gt.
Check @endpoint_ge. Print Assumptions endpoint_ge.
Check @endpoint_compare. Print Assumptions endpoint_compare.
Check @endpoint_max. Print Assumptions endpoint_max.
Check @endpoint_min. Print Assumptions endpoint_min.
Check @endpoint_reverse_false. Print Assumptions endpoint_reverse_false.
Check @endpoint_max_assoc. Print Assumptions endpoint_max_assoc.
Check @endpoint_max_upper. Print Assumptions endpoint_max_upper.
Check @endpoint_max_least. Print Assumptions endpoint_max_least.
Check @intervalUnion_assoc. Print Assumptions intervalUnion_assoc.
Check @intervalUnion_left_id. Print Assumptions intervalUnion_left_id.
Check @intervalUnion_right_id. Print Assumptions intervalUnion_right_id.
Check @summary_mappend. Print Assumptions summary_mappend.
Check @summary_semigroup. Print Assumptions summary_semigroup.
Check @summary_mempty. Print Assumptions summary_mempty.
Check @summary_mconcat. Print Assumptions summary_mconcat.
Check @fullEntry. Print Assumptions fullEntry.
Check @rawTree. Print Assumptions rawTree.
Check @entries. Print Assumptions entries.
Check @closed. Print Assumptions closed.
Check @intervalLE. Print Assumptions intervalLE.
Check @entryLE. Print Assumptions entryLE.
Check @cacheValid. Print Assumptions cacheValid.
Check @valid. Print Assumptions valid.
Check @entryMeasure. Print Assumptions entryMeasure.
Check @summary. Print Assumptions summary.
Check @node_measure. Print Assumptions node_measure.
Check @summary_nil. Print Assumptions summary_nil.
Check @summary_cons. Print Assumptions summary_cons.
Check @summary_empty_iff. Print Assumptions summary_empty_iff.
Check @summary_nonempty. Print Assumptions summary_nonempty.
Check @summary_app. Print Assumptions summary_app.
Check @summary_listMeasure. Print Assumptions summary_listMeasure.
Check @measure_entries. Print Assumptions measure_entries.
Check @summary_endpoints. Print Assumptions summary_endpoints.
Check @prefix_summary_nonempty. Print Assumptions prefix_summary_nonempty.
Check @intervalLE_refl. Print Assumptions intervalLE_refl.
Check @intervalLE_trans. Print Assumptions intervalLE_trans.
Check @interval_ge_iff. Print Assumptions interval_ge_iff.
Check @summaryTest. Print Assumptions summaryTest.
Check @summary_test_exists. Print Assumptions summary_test_exists.
Check @intervalLE_total. Print Assumptions intervalLE_total.
Check @endpoint_le_max. Print Assumptions endpoint_le_max.
Check @atleastTest. Print Assumptions atleastTest.
Check @atleastTest_union. Print Assumptions atleastTest_union.
Check @summary_atleast. Print Assumptions summary_atleast.
