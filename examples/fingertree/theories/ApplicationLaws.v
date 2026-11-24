From Stdlib Require Import Lists.List Bool.Bool.
Require Import FingerTreeProofs.IntervalOperations FingerTreeProofs.PriorityOperations
  FingerTreeProofs.CoreInstances Proofs.GHC.Base.
Set Implicit Arguments.
Set Typeclasses Depth 8.
Module IM := Data.IntervalMap.FingerTree.
Module PQ := Data.PriorityQueue.FingerTree.

(* All dictionaries below are the actual translated dictionaries. Comparison
   ties are Boolean equivalences, not propositional equality of leaf values. *)
Lemma pair_compare_laws {A B} `{GHC.Base.Ord A} `{GHC.Base.Ord B} :
  ComparisonLaws (@GHC.Base.compare A _ _) ->
  ComparisonLaws (@GHC.Base.compare B _ _) ->
  ComparisonLaws (@GHC.Base.compare (A * B) _ _).
Proof.
  intros CA CB; eapply (comparison_pullback _
    (pairCompare (@GHC.Base.compare A _ _) (@GHC.Base.compare B _ _)) (fun x : A * B => x)).
  - intros [] []; reflexivity.
  - apply pairComparisonLaws; assumption.
Qed.
Lemma list_compare_laws {A} `{GHC.Base.Ord A} :
  ComparisonLaws (@GHC.Base.compare A _ _) -> ComparisonLaws (@GHC.Base.compare (list A) _ _).
Proof.
  intro C; eapply (comparison_pullback _ (listCompare (@GHC.Base.compare A _ _)) (fun x : list A => x));
    [apply source_list_compare|apply listComparisonLaws; exact C].
Qed.
Lemma pair_eq_compare {A B} `{GHC.Base.Ord A} `{GHC.Base.Ord B} :
  EqCompare (@GHC.Base.op_zeze__ A _) (@GHC.Base.compare A _ _) ->
  EqCompare (@GHC.Base.op_zeze__ B _) (@GHC.Base.compare B _ _) ->
  EqCompare (@GHC.Base.op_zeze__ (A * B) _) (@GHC.Base.compare (A * B) _ _).
Proof. intros EA EB [x u] [y v]; exact (pairEqCompare _ _ EA EB (x,u) (y,v)). Qed.
Lemma list_eq_compare {A} `{GHC.Base.Ord A} :
  EqCompare (@GHC.Base.op_zeze__ A _) (@GHC.Base.compare A _ _) ->
  EqCompare (@GHC.Base.op_zeze__ (list A) _) (@GHC.Base.compare (list A) _ _).
Proof. intros E x y; rewrite source_list_compare; apply listEqCompare; exact E. Qed.

Section IntervalEquality.
Context {K} `{EqLaws K}.
Lemma interval_EqLaws : EqLaws (IM.Interval K).
Proof.
  apply (EqLaws_pullback (fun i : IM.Interval K => (IM.low i, IM.high i)));
    [intros [] []; reflexivity|intros; reflexivity].
Qed.
#[local] Existing Instance interval_EqLaws.
Context {A} `{EqLaws A}.
Lemma node_EqLaws : EqLaws (IM.Node K A).
Proof.
  apply (EqLaws_pullback (@IntervalModel.fullEntry K A));
    [apply node_equality_full|intros; reflexivity].
Qed.
Lemma map_EqLaws : EqLaws (IM.IntervalMap K A).
Proof.
  apply (EqLaws_pullback (@IntervalModel.entries K A));
    [apply equality_entries|intros; reflexivity].
Qed.
End IntervalEquality.

Section IntervalComparison.
Context {K} `{GHC.Base.Ord K}.
Context (CK : ComparisonLaws (@GHC.Base.compare K _ _)).
Lemma interval_comparison : ComparisonLaws (@GHC.Base.compare (IM.Interval K) _ _).
Proof.
  eapply (comparison_pullback _ (@GHC.Base.compare (K * K) _ _) (fun i : IM.Interval K => (IM.low i, IM.high i)));
    [intros [] []; reflexivity|apply pair_compare_laws; exact CK].
Qed.
Context {A} `{GHC.Base.Ord A}.
Context (CA : ComparisonLaws (@GHC.Base.compare A _ _)).
Lemma node_comparison : ComparisonLaws (@GHC.Base.compare (IM.Node K A) _ _).
Proof.
  eapply (comparison_pullback _ (@GHC.Base.compare (IM.Interval K * A) _ _) (@IntervalModel.fullEntry K A));
    [apply node_compare_full|apply pair_compare_laws; [apply interval_comparison|exact CA]].
Qed.
Lemma map_comparison : ComparisonLaws (@GHC.Base.compare (IM.IntervalMap K A) _ _).
Proof.
  eapply (comparison_pullback _ (@GHC.Base.compare (list (IM.Interval K * A)) _ _) (@IntervalModel.entries K A));
    [apply compare_entries|apply list_compare_laws, pair_compare_laws; [apply interval_comparison|exact CA]].
Qed.
End IntervalComparison.

Section IntervalCoherence.
Context {K} `{GHC.Base.Ord K}.
Context (EK : EqCompare (@GHC.Base.op_zeze__ K _) (@GHC.Base.compare K _ _)).
Lemma interval_eq_compare : EqCompare (@GHC.Base.op_zeze__ (IM.Interval K) _) (@GHC.Base.compare (IM.Interval K) _ _).
Proof.
  intros x y; rewrite interval_equality_full, interval_compare_full; apply pair_eq_compare; exact EK.
Qed.
Context {A} `{GHC.Base.Ord A}.
Context (EA : EqCompare (@GHC.Base.op_zeze__ A _) (@GHC.Base.compare A _ _)).
Lemma node_eq_compare : EqCompare (@GHC.Base.op_zeze__ (IM.Node K A) _) (@GHC.Base.compare (IM.Node K A) _ _).
Proof.
  intros x y; rewrite node_equality_full, node_compare_full; apply pair_eq_compare;
    [apply interval_eq_compare|exact EA].
Qed.
Lemma map_eq_compare : EqCompare (@GHC.Base.op_zeze__ (IM.IntervalMap K A) _) (@GHC.Base.compare (IM.IntervalMap K A) _ _).
Proof.
  intros x y; rewrite equality_entries, compare_entries; apply list_eq_compare, pair_eq_compare;
    [apply interval_eq_compare|exact EA].
Qed.
End IntervalCoherence.

(* Derived interval/node (<) delegates its final field to that field's actual
   (<). Only this field-method coherence is needed, not EndpointOrderLaws. *)
Local Ltac derived_methods LT SW :=
  unfold OrdMethods; repeat apply conj; intros x y;
  first [apply LT | match goal with |- _ = ?rhs =>
    first [change (negb (GHC.Base.op_zl__ y x) = rhs)
          |change (GHC.Base.op_zl__ y x = rhs)
          |change (negb (GHC.Base.op_zl__ x y) = rhs)
          |change ((if negb (GHC.Base.op_zl__ y x) then x else y) = rhs)
          |change ((if negb (GHC.Base.op_zl__ y x) then y else x) = rhs)]
    end; rewrite !LT, ?(SW x y); destruct (GHC.Base.compare x y); reflexivity].

Section IntervalMethods.
Context {K} `{GHC.Base.Ord K}.
Lemma interval_methods : ComparisonLaws (@GHC.Base.compare K _ _) ->
  (forall x y : K, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) -> OrdMethods (IM.Interval K).
Proof.
  intros C E; destruct (interval_comparison C) as [_ [SW _]].
  assert (LT : forall x y : IM.Interval K, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)).
  { intros [l h] [l' h']; change ((match GHC.Base.compare l l' with Eq => GHC.Base.op_zl__ h h' | Lt => true | Gt => false end) =
      isLT (lexCompare (GHC.Base.compare l l') (GHC.Base.compare h h'))).
    rewrite E; destruct (GHC.Base.compare l l'); reflexivity. }
  derived_methods LT SW.
Qed.
Lemma node_methods {A} `{GHC.Base.Ord A} :
  ComparisonLaws (@GHC.Base.compare K _ _) -> ComparisonLaws (@GHC.Base.compare A _ _) ->
  (forall x y : A, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) -> OrdMethods (IM.Node K A).
Proof.
  intros CK CA E; destruct (node_comparison CK CA) as [_ [SW _]].
  assert (LT : forall x y : IM.Node K A, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)).
  { intros [i a] [j b]; change ((match GHC.Base.compare i j with Eq => GHC.Base.op_zl__ a b | Lt => true | Gt => false end) =
      isLT (lexCompare (GHC.Base.compare i j) (GHC.Base.compare a b))).
    rewrite E; destruct (GHC.Base.compare i j); reflexivity. }
  derived_methods LT SW.
Qed.
Lemma map_methods {A} `{GHC.Base.Ord A} : OrdMethods (IM.IntervalMap K A).
Proof. direct_ord_methods. Qed.
End IntervalMethods.

Section IntervalBundles.
Context {K} `{GHC.Base.Ord K}
  (CK : ComparisonLaws (@GHC.Base.compare K _ _))
  (EK : EqCompare (@GHC.Base.op_zeze__ K _) (@GHC.Base.compare K _ _)).
Lemma interval_behavior
  (LK : forall x y : K, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) : OrdBehavior (IM.Interval K).
Proof. split; [apply interval_comparison; exact CK|split; [apply interval_eq_compare; exact EK|apply interval_methods; assumption]]. Qed.
Lemma interval_order (LK : forall x y : K, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) : OrderLaws (IM.Interval K).
Proof. apply ord_behavior_laws; exact (interval_behavior LK). Qed.
Lemma interval_minmax (LK : forall x y : K, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) : MinMaxLaws (IM.Interval K).
Proof. apply order_minmax_laws; exact (interval_order LK). Qed.
Context {A} `{GHC.Base.Ord A}
  (CA : ComparisonLaws (@GHC.Base.compare A _ _))
  (EA : EqCompare (@GHC.Base.op_zeze__ A _) (@GHC.Base.compare A _ _)).
Lemma node_behavior
  (LA : forall x y : A, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) : OrdBehavior (IM.Node K A).
Proof. split; [apply node_comparison; assumption|split; [apply node_eq_compare; assumption|apply node_methods; assumption]]. Qed.
Lemma node_order (LA : forall x y : A, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) : OrderLaws (IM.Node K A).
Proof. apply ord_behavior_laws; exact (node_behavior LA). Qed.
Lemma node_minmax (LA : forall x y : A, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) : MinMaxLaws (IM.Node K A).
Proof. apply order_minmax_laws; exact (node_order LA). Qed.
Lemma map_behavior : OrdBehavior (IM.IntervalMap K A).
Proof. split; [apply map_comparison; assumption|split; [apply map_eq_compare; assumption|apply map_methods]]. Qed.
Lemma map_order : OrderLaws (IM.IntervalMap K A).
Proof. apply ord_behavior_laws; exact map_behavior. Qed.
Lemma map_minmax : MinMaxLaws (IM.IntervalMap K A).
Proof. apply order_minmax_laws; exact map_order. Qed.
End IntervalBundles.

Section QueueEquality.
Context {K} {EK : GHC.Base.Eq_ K} {OK : GHC.Base.Ord K}
  (laws : @PriorityModel.PriorityOrderLaws K EK OK) {A} {EA : GHC.Base.Eq_ A}.
Context {ELK : @EqLaws K EK} {ELA : @EqLaws A EA}.
Lemma queue_eq_reflexive (q : PQ.PQueue K A) : valid q -> GHC.Base.op_zeze__ q q = true.
Proof. intro V; rewrite (eq_model laws V V); apply Eq_refl. Qed.
Lemma queue_eq_symmetric (q r : PQ.PQueue K A) : valid q -> valid r ->
  GHC.Base.op_zeze__ q r = GHC.Base.op_zeze__ r q.
Proof. intros V W; rewrite !eq_model by assumption; apply Eq_sym. Qed.
Lemma queue_eq_transitive (q r s : PQ.PQueue K A) : valid q -> valid r -> valid s ->
  GHC.Base.op_zeze__ q r = true -> GHC.Base.op_zeze__ r s = true -> GHC.Base.op_zeze__ q s = true.
Proof.
  intros V W U E F; rewrite (eq_model laws V W) in E; rewrite (eq_model laws W U) in F.
  rewrite (eq_model laws V U); eapply Eq_trans; eassumption.
Qed.
End QueueEquality.

Section QueueComparison.
Context {K} `{GHC.Base.Ord K} (laws : @PriorityModel.PriorityOrderLaws K H H0).
Context {A} `{GHC.Base.Ord A}.
Context (CK : ComparisonLaws (@GHC.Base.compare K _ _))
  (CA : ComparisonLaws (@GHC.Base.compare A _ _)).
(* Restrict only the comparator, not the raw representation or dictionaries. *)
Lemma queue_comparison : ComparisonLaws
  (fun x y : {q : PQ.PQueue K A | valid q} => GHC.Base.compare (proj1_sig x) (proj1_sig y)).
Proof.
  eapply (comparison_pullback _ (@GHC.Base.compare (list (K * A)) _ _) (fun x : {q : PQ.PQueue K A | valid q} => model (proj1_sig x)));
    [intros [q V] [r W]; apply compare_model; assumption|].
  apply list_compare_laws, pair_compare_laws; assumption.
Qed.
Lemma queue_eq_compare
  (EK : EqCompare (@GHC.Base.op_zeze__ K _) (@GHC.Base.compare K _ _))
  (EA : EqCompare (@GHC.Base.op_zeze__ A _) (@GHC.Base.compare A _ _))
  (q r : PQ.PQueue K A) : valid q -> valid r ->
  GHC.Base.op_zeze__ q r = isEQ (GHC.Base.compare q r).
Proof.
  intros V W; rewrite (eq_model laws V W), (compare_model laws V W).
  apply list_eq_compare, pair_eq_compare; assumption.
Qed.
End QueueComparison.

Lemma queue_methods {K A} `{GHC.Base.Ord K} `{GHC.Base.Ord A} : OrdMethods (PQ.PQueue K A).
Proof. direct_ord_methods. Qed.

Section QueueOrder.
Context {K} `{GHC.Base.Ord K} (laws : @PriorityModel.PriorityOrderLaws K H H0).
Context {A} `{GHC.Base.Ord A}
  (CK : ComparisonLaws (@GHC.Base.compare K _ _))
  (CA : ComparisonLaws (@GHC.Base.compare A _ _)).

Lemma queue_compare_reflexive (q : PQ.PQueue K A) : valid q -> GHC.Base.compare q q = Eq.
Proof.
  intro V; destruct (queue_comparison laws CK CA) as [R _].
  exact (R (exist _ q V)).
Qed.
Lemma queue_compare_opposite (q r : PQ.PQueue K A) : valid q -> valid r ->
  GHC.Base.compare r q = compareOpp (GHC.Base.compare q r).
Proof.
  intros V W; destruct (queue_comparison laws CK CA) as [_ [S _]].
  exact (S (exist _ q V) (exist _ r W)).
Qed.
Lemma queue_compare_transitive (q r s : PQ.PQueue K A) : valid q -> valid r -> valid s ->
  GHC.Base.compare q r = Lt -> GHC.Base.compare r s = Lt -> GHC.Base.compare q s = Lt.
Proof.
  intros V W U; destruct (queue_comparison laws CK CA) as [_ [_ [T _]]].
  exact (T (exist _ q V) (exist _ r W) (exist _ s U)).
Qed.
Lemma queue_compare_ties (q q' r r' : PQ.PQueue K A) :
  valid q -> valid q' -> valid r -> valid r' ->
  GHC.Base.compare q q' = Eq -> GHC.Base.compare r r' = Eq ->
  GHC.Base.compare q r = GHC.Base.compare q' r'.
Proof.
  intros V V' W W'; destruct (queue_comparison laws CK CA) as [_ [_ [_ T]]].
  exact (T (exist _ q V) (exist _ q' V') (exist _ r W) (exist _ r' W')).
Qed.

Context (EK : EqCompare (@GHC.Base.op_zeze__ K _) (@GHC.Base.compare K _ _))
  (EA : EqCompare (@GHC.Base.op_zeze__ A _) (@GHC.Base.compare A _ _)).

(* OrderLaws, with each quantifier restricted to the actual valid raw queues.
   Antisymmetry uses their Boolean equality, not equality of models or trees. *)
Lemma queue_order :
  (forall q : PQ.PQueue K A, valid q -> GHC.Base.op_zlze__ q q = true) /\
  (forall q r s : PQ.PQueue K A, valid q -> valid r -> valid s ->
    GHC.Base.op_zlze__ q r = true -> GHC.Base.op_zlze__ r s = true -> GHC.Base.op_zlze__ q s = true) /\
  (forall q r : PQ.PQueue K A, valid q -> valid r -> orb (GHC.Base.op_zlze__ q r) (GHC.Base.op_zlze__ r q) = true) /\
  (forall q r : PQ.PQueue K A, valid q -> valid r ->
    (GHC.Base.op_zlze__ q r = true /\ GHC.Base.op_zlze__ r q = true) <-> GHC.Base.op_zeze__ q r = true) /\
  (forall q r s : PQ.PQueue K A, valid q -> valid r -> valid s ->
    GHC.Base.op_zl__ q r = true -> GHC.Base.op_zl__ r s = true -> GHC.Base.op_zl__ q s = true) /\
  (forall q r : PQ.PQueue K A, valid q -> valid r ->
    GHC.Base.op_zl__ q r = andb (GHC.Base.op_zlze__ q r) (negb (GHC.Base.op_zeze__ q r))) /\
  (forall q r : PQ.PQueue K A, valid q -> valid r ->
    GHC.Base.op_zlze__ (GHC.Base.min q r) q = true /\ GHC.Base.op_zlze__ (GHC.Base.min q r) r = true) /\
  (forall q r : PQ.PQueue K A, valid q -> valid r ->
    GHC.Base.op_zlze__ q (GHC.Base.max q r) = true /\ GHC.Base.op_zlze__ r (GHC.Base.max q r) = true) /\
  (forall q r s : PQ.PQueue K A, valid q -> valid r -> valid s ->
    (GHC.Base.op_zlze__ s q = true /\ GHC.Base.op_zlze__ s r = true) <-> GHC.Base.op_zlze__ s (GHC.Base.min q r) = true) /\
  (forall q r s : PQ.PQueue K A, valid q -> valid r -> valid s ->
    (GHC.Base.op_zlze__ q s = true /\ GHC.Base.op_zlze__ r s = true) <-> GHC.Base.op_zlze__ (GHC.Base.max q r) s = true).
Proof.
  destruct (@queue_methods K A H H0 H1 H2) as [LT [LE [GT [GE [MN MX]]]]].
  pose proof (queue_comparison laws CK CA) as C.
  assert (R : forall q : PQ.PQueue K A, valid q -> GHC.Base.compare q q = Eq)
    by (intros; apply queue_compare_reflexive; assumption).
  assert (SW : forall q r : PQ.PQueue K A, valid q -> valid r ->
    GHC.Base.compare r q = compareOpp (GHC.Base.compare q r))
    by (intros; apply queue_compare_opposite; assumption).
  assert (T : forall q r s : PQ.PQueue K A, valid q -> valid r -> valid s ->
    isLE (GHC.Base.compare q r) = true -> isLE (GHC.Base.compare r s) = true -> isLE (GHC.Base.compare q s) = true).
  { intros q r s V W U; exact (comparison_le_trans _ C (exist _ q V) (exist _ r W) (exist _ s U)). }
  assert (E : forall q r : PQ.PQueue K A, valid q -> valid r ->
    GHC.Base.op_zeze__ q r = isEQ (GHC.Base.compare q r))
    by (intros; apply queue_eq_compare; assumption).
  repeat apply conj.
  - intros q V; rewrite LE, (R q V); reflexivity.
  - intros q r s V W U X Y; rewrite LE in X, Y; rewrite LE; exact (T q r s V W U X Y).
  - intros q r V W; rewrite !LE, (SW q r V W); destruct (GHC.Base.compare q r); reflexivity.
  - intros q r V W; rewrite !LE, (E q r V W), (SW q r V W).
    destruct (GHC.Base.compare q r); cbn; intuition discriminate.
  - intros q r s V W U X Y; rewrite LT in X,Y; rewrite LT.
    destruct (GHC.Base.compare q r) eqn:X', (GHC.Base.compare r s) eqn:Y'; try discriminate.
    rewrite (queue_compare_transitive V W U X' Y'); reflexivity.
  - intros q r V W; rewrite LT, LE, (E q r V W); destruct (GHC.Base.compare q r); reflexivity.
  - intros q r V W; rewrite MN, !LE; destruct (GHC.Base.compare q r) eqn:X;
      cbn [isLE]; rewrite ?(R q V), ?(R r W), ?(SW q r V W), ?X; split; reflexivity.
  - intros q r V W; rewrite MX, !LE; destruct (GHC.Base.compare q r) eqn:X;
      cbn [isLE]; rewrite ?(R q V), ?(R r W), ?(SW q r V W), ?X; split; reflexivity.
  - intros q r s V W U; rewrite MN, !LE; destruct (GHC.Base.compare q r) eqn:X; cbn [isLE].
    + pose proof (compare_eq_right _ C (exist _ s U) (exist _ q V) (exist _ r W) X) as Z.
      cbn [proj1_sig] in Z; rewrite Z; tauto.
    + split; [tauto|intro Z; split; [exact Z|]]; eapply T; [exact U|exact V|exact W|exact Z|rewrite X; reflexivity].
    + split; [tauto|intro Z; split; [|exact Z]]; eapply T; [exact U|exact W|exact V|exact Z|rewrite (SW q r V W), X; reflexivity].
  - intros q r s V W U; rewrite MX, !LE; destruct (GHC.Base.compare q r) eqn:X; cbn [isLE].
    + pose proof (compare_eq_left _ C (exist _ q V) (exist _ r W) (exist _ s U) X) as Z.
      cbn [proj1_sig] in Z; rewrite Z; tauto.
    + split; [tauto|intro Z; split; [|exact Z]]; eapply T; [exact V|exact W|exact U|rewrite X; reflexivity|exact Z].
    + split; [tauto|intro Z; split; [exact Z|]]; eapply T; [exact W|exact V|exact U|rewrite (SW q r V W), X; reflexivity|exact Z].
Qed.

(* The eight lattice identities are Boolean laws on valid queues. The min/max
   implementations select an input, so their intermediate queues remain valid. *)
Lemma queue_minmax :
  (forall q : PQ.PQueue K A, valid q -> GHC.Base.op_zeze__ (GHC.Base.min q q) q = true) /\
  (forall q : PQ.PQueue K A, valid q -> GHC.Base.op_zeze__ (GHC.Base.max q q) q = true) /\
  (forall q r : PQ.PQueue K A, valid q -> valid r -> GHC.Base.op_zeze__ (GHC.Base.min q r) (GHC.Base.min r q) = true) /\
  (forall q r : PQ.PQueue K A, valid q -> valid r -> GHC.Base.op_zeze__ (GHC.Base.max q r) (GHC.Base.max r q) = true) /\
  (forall q r s : PQ.PQueue K A, valid q -> valid r -> valid s ->
    GHC.Base.op_zeze__ (GHC.Base.min (GHC.Base.min q r) s) (GHC.Base.min q (GHC.Base.min r s)) = true) /\
  (forall q r s : PQ.PQueue K A, valid q -> valid r -> valid s ->
    GHC.Base.op_zeze__ (GHC.Base.max (GHC.Base.max q r) s) (GHC.Base.max q (GHC.Base.max r s)) = true) /\
  (forall q r : PQ.PQueue K A, valid q -> valid r -> GHC.Base.op_zeze__ (GHC.Base.min q (GHC.Base.max q r)) q = true) /\
  (forall q r : PQ.PQueue K A, valid q -> valid r -> GHC.Base.op_zeze__ (GHC.Base.max q (GHC.Base.min q r)) q = true).
Proof.
  destruct queue_order as [R [T [_ [AS [_ [_ [MB [XB [GLB LUB]]]]]]]]].
  assert (VM : forall q r : PQ.PQueue K A, valid q -> valid r -> valid (GHC.Base.min q r))
    by (intros; apply min_valid; assumption).
  assert (VX : forall q r : PQ.PQueue K A, valid q -> valid r -> valid (GHC.Base.max q r))
    by (intros; apply max_valid; assumption).
  pose (M1 := fun q r V W => proj1 (MB q r V W)).
  pose (M2 := fun q r V W => proj2 (MB q r V W)).
  pose (X1 := fun q r V W => proj1 (XB q r V W)).
  pose (X2 := fun q r V W => proj2 (XB q r V W)).
  repeat apply conj.
  - intros q V; apply (proj1 (AS _ _ (VM q q V V) V)); split; [apply MB; assumption|apply GLB; [exact V|exact V|exact V|split; apply R; exact V]].
  - intros q V; apply (proj1 (AS _ _ (VX q q V V) V)); split; [apply LUB; [exact V|exact V|exact V|split; apply R; exact V]|apply XB; assumption].
  - intros q r V W; apply (proj1 (AS _ _ (VM q r V W) (VM r q W V))); split;
      apply GLB; try (apply VM; assumption); try assumption; split; apply MB; assumption.
  - intros q r V W; apply (proj1 (AS _ _ (VX q r V W) (VX r q W V))); split;
      apply LUB; try (apply VX; assumption); try assumption; split; apply XB; assumption.
  - intros q r s V W U.
    apply (proj1 (AS _ _ (VM _ _ (VM _ _ V W) U) (VM _ _ V (VM _ _ W U)))); split.
    + apply (proj1 (GLB _ _ _ V (VM _ _ W U) (VM _ _ (VM _ _ V W) U))); split.
      * exact (T _ _ _ (VM _ _ (VM _ _ V W) U) (VM _ _ V W) V
          (M1 _ _ (VM _ _ V W) U) (M1 _ _ V W)).
      * apply (proj1 (GLB _ _ _ W U (VM _ _ (VM _ _ V W) U))); split.
        -- exact (T _ _ _ (VM _ _ (VM _ _ V W) U) (VM _ _ V W) W
             (M1 _ _ (VM _ _ V W) U) (M2 _ _ V W)).
        -- exact (M2 _ _ (VM _ _ V W) U).
    + apply (proj1 (GLB _ _ _ (VM _ _ V W) U (VM _ _ V (VM _ _ W U)))); split.
      * apply (proj1 (GLB _ _ _ V W (VM _ _ V (VM _ _ W U)))); split.
        -- exact (M1 _ _ V (VM _ _ W U)).
        -- exact (T _ _ _ (VM _ _ V (VM _ _ W U)) (VM _ _ W U) W
             (M2 _ _ V (VM _ _ W U)) (M1 _ _ W U)).
      * exact (T _ _ _ (VM _ _ V (VM _ _ W U)) (VM _ _ W U) U
          (M2 _ _ V (VM _ _ W U)) (M2 _ _ W U)).
  - intros q r s V W U.
    apply (proj1 (AS _ _ (VX _ _ (VX _ _ V W) U) (VX _ _ V (VX _ _ W U)))); split.
    + apply (proj1 (LUB _ _ _ (VX _ _ V W) U (VX _ _ V (VX _ _ W U)))); split.
      * apply (proj1 (LUB _ _ _ V W (VX _ _ V (VX _ _ W U)))); split.
        -- exact (X1 _ _ V (VX _ _ W U)).
        -- exact (T _ _ _ W (VX _ _ W U) (VX _ _ V (VX _ _ W U))
             (X1 _ _ W U) (X2 _ _ V (VX _ _ W U))).
      * exact (T _ _ _ U (VX _ _ W U) (VX _ _ V (VX _ _ W U))
          (X2 _ _ W U) (X2 _ _ V (VX _ _ W U))).
    + apply (proj1 (LUB _ _ _ V (VX _ _ W U) (VX _ _ (VX _ _ V W) U))); split.
      * exact (T _ _ _ V (VX _ _ V W) (VX _ _ (VX _ _ V W) U)
          (X1 _ _ V W) (X1 _ _ (VX _ _ V W) U)).
      * apply (proj1 (LUB _ _ _ W U (VX _ _ (VX _ _ V W) U))); split.
        -- exact (T _ _ _ W (VX _ _ V W) (VX _ _ (VX _ _ V W) U)
             (X2 _ _ V W) (X1 _ _ (VX _ _ V W) U)).
        -- exact (X2 _ _ (VX _ _ V W) U).
  - intros q r V W; apply (proj1 (AS _ _ (VM _ _ V (VX _ _ V W)) V)); split.
    + apply MB; [assumption|apply VX; assumption].
    + apply GLB; try assumption; [apply VX; assumption|split; [apply R; assumption|apply XB; assumption]].
  - intros q r V W; apply (proj1 (AS _ _ (VX _ _ V (VM _ _ V W)) V)); split.
    + apply LUB; try assumption; [apply VM; assumption|split; [apply R; assumption|apply MB; assumption]].
    + apply XB; [assumption|apply VM; assumption].
Qed.
End QueueOrder.

Check @pair_compare_laws. Print Assumptions pair_compare_laws.
Check @list_compare_laws. Print Assumptions list_compare_laws.
Check @pair_eq_compare. Print Assumptions pair_eq_compare.
Check @list_eq_compare. Print Assumptions list_eq_compare.
Check @interval_EqLaws. Print Assumptions interval_EqLaws.
Check @node_EqLaws. Print Assumptions node_EqLaws.
Check @map_EqLaws. Print Assumptions map_EqLaws.
Check @interval_comparison. Print Assumptions interval_comparison.
Check @node_comparison. Print Assumptions node_comparison.
Check @map_comparison. Print Assumptions map_comparison.
Check @interval_eq_compare. Print Assumptions interval_eq_compare.
Check @node_eq_compare. Print Assumptions node_eq_compare.
Check @map_eq_compare. Print Assumptions map_eq_compare.
Check @interval_methods. Print Assumptions interval_methods.
Check @node_methods. Print Assumptions node_methods.
Check @map_methods. Print Assumptions map_methods.
Check @interval_behavior. Print Assumptions interval_behavior.
Check @interval_order. Print Assumptions interval_order.
Check @interval_minmax. Print Assumptions interval_minmax.
Check @node_behavior. Print Assumptions node_behavior.
Check @node_order. Print Assumptions node_order.
Check @node_minmax. Print Assumptions node_minmax.
Check @map_behavior. Print Assumptions map_behavior.
Check @map_order. Print Assumptions map_order.
Check @map_minmax. Print Assumptions map_minmax.
Check @queue_eq_reflexive. Print Assumptions queue_eq_reflexive.
Check @queue_eq_symmetric. Print Assumptions queue_eq_symmetric.
Check @queue_eq_transitive. Print Assumptions queue_eq_transitive.
Check @queue_comparison. Print Assumptions queue_comparison.
Check @queue_eq_compare. Print Assumptions queue_eq_compare.
Check @queue_methods. Print Assumptions queue_methods.
Check @queue_compare_reflexive. Print Assumptions queue_compare_reflexive.
Check @queue_compare_opposite. Print Assumptions queue_compare_opposite.
Check @queue_compare_transitive. Print Assumptions queue_compare_transitive.
Check @queue_compare_ties. Print Assumptions queue_compare_ties.
Check @queue_order. Print Assumptions queue_order.
Check @queue_minmax. Print Assumptions queue_minmax.
