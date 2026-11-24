From Stdlib Require Import Lists.List Bool.Bool Logic.FunctionalExtensionality.
Set Warnings "-masking-absolute-name".
Require Import FingerTreeProofs.IntervalModel FingerTreeProofs.IntervalOperations
  FingerTreeProofs.CoreTraversal FingerTreeProofs.ApplicativeValidity.
Require Import Data.Functor.Compose Data.Functor.Identity Proofs.GHC.Base.
Import ListNotations.
Set Implicit Arguments.
Set Typeclasses Depth 8.

(* These laws concern the supplied comparison, not a replacement dictionary. *)
Definition opposite (c : comparison) : comparison :=
  match c with Eq => Eq | Lt => Gt | Gt => Lt end.
Record ComparisonLaws {A} (cmp : A -> A -> comparison) : Prop := {
  comparison_eq : forall x y, cmp x y = Eq <-> x=y;
  comparison_swap : forall x y, cmp y x = opposite (cmp x y);
  comparison_trans : forall x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt
}.
Lemma comparison_laws_ext {A} (cmp cmp' : A -> A -> comparison) :
  (forall x y, cmp x y=cmp' x y) -> ComparisonLaws cmp -> ComparisonLaws cmp'.
Proof.
  intros E L; constructor; intros; repeat rewrite <- E in *;
    eauto using comparison_eq, comparison_swap, comparison_trans.
Qed.

Definition lexCompare {A B} (ca : A -> A -> comparison) (cb : B -> B -> comparison)
  (x y : A*B) : comparison :=
  match x,y with (x,a),(y,b) => match ca x y with Eq => cb a b | c => c end end.

Lemma lexCompare_laws {A B} ca cb : @ComparisonLaws A ca -> @ComparisonLaws B cb ->
  ComparisonLaws (lexCompare ca cb).
Proof.
  intros LA LB; constructor.
  - intros [x a] [y b]; unfold lexCompare; cbn.
    destruct (ca x y) eqn:C; try (split; [discriminate|intro E; injection E as E1 E2;
      subst; pose proof (proj2 (comparison_eq LA y y) eq_refl); congruence]).
    rewrite comparison_eq by exact LB.
    apply (proj1 (comparison_eq LA x y)) in C; subst y.
    split; [intro; now subst|intro E; now injection E].
  - intros [x a] [y b]; unfold lexCompare; cbn.
    rewrite (comparison_swap LA x y); destruct (ca x y); cbn; auto using comparison_swap.
  - intros [x a] [y b] [z c]; unfold lexCompare; cbn.
    destruct (ca x y) eqn:XY, (ca y z) eqn:YZ; try discriminate.
    + apply (proj1 (comparison_eq LA x y)) in XY; apply (proj1 (comparison_eq LA y z)) in YZ; subst.
      rewrite (proj2 (comparison_eq LA z z) eq_refl); apply (comparison_trans LB).
    + apply (proj1 (comparison_eq LA x y)) in XY; subst; rewrite YZ; auto.
    + apply (proj1 (comparison_eq LA y z)) in YZ; subst; rewrite XY; auto.
    + intros _ _; rewrite (comparison_trans LA _ _ _ XY YZ); reflexivity.
Qed.

Fixpoint listCompare {A} (cmp : A -> A -> comparison) (xs ys : list A) : comparison :=
  match xs,ys with
  | [],[] => Eq | [],_::_ => Lt | _::_,[] => Gt
  | x::xs,y::ys => match cmp x y with Eq => listCompare cmp xs ys | c => c end
  end.

Lemma listCompare_laws {A} cmp : @ComparisonLaws A cmp -> ComparisonLaws (listCompare cmp).
Proof.
  intro L; constructor.
  - intro xs; induction xs as [|x xs IH]; intros [|y ys]; cbn;
      try (split; discriminate); [tauto|].
    destruct (cmp x y) eqn:C; try (split; [discriminate|intro E; injection E as E1 E2;
      subst; pose proof (proj2 (comparison_eq L y y) eq_refl); congruence]).
    rewrite IH; apply (proj1 (comparison_eq L x y)) in C; subst y.
    split; [intro; now subst|intro E; now injection E].
  - intro xs; induction xs as [|x xs IH]; intros [|y ys]; cbn; try reflexivity.
    rewrite (comparison_swap L x y); destruct (cmp x y); cbn; auto.
  - intro xs; induction xs as [|x xs IH]; intros [|y ys] [|z zs]; cbn; try discriminate; auto.
    destruct (cmp x y) eqn:XY, (cmp y z) eqn:YZ; try discriminate.
    + apply (proj1 (comparison_eq L x y)) in XY; apply (proj1 (comparison_eq L y z)) in YZ; subst.
      rewrite (proj2 (comparison_eq L z z) eq_refl); apply IH.
    + apply (proj1 (comparison_eq L x y)) in XY; subst; rewrite YZ; auto.
    + apply (proj1 (comparison_eq L y z)) in YZ; subst; rewrite XY; auto.
    + intros _ _; rewrite (comparison_trans L _ _ _ XY YZ); reflexivity.
Qed.

Section Endpoints.
Context {K} `{GHC.Base.Ord K} (laws : EndpointOrderLaws).
Lemma endpoint_comparison_laws : ComparisonLaws (@GHC.Base.compare K H H0).
Proof.
  constructor.
  - intros x y; rewrite endpoint_compare by exact laws.
    destruct (GHC.Base.op_zlze__ x y) eqn:A, (GHC.Base.op_zlze__ y x) eqn:B; cbn.
    + split; [intro; eapply endpoint_antisym; eauto|auto].
    + split; [discriminate|intro E; subst; rewrite endpoint_refl in B by exact laws; discriminate].
    + split; [discriminate|intro E; subst; rewrite endpoint_refl in A by exact laws; discriminate].
    + split; [discriminate|intro E; subst; rewrite endpoint_refl in A by exact laws; discriminate].
  - intros x y; rewrite !endpoint_compare by exact laws.
    destruct (GHC.Base.op_zlze__ x y) eqn:A, (GHC.Base.op_zlze__ y x) eqn:B; cbn; try reflexivity.
    destruct (endpoint_total laws x y); congruence.
  - intros x y z; rewrite !endpoint_compare by exact laws.
    destruct (GHC.Base.op_zlze__ x y) eqn:A, (GHC.Base.op_zlze__ y x) eqn:B; try discriminate.
    destruct (GHC.Base.op_zlze__ y z) eqn:C, (GHC.Base.op_zlze__ z y) eqn:D; try discriminate.
    intros _ _.
    rewrite (@endpoint_trans K H H0 laws x y z A C).
    destruct (GHC.Base.op_zlze__ z x) eqn:E; [|reflexivity].
    pose proof (@endpoint_trans K H H0 laws y z x C E); congruence.
Qed.
Lemma interval_comparison_laws : ComparisonLaws (fun x y : IM.Interval K => GHC.Base.compare x y).
Proof.
  pose proof (lexCompare_laws endpoint_comparison_laws endpoint_comparison_laws) as L.
  constructor.
  - intros [x a] [y b]; change (lexCompare GHC.Base.compare GHC.Base.compare (x,a) (y,b) = Eq <-> IM.MkInterval x a = IM.MkInterval y b).
    rewrite (comparison_eq L); split; intro E; injection E; intros; subst; reflexivity.
  - intros [x a] [y b]; exact (comparison_swap L (x,a) (y,b)).
  - intros [x a] [y b] [z c]; exact (comparison_trans L (x,a) (y,b) (z,c)).
Qed.
End Endpoints.

Definition comparisonLE (c : comparison) : bool := match c with Gt => false | _ => true end.
Definition comparisonLT (c : comparison) : bool := match c with Lt => true | _ => false end.
Lemma bool_equiv b c : (b=true <-> c=true) -> b=c.
Proof. destruct b,c; intuition discriminate. Qed.
Lemma comparison_reflexive {A} cmp (L : @ComparisonLaws A cmp) x : cmp x x = Eq.
Proof. apply (proj2 (comparison_eq L _ _)); reflexivity. Qed.
Lemma comparison_le_total {A} cmp (L : @ComparisonLaws A cmp) x y :
  comparisonLE (cmp x y)=true \/ comparisonLE (cmp y x)=true.
Proof. rewrite (comparison_swap L x y); destruct (cmp x y); cbn; auto. Qed.
Lemma comparison_le_trans {A} cmp (L : @ComparisonLaws A cmp) x y z :
  comparisonLE (cmp x y)=true -> comparisonLE (cmp y z)=true -> comparisonLE (cmp x z)=true.
Proof.
  destruct (cmp x y) eqn:XY, (cmp y z) eqn:YZ; cbn; try discriminate; intros _ _.
  - apply (proj1 (comparison_eq L _ _)) in XY; subst; now rewrite YZ.
  - apply (proj1 (comparison_eq L _ _)) in XY; subst; now rewrite YZ.
  - apply (proj1 (comparison_eq L _ _)) in YZ; subst; now rewrite XY.
  - rewrite (comparison_trans L _ _ _ XY YZ); reflexivity.
Qed.
Lemma comparison_le_antisymmetric {A} cmp (L : @ComparisonLaws A cmp) x y :
  comparisonLE (cmp x y)=true -> comparisonLE (cmp y x)=true -> x=y.
Proof.
  rewrite (comparison_swap L x y); destruct (cmp x y) eqn:C; cbn; try discriminate.
  intros; apply (proj1 (comparison_eq L _ _)); exact C.
Qed.

(* [obs] is deliberately not required to be injective. For maps it is the full
   entry list, so equal lists may have different raw tree shapes. *)
Record OrderSpec {T O} `{GHC.Base.Ord T} (obs : T -> O) (cmp : O -> O -> comparison) : Prop := {
  order_eq_spec : forall x y, GHC.Base.op_zeze__ x y=true <-> obs x=obs y;
  order_ne_spec : forall x y, GHC.Base.op_zsze__ x y=negb (GHC.Base.op_zeze__ x y);
  order_compare_spec : forall x y, GHC.Base.compare x y=cmp (obs x) (obs y);
  order_lt_spec : forall x y, GHC.Base.op_zl__ x y=comparisonLT (cmp (obs x) (obs y));
  order_le_spec : forall x y, GHC.Base.op_zlze__ x y=comparisonLE (cmp (obs x) (obs y));
  order_gt_spec : forall x y, GHC.Base.op_zg__ x y=comparisonLT (cmp (obs y) (obs x));
  order_ge_spec : forall x y, GHC.Base.op_zgze__ x y=comparisonLE (cmp (obs y) (obs x));
  order_max_spec : forall x y, GHC.Base.max x y=if GHC.Base.op_zlze__ x y then y else x;
  order_min_spec : forall x y, GHC.Base.min x y=if GHC.Base.op_zlze__ x y then x else y
}.

Section DerivedOrderLaws.
Context {T O} `{GHC.Base.Ord T} (obs : T -> O) cmp
  (CL : ComparisonLaws cmp) (OS : OrderSpec obs cmp).

Lemma observational_eq_laws :
  (forall x : T, GHC.Base.op_zeze__ x x=true) /\
  (forall x y : T, GHC.Base.op_zeze__ x y=GHC.Base.op_zeze__ y x) /\
  (forall x y z : T, GHC.Base.op_zeze__ x y=true -> GHC.Base.op_zeze__ y z=true -> GHC.Base.op_zeze__ x z=true) /\
  (forall x y : T, GHC.Base.op_zsze__ x y=negb (GHC.Base.op_zeze__ x y)).
Proof.
  repeat split.
  - intro; apply (proj2 (order_eq_spec OS _ _)); reflexivity.
  - intros; apply bool_equiv; rewrite !(order_eq_spec OS); split; congruence.
  - intros; apply (proj2 (order_eq_spec OS _ _));
      apply (proj1 (order_eq_spec OS _ _)) in H1,H2; congruence.
  - apply (order_ne_spec OS).
Qed.

Lemma observational_order_laws :
  (forall x : T, GHC.Base.compare x x=Eq) /\
  (forall x y : T, GHC.Base.compare x y=Eq <-> obs x=obs y) /\
  (forall x y : T, GHC.Base.compare y x=opposite (GHC.Base.compare x y)) /\
  (forall x : T, GHC.Base.op_zl__ x x=false) /\
  (forall x y z : T, GHC.Base.op_zl__ x y=true -> GHC.Base.op_zl__ y z=true -> GHC.Base.op_zl__ x z=true) /\
  (forall x : T, GHC.Base.op_zlze__ x x=true) /\
  (forall x y z : T, GHC.Base.op_zlze__ x y=true -> GHC.Base.op_zlze__ y z=true -> GHC.Base.op_zlze__ x z=true) /\
  (forall x y : T, GHC.Base.op_zlze__ x y=true -> GHC.Base.op_zlze__ y x=true -> obs x=obs y) /\
  (forall x y : T, GHC.Base.op_zlze__ x y=true \/ GHC.Base.op_zlze__ y x=true) /\
  (forall x y : T, GHC.Base.op_zl__ x y=negb (GHC.Base.op_zlze__ y x)) /\
  (forall x y : T, GHC.Base.op_zg__ x y=GHC.Base.op_zl__ y x) /\
  (forall x y : T, GHC.Base.op_zgze__ x y=GHC.Base.op_zlze__ y x).
Proof.
  repeat match goal with |- _ /\ _ => split end.
  - intro; rewrite (order_compare_spec OS); apply comparison_reflexive; exact CL.
  - intros; rewrite (order_compare_spec OS); apply comparison_eq; exact CL.
  - intros; rewrite !(order_compare_spec OS); apply comparison_swap; exact CL.
  - intro; rewrite (order_lt_spec OS), (comparison_reflexive CL); reflexivity.
  - intros x y z; rewrite !(order_lt_spec OS).
    destruct (cmp (obs x) (obs y)) eqn:XY, (cmp (obs y) (obs z)) eqn:YZ;
      cbn; try discriminate; intros _ _; rewrite (comparison_trans CL _ _ _ XY YZ); reflexivity.
  - intro; rewrite (order_le_spec OS), (comparison_reflexive CL); reflexivity.
  - intros; rewrite !(order_le_spec OS) in *; eapply comparison_le_trans; eauto.
  - intros; rewrite !(order_le_spec OS) in *; eapply comparison_le_antisymmetric; eauto.
  - intros; rewrite !(order_le_spec OS); apply comparison_le_total; exact CL.
  - intros; rewrite (order_lt_spec OS), (order_le_spec OS), (comparison_swap CL (obs x) (obs y)).
    destruct (cmp (obs x) (obs y)); reflexivity.
  - intros; rewrite (order_gt_spec OS), (order_lt_spec OS); reflexivity.
  - intros; rewrite (order_ge_spec OS), (order_le_spec OS); reflexivity.
Qed.

Lemma observational_extrema_laws :
  (forall x y : T, GHC.Base.op_zlze__ x (GHC.Base.max x y)=true /\ GHC.Base.op_zlze__ y (GHC.Base.max x y)=true) /\
  (forall x y z : T, GHC.Base.op_zlze__ x z=true -> GHC.Base.op_zlze__ y z=true -> GHC.Base.op_zlze__ (GHC.Base.max x y) z=true) /\
  (forall x y : T, GHC.Base.op_zlze__ (GHC.Base.min x y) x=true /\ GHC.Base.op_zlze__ (GHC.Base.min x y) y=true) /\
  (forall x y z : T, GHC.Base.op_zlze__ z x=true -> GHC.Base.op_zlze__ z y=true -> GHC.Base.op_zlze__ z (GHC.Base.min x y)=true).
Proof.
  assert (Refl : forall x : T, GHC.Base.op_zlze__ x x=true).
  { intro; rewrite (order_le_spec OS), (comparison_reflexive CL); reflexivity. }
  assert (Rev : forall x y : T, GHC.Base.op_zlze__ x y=false -> GHC.Base.op_zlze__ y x=true).
  { intros x y; rewrite !(order_le_spec OS); rewrite (comparison_swap CL (obs x) (obs y));
      destruct (cmp (obs x) (obs y)); cbn; congruence. }
  repeat split; intros; rewrite ?(order_max_spec OS), ?(order_min_spec OS);
    destruct (GHC.Base.op_zlze__ x y) eqn:C; auto.
Qed.
End DerivedOrderLaws.

Lemma derived_order_spec {T O} `{GHC.Base.Ord T} (obs : T -> O) cmp (CL : ComparisonLaws cmp)
  (EQ : forall x y, GHC.Base.op_zeze__ x y=true <-> obs x=obs y)
  (NE : forall x y, GHC.Base.op_zsze__ x y=negb (GHC.Base.op_zeze__ x y))
  (CP : forall x y, GHC.Base.compare x y=cmp (obs x) (obs y))
  (LT : forall x y, GHC.Base.op_zl__ x y=comparisonLT (cmp (obs x) (obs y)))
  (LE : forall x y, GHC.Base.op_zlze__ x y=negb (GHC.Base.op_zl__ y x))
  (GT : forall x y, GHC.Base.op_zg__ x y=GHC.Base.op_zl__ y x)
  (GE : forall x y, GHC.Base.op_zgze__ x y=negb (GHC.Base.op_zl__ x y))
  (MX : forall x y, GHC.Base.max x y=if GHC.Base.op_zlze__ x y then y else x)
  (MN : forall x y, GHC.Base.min x y=if GHC.Base.op_zlze__ x y then x else y) : OrderSpec obs cmp.
Proof.
  constructor; auto.
  - intros; rewrite LE,LT,(comparison_swap CL (obs x) (obs y)); destruct (cmp (obs x) (obs y)); reflexivity.
  - intros; rewrite GT,LT; reflexivity.
  - intros; rewrite GE,LT,(comparison_swap CL (obs x) (obs y)); destruct (cmp (obs x) (obs y)); reflexivity.
Qed.

Section ConcreteOrders.
Context {K} `{GHC.Base.Ord K} (laws : EndpointOrderLaws).

Lemma endpoint_lt_compare x y : GHC.Base.op_zl__ x y=comparisonLT (GHC.Base.compare x y).
Proof.
  rewrite endpoint_lt,endpoint_compare by exact laws.
  destruct (GHC.Base.op_zlze__ x y) eqn:A, (GHC.Base.op_zlze__ y x) eqn:B; try reflexivity.
  destruct (endpoint_total laws x y); congruence.
Qed.
Lemma interval_order_spec : OrderSpec (fun i : IM.Interval K => i) GHC.Base.compare.
Proof.
  apply derived_order_spec; try apply interval_comparison_laws; try exact laws;
    try apply interval_equality_law; try exact laws; try apply interval_inequality; try reflexivity.
  - intros [x a] [y b]; change ((match GHC.Base.compare x y with
      | Lt => true | Eq => GHC.Base.op_zl__ a b | Gt => false end) =
      comparisonLT (match GHC.Base.compare x y with Eq => GHC.Base.compare a b | c => c end)).
    destruct (GHC.Base.compare x y); cbn; auto using endpoint_lt_compare.
Qed.

Section PayloadOrder.
Context {A} {EA : GHC.Base.Eq_ A} {OA : GHC.Base.Ord A}.
Context (PE : forall a b : A, GHC.Base.op_zeze__ a b=true <-> a=b)
  (PC : ComparisonLaws (@GHC.Base.compare A EA OA))
  (PL : forall a b : A, GHC.Base.op_zl__ a b=comparisonLT (GHC.Base.compare a b)).

Lemma full_entry_comparison_laws : ComparisonLaws (fun x y : IM.Interval K * A => GHC.Base.compare x y).
Proof.
  change (ComparisonLaws (lexCompare (fun x y : IM.Interval K => GHC.Base.compare x y) (@GHC.Base.compare A EA OA))).
  exact (lexCompare_laws (interval_comparison_laws laws) PC). Qed.
Lemma full_entry_list_comparison_laws : ComparisonLaws (fun x y : list (IM.Interval K * A) => GHC.Base.compare x y).
Proof.
  eapply comparison_laws_ext; [|exact (listCompare_laws full_entry_comparison_laws)].
  intro xs; induction xs as [|x xs IH]; intros [|y ys]; try reflexivity.
  change ((match GHC.Base.compare x y with Eq => listCompare (fun a b => GHC.Base.compare a b) xs ys | c => c end) =
    match GHC.Base.compare x y with Eq => GHC.Base.compare xs ys | c => c end).
  rewrite IH; reflexivity.
Qed.

Lemma node_comparison_laws : ComparisonLaws (fun x y : IM.Node K A => GHC.Base.compare x y).
Proof.
  constructor.
  - intros [i a] [j b]; rewrite node_compare_full, (comparison_eq full_entry_comparison_laws).
    cbn [fullEntry]; split; intro E; injection E; intros; subst; reflexivity.
  - intros x y; rewrite !node_compare_full; apply (comparison_swap full_entry_comparison_laws).
  - intros x y z; rewrite !node_compare_full; apply (comparison_trans full_entry_comparison_laws).
Qed.
Lemma node_order_spec : OrderSpec (fun n : IM.Node K A => n) GHC.Base.compare.
Proof.
  apply derived_order_spec; try exact node_comparison_laws; try apply (node_equality_law laws PE);
    try apply node_inequality; try reflexivity.
  intros [i a] [j b]; change ((match GHC.Base.compare i j with
    | Lt => true | Eq => GHC.Base.op_zl__ a b | Gt => false end) =
    comparisonLT (match GHC.Base.compare i j with Eq => GHC.Base.compare a b | c => c end)).
  destruct (GHC.Base.compare i j); cbn; auto using PL.
Qed.
Lemma map_order_spec : OrderSpec (@entries K A) GHC.Base.compare.
Proof.
  constructor.
  - apply (map_equality_law laws PE).
  - reflexivity.
  - apply compare_entries.
  - intros; change (GHC.Base.op_zeze__ (GHC.Base.compare x y) Lt = comparisonLT (GHC.Base.compare (entries x) (entries y))).
    rewrite compare_entries; destruct (GHC.Base.compare (entries x) (entries y)); reflexivity.
  - intros; change (GHC.Base.op_zsze__ (GHC.Base.compare x y) Gt = comparisonLE (GHC.Base.compare (entries x) (entries y))).
    rewrite compare_entries; destruct (GHC.Base.compare (entries x) (entries y)); reflexivity.
  - intros; change (GHC.Base.op_zeze__ (GHC.Base.compare x y) Gt = comparisonLT (GHC.Base.compare (entries y) (entries x))).
    rewrite compare_entries, (comparison_swap full_entry_list_comparison_laws (entries x) (entries y));
      destruct (GHC.Base.compare (entries x) (entries y)); reflexivity.
  - intros; change (GHC.Base.op_zsze__ (GHC.Base.compare x y) Lt = comparisonLE (GHC.Base.compare (entries y) (entries x))).
    rewrite compare_entries, (comparison_swap full_entry_list_comparison_laws (entries x) (entries y));
      destruct (GHC.Base.compare (entries x) (entries y)); reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition node_eq_laws := observational_eq_laws node_order_spec.
Definition node_ord_laws := observational_order_laws node_comparison_laws node_order_spec.
Definition node_minmax_laws := observational_extrema_laws node_comparison_laws node_order_spec.
Definition map_eq_laws := observational_eq_laws map_order_spec.
Definition map_ord_laws := observational_order_laws full_entry_list_comparison_laws map_order_spec.
Definition map_minmax_laws := observational_extrema_laws full_entry_list_comparison_laws map_order_spec.
End PayloadOrder.

Definition interval_eq_laws := observational_eq_laws interval_order_spec.
Definition interval_ord_laws := observational_order_laws (interval_comparison_laws laws) interval_order_spec.
Definition interval_minmax_laws := observational_extrema_laws (interval_comparison_laws laws) interval_order_spec.
End ConcreteOrders.

Section ApplicativeAlgebra.
Context {F : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F}.
Lemma fmap_liftA2 {A B C D} (h : C -> D) (k : A -> B -> C) x y :
  GHC.Base.fmap h (GHC.Base.liftA2 k x y)=GHC.Base.liftA2 (fun a b => h (k a b)) x y.
Proof. rewrite !applicative_liftA2, fmap_ap, functor_composition; reflexivity. Qed.
Lemma liftA2_fmap_left {A B C D} (k : B -> C -> D) (h : A -> B) x y :
  GHC.Base.liftA2 k (GHC.Base.fmap h x) y=GHC.Base.liftA2 (fun a c => k (h a) c) x y.
Proof. rewrite !applicative_liftA2, functor_composition; reflexivity. Qed.
Lemma liftA2_fmap_right {A B C D} (k : A -> C -> D) (h : B -> C) x y :
  GHC.Base.liftA2 k x (GHC.Base.fmap h y)=GHC.Base.liftA2 (fun a b => k a (h b)) x y.
Proof. rewrite !applicative_liftA2, ap_fmap_right_comp, functor_composition; reflexivity. Qed.
Lemma liftA2_associate {A B C D E X} (h : A -> B -> D) (k : D -> C -> E)
  (g : B -> C -> X) (f : A -> X -> E) x y z :
  (forall a b c, k (h a b) c=f a (g b c)) ->
  GHC.Base.liftA2 k (GHC.Base.liftA2 h x y) z=GHC.Base.liftA2 f x (GHC.Base.liftA2 g y z).
Proof.
  intro E0; rewrite !applicative_liftA2, <-applicative_composition, <-applicative_fmap.
  repeat first [rewrite fmap_ap|rewrite ap_fmap_right_comp|rewrite functor_composition].
  f_equal; f_equal; f_equal; apply functional_extensionality; intro a.
  apply functional_extensionality; intro b; apply functional_extensionality; intro c; apply E0.
Qed.
End ApplicativeAlgebra.

Section ComposeLaws.
Context {F G : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F} `{Proofs.GHC.Base.ApplicativeLaws G}.

Definition compose_functor_laws : Proofs.GHC.Base.FunctorLaws (Data.Functor.Compose.Compose F G).
Proof.
  constructor.
  - intros A [x]; change (Data.Functor.Compose.Mk_Compose (GHC.Base.fmap (GHC.Base.fmap (fun x : A => x)) x) = Data.Functor.Compose.Mk_Compose x).
    assert (E : @GHC.Base.fmap G Functor1 A A (fun x => x) = (fun x => x)).
    { apply functional_extensionality; apply functor_identity. }
    rewrite E, functor_identity; reflexivity.
  - intros A B C f g [x].
    change (Data.Functor.Compose.Mk_Compose (GHC.Base.fmap (GHC.Base.fmap g)
      (GHC.Base.fmap (GHC.Base.fmap f) x)) =
      Data.Functor.Compose.Mk_Compose (GHC.Base.fmap (GHC.Base.fmap (fun a => g (f a))) x)).
    rewrite functor_composition; f_equal; f_equal; apply functional_extensionality; intro y.
    apply functor_composition.
Defined.
#[local] Existing Instance compose_functor_laws.

Definition compose_applicative_laws : Proofs.GHC.Base.ApplicativeLaws (Data.Functor.Compose.Compose F G).
Proof.
  constructor.
  - intros A [x]; change (Data.Functor.Compose.Mk_Compose
      (GHC.Base.liftA2 GHC.Base.op_zlztzg__ (GHC.Base.pure (GHC.Base.pure (fun a : A => a))) x) = Data.Functor.Compose.Mk_Compose x).
    rewrite liftA2_pure_left; f_equal.
    replace (fun a : G A => GHC.Base.op_zlztzg__ (GHC.Base.pure (fun a : A => a)) a) with (fun a : G A => a)
      by (apply functional_extensionality; intro; symmetry; apply applicative_identity).
    apply functor_identity.
  - intros A B C [u] [v] [w].
    change (Data.Functor.Compose.Mk_Compose
      (GHC.Base.liftA2 GHC.Base.op_zlztzg__
        (GHC.Base.liftA2 GHC.Base.op_zlztzg__
          (GHC.Base.liftA2 GHC.Base.op_zlztzg__ (GHC.Base.pure (GHC.Base.pure GHC.Base.op_z2218U__)) u) v) w) =
      Data.Functor.Compose.Mk_Compose (GHC.Base.liftA2 GHC.Base.op_zlztzg__ u (GHC.Base.liftA2 GHC.Base.op_zlztzg__ v w))).
    rewrite liftA2_pure_left, liftA2_fmap_left; f_equal.
    apply liftA2_associate; intros; apply applicative_composition.
  - intros A B f x; change (@Data.Functor.Compose.Mk_Compose Type Type F G B
      (GHC.Base.liftA2 GHC.Base.op_zlztzg__ (GHC.Base.pure (GHC.Base.pure f)) (GHC.Base.pure (GHC.Base.pure x))) =
      @Data.Functor.Compose.Mk_Compose Type Type F G B (GHC.Base.pure (GHC.Base.pure (f x)))).
    rewrite liftA2_pure_left, fmap_pure, applicative_homomorphism; reflexivity.
  - intros A B [u] y; change (Data.Functor.Compose.Mk_Compose
      (GHC.Base.liftA2 GHC.Base.op_zlztzg__ u (GHC.Base.pure (GHC.Base.pure y))) =
      Data.Functor.Compose.Mk_Compose
      (GHC.Base.liftA2 GHC.Base.op_zlztzg__ (GHC.Base.pure (GHC.Base.pure (fun f => f y))) u)).
    rewrite liftA2_pure_right, liftA2_pure_left; f_equal; f_equal.
    apply functional_extensionality; intro; apply applicative_interchange.
  - intros A B C f [x] [y]; change (Data.Functor.Compose.Mk_Compose
      (GHC.Base.liftA2 (GHC.Base.liftA2 f) x y) = Data.Functor.Compose.Mk_Compose
      (GHC.Base.liftA2 GHC.Base.op_zlztzg__ (GHC.Base.fmap (GHC.Base.fmap f) x) y)).
    rewrite liftA2_fmap_left; f_equal; f_equal.
    apply functional_extensionality; intro a; apply functional_extensionality; intro b; apply applicative_liftA2.
  - intros A B f [x]; change (Data.Functor.Compose.Mk_Compose (GHC.Base.fmap (GHC.Base.fmap f) x) =
      Data.Functor.Compose.Mk_Compose (GHC.Base.liftA2 GHC.Base.op_zlztzg__ (GHC.Base.pure (GHC.Base.pure f)) x)).
    rewrite liftA2_pure_left; f_equal; f_equal; apply functional_extensionality; intro; apply applicative_fmap.
Defined.
End ComposeLaws.

Definition identity_functor_laws : Proofs.GHC.Base.FunctorLaws Data.Functor.Identity.Identity.
Proof. constructor; [intros A [x]|intros A B C f g [x]]; reflexivity. Defined.
#[local] Existing Instance identity_functor_laws.
Definition identity_applicative_laws : Proofs.GHC.Base.ApplicativeLaws Data.Functor.Identity.Identity.
Proof.
  constructor; [intros A [v]|intros A B C [u] [v] [w]|intros A B f x|
    intros A B [u] y|intros A B C f [x] [y]|intros A B f [x]]; reflexivity.
Defined.
#[local] Existing Instance identity_applicative_laws.

Record ApplicativeMorphism {F G : Type -> Type} `{GHC.Base.Applicative F} `{GHC.Base.Applicative G}
  (eta : forall A, F A -> G A) : Prop := {
  morphism_pure : forall A (x : A), eta A (GHC.Base.pure x)=GHC.Base.pure x;
  morphism_liftA2 : forall A B C (h : A -> B -> C) x y,
    eta C (GHC.Base.liftA2 h x y)=GHC.Base.liftA2 h (eta A x) (eta B y)
}.

Section Morphisms.
Context {F G : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F} `{Proofs.GHC.Base.ApplicativeLaws G}
  (eta : forall A, F A -> G A) (EM : ApplicativeMorphism eta).
Lemma morphism_fmap {A B} (h : A -> B) x :
  @eta B (GHC.Base.fmap h x)=GHC.Base.fmap h (@eta A x).
Proof.
  replace (GHC.Base.fmap h x) with
    (GHC.Base.liftA2 (fun a (_ : unit) => h a) x (GHC.Base.pure tt))
    by (rewrite liftA2_pure_right; reflexivity).
  rewrite (morphism_liftA2 EM), (morphism_pure EM), liftA2_pure_right; reflexivity.
Qed.
Lemma traverse_list_naturality {A B} (f : A -> F B) xs :
  @eta (list B) (traverse_list f xs)=traverse_list (fun a => @eta B (f a)) xs.
Proof.
  induction xs as [|x xs IH]; cbn [traverse_list];
    [apply (morphism_pure EM)|rewrite (morphism_liftA2 EM), IH; reflexivity].
Qed.
End Morphisms.

Section ListAlgebra.
Context {F : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F}.
Lemma traverse_list_input_map {A B C} (h : A -> B) (f : B -> F C) xs :
  traverse_list f (List.map h xs)=traverse_list (fun x => f (h x)) xs.
Proof. induction xs; cbn [List.map traverse_list]; congruence. Qed.
Lemma traverse_list_output_map {A B C} (f : A -> F B) (h : B -> C) xs :
  GHC.Base.fmap (List.map h) (traverse_list f xs)=traverse_list (fun a => GHC.Base.fmap h (f a)) xs.
Proof.
  induction xs as [|x xs IH]; cbn [traverse_list]; [rewrite fmap_pure; reflexivity|].
  rewrite fmap_liftA2, liftA2_fmap_left, <-IH, liftA2_fmap_right; reflexivity.
Qed.
End ListAlgebra.

Section ComposeBehavior.
Context {F G : Type -> Type} {FF : GHC.Base.Functor F} {FA : GHC.Base.Applicative F}
  {GF : GHC.Base.Functor G} {GA : GHC.Base.Applicative G}.
Lemma compose_get_pure {A} (a : A) :
  Data.Functor.Compose.getCompose (@GHC.Base.pure (Data.Functor.Compose.Compose F G)
    (@Data.Functor.Compose.Functor__Compose F G FF GF)
    (@Data.Functor.Compose.Applicative__Compose F G FF FA GF GA) A a)=
    @GHC.Base.pure F FF FA (G A) (@GHC.Base.pure G GF GA A a).
Proof. reflexivity. Qed.
Lemma compose_get_fmap {A B} (h : A -> B) (x : Data.Functor.Compose.Compose F G A) :
  Data.Functor.Compose.getCompose (GHC.Base.fmap h x)=GHC.Base.fmap (GHC.Base.fmap h) (Data.Functor.Compose.getCompose x).
Proof. destruct x; reflexivity. Qed.
Lemma compose_get_liftA2 {A B C} (h : A -> B -> C)
  (x : Data.Functor.Compose.Compose F G A) (y : Data.Functor.Compose.Compose F G B) :
  Data.Functor.Compose.getCompose (@GHC.Base.liftA2 (Data.Functor.Compose.Compose F G)
    (@Data.Functor.Compose.Functor__Compose F G FF GF)
    (@Data.Functor.Compose.Applicative__Compose F G FF FA GF GA) A B C h x y)=
    @GHC.Base.liftA2 F FF FA (G A) (G B) (G C) (@GHC.Base.liftA2 G GF GA A B C h)
      (Data.Functor.Compose.getCompose x) (Data.Functor.Compose.getCompose y).
Proof. destruct x,y; reflexivity. Qed.
End ComposeBehavior.

Section ListComposition.
Context {F G : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F} `{Proofs.GHC.Base.ApplicativeLaws G}.
Lemma traverse_list_composition {A B C} (f : A -> F B) (g : B -> G C) xs :
  Data.Functor.Compose.getCompose
    (traverse_list (fun a => @Data.Functor.Compose.Mk_Compose Type Type F G C (GHC.Base.fmap g (f a))) xs) =
    GHC.Base.fmap (traverse_list g) (traverse_list f xs).
Proof.
  induction xs as [|x xs IH]; cbn [traverse_list].
  - rewrite fmap_pure; reflexivity.
  - rewrite compose_get_liftA2, IH, fmap_liftA2.
    cbn [Data.Functor.Compose.getCompose].
    rewrite liftA2_fmap_left, liftA2_fmap_right; reflexivity.
Qed.
End ListComposition.

Lemma traverse_list_identity {A} (xs : list A) :
  traverse_list Data.Functor.Identity.Mk_Identity xs=Data.Functor.Identity.Mk_Identity xs.
Proof. induction xs; cbn [traverse_list]; [reflexivity|rewrite IHxs; reflexivity]. Qed.

Definition entryEffect {K F} `{GHC.Base.Functor F} {A B} (f : A -> F B) (e : IM.Interval K * A) : F ((IM.Interval K * B)%type) :=
  GHC.Base.fmap (fun b => (fst e,b)) (f (snd e)).

#[local] Existing Instance compose_functor_laws.
#[local] Existing Instance compose_applicative_laws.

Section TraversalReference.
Context {F : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F}.
Lemma map_traverse_reference {K A B} (f : A -> F B) (m : IM.IntervalMap K A) :
  GHC.Base.fmap entries (Data.Traversable.traverse f m)=traverse_list (entryEffect f) (entries m).
Proof. apply traverse_entries. Qed.
End TraversalReference.

Lemma node_traversal_identity {K A} (n : IM.Node K A) :
  Data.Traversable.traverse Data.Functor.Identity.Mk_Identity n=Data.Functor.Identity.Mk_Identity n.
Proof. destruct n; reflexivity. Qed.
Lemma map_traversal_identity {K A} (m : IM.IntervalMap K A) :
  GHC.Base.fmap entries (Data.Traversable.traverse Data.Functor.Identity.Mk_Identity m)=
    Data.Functor.Identity.Mk_Identity (entries m).
Proof.
  rewrite map_traverse_reference.
  assert (E : @entryEffect K Data.Functor.Identity.Identity _ A A Data.Functor.Identity.Mk_Identity =
    Data.Functor.Identity.Mk_Identity).
  { apply functional_extensionality; intros [i a]; reflexivity. }
  rewrite E; apply traverse_list_identity.
Qed.

Section TraversalNaturality.
Context {F G : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F} `{Proofs.GHC.Base.ApplicativeLaws G}
  (eta : forall A, F A -> G A) (EM : ApplicativeMorphism eta).

Lemma node_traversal_naturality {K A B} (f : A -> F B) (n : IM.Node K A) :
  @eta (IM.Node K B) (Data.Traversable.traverse f n)=
    Data.Traversable.traverse (fun a => @eta B (f a)) n.
Proof. destruct n as [i a]; apply (morphism_fmap EM). Qed.

Lemma map_traversal_naturality {K A B} (f : A -> F B) (m : IM.IntervalMap K A) :
  GHC.Base.fmap entries (@eta (IM.IntervalMap K B) (Data.Traversable.traverse f m))=
    GHC.Base.fmap entries (Data.Traversable.traverse (fun a => @eta B (f a)) m).
Proof.
  rewrite <- (morphism_fmap EM), !map_traverse_reference, (traverse_list_naturality EM).
  f_equal; apply functional_extensionality; intro e.
  unfold entryEffect; apply morphism_fmap; exact EM.
Qed.
End TraversalNaturality.

Section TraversalComposition.
Context {F G : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F} `{Proofs.GHC.Base.ApplicativeLaws G}.

Lemma entryEffect_composition {K A B C} (f : A -> F B) (g : B -> G C) e :
  entryEffect (fun a => @Data.Functor.Compose.Mk_Compose Type Type F G C (GHC.Base.fmap g (f a))) e =
    @Data.Functor.Compose.Mk_Compose Type Type F G ((IM.Interval K * C)%type)
      (GHC.Base.fmap (entryEffect g) (entryEffect f e)).
Proof.
  destruct e as [i a]; change (Data.Functor.Compose.Mk_Compose
    (GHC.Base.fmap (GHC.Base.fmap (fun c => (i,c))) (GHC.Base.fmap g (f a))) =
    Data.Functor.Compose.Mk_Compose (GHC.Base.fmap (entryEffect g) (GHC.Base.fmap (fun b => (i,b)) (f a)))).
  rewrite !functor_composition; reflexivity.
Qed.

Lemma node_traversal_composition {K A B C} (f : A -> F B) (g : B -> G C) (n : IM.Node K A) :
  Data.Functor.Compose.getCompose
    (Data.Traversable.traverse (fun a => @Data.Functor.Compose.Mk_Compose Type Type F G C (GHC.Base.fmap g (f a))) n)=
    GHC.Base.fmap (Data.Traversable.traverse g) (Data.Traversable.traverse f n).
Proof.
  destruct n as [i a]; change (GHC.Base.fmap (GHC.Base.fmap (IM.MkNode i)) (GHC.Base.fmap g (f a)) =
    GHC.Base.fmap (Data.Traversable.traverse g) (GHC.Base.fmap (IM.MkNode i) (f a))).
  rewrite !functor_composition; reflexivity.
Qed.

Lemma map_traversal_composition {K A B C} (f : A -> F B) (g : B -> G C) (m : IM.IntervalMap K A) :
  Data.Functor.Compose.getCompose
    (GHC.Base.fmap entries (Data.Traversable.traverse
      (fun a => @Data.Functor.Compose.Mk_Compose Type Type F G C (GHC.Base.fmap g (f a))) m)) =
    GHC.Base.fmap (fun n => GHC.Base.fmap entries (Data.Traversable.traverse g n)) (Data.Traversable.traverse f m).
Proof.
  rewrite map_traverse_reference.
  assert (E : (fun n : IM.IntervalMap K B => GHC.Base.fmap entries (Data.Traversable.traverse g n)) =
    (fun n => traverse_list (entryEffect g) (entries n))).
  { apply functional_extensionality; intro; apply map_traverse_reference. }
  rewrite E.
  replace (GHC.Base.fmap (fun n => traverse_list (entryEffect g) (entries n)) (Data.Traversable.traverse f m)) with
    (GHC.Base.fmap (traverse_list (entryEffect g)) (GHC.Base.fmap entries (Data.Traversable.traverse f m)))
    by (apply functor_composition).
  rewrite map_traverse_reference, <-traverse_list_composition.
  f_equal; f_equal; apply functional_extensionality; intro e; apply entryEffect_composition.
Qed.
End TraversalComposition.

Section NodeEffectValidity.
Context {F : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F}.
Lemma node_traversal_holds {K A B} (P : B -> Prop) (f : A -> F B) i a :
  HoldsF P (f a) -> HoldsF (fun n : IM.Node K B =>
    fst (fullEntry n)=i /\ P (snd (fullEntry n))) (Data.Traversable.traverse f (IM.MkNode i a)).
Proof.
  intro V; change (HoldsF (fun n : IM.Node K B => fst (fullEntry n)=i /\ P (snd (fullEntry n)))
    (GHC.Base.fmap (IM.MkNode i) (f a))).
  apply (HoldsF_fmap P); [intros b Pb; split; [reflexivity|exact Pb]|exact V].
Qed.
End NodeEffectValidity.

(* Complete typed interface and transitive assumption inventory. *)
Check @opposite. Print Assumptions opposite.
Check @ComparisonLaws. Print Assumptions ComparisonLaws.
Check @Build_ComparisonLaws. Print Assumptions Build_ComparisonLaws.
Check @comparison_eq. Print Assumptions comparison_eq.
Check @comparison_swap. Print Assumptions comparison_swap.
Check @comparison_trans. Print Assumptions comparison_trans.
Check @comparison_laws_ext. Print Assumptions comparison_laws_ext.
Check @lexCompare. Print Assumptions lexCompare.
Check @lexCompare_laws. Print Assumptions lexCompare_laws.
Check @listCompare. Print Assumptions listCompare.
Check @listCompare_laws. Print Assumptions listCompare_laws.
Check @endpoint_comparison_laws. Print Assumptions endpoint_comparison_laws.
Check @interval_comparison_laws. Print Assumptions interval_comparison_laws.
Check @comparisonLE. Print Assumptions comparisonLE.
Check @comparisonLT. Print Assumptions comparisonLT.
Check @bool_equiv. Print Assumptions bool_equiv.
Check @comparison_reflexive. Print Assumptions comparison_reflexive.
Check @comparison_le_total. Print Assumptions comparison_le_total.
Check @comparison_le_trans. Print Assumptions comparison_le_trans.
Check @comparison_le_antisymmetric. Print Assumptions comparison_le_antisymmetric.
Check @OrderSpec. Print Assumptions OrderSpec.
Check @Build_OrderSpec. Print Assumptions Build_OrderSpec.
Check @order_eq_spec. Print Assumptions order_eq_spec.
Check @order_ne_spec. Print Assumptions order_ne_spec.
Check @order_compare_spec. Print Assumptions order_compare_spec.
Check @order_lt_spec. Print Assumptions order_lt_spec.
Check @order_le_spec. Print Assumptions order_le_spec.
Check @order_gt_spec. Print Assumptions order_gt_spec.
Check @order_ge_spec. Print Assumptions order_ge_spec.
Check @order_max_spec. Print Assumptions order_max_spec.
Check @order_min_spec. Print Assumptions order_min_spec.
Check @observational_eq_laws. Print Assumptions observational_eq_laws.
Check @observational_order_laws. Print Assumptions observational_order_laws.
Check @observational_extrema_laws. Print Assumptions observational_extrema_laws.
Check @derived_order_spec. Print Assumptions derived_order_spec.
Check @endpoint_lt_compare. Print Assumptions endpoint_lt_compare.
Check @interval_order_spec. Print Assumptions interval_order_spec.
Check @full_entry_comparison_laws. Print Assumptions full_entry_comparison_laws.
Check @full_entry_list_comparison_laws. Print Assumptions full_entry_list_comparison_laws.
Check @node_comparison_laws. Print Assumptions node_comparison_laws.
Check @node_order_spec. Print Assumptions node_order_spec.
Check @map_order_spec. Print Assumptions map_order_spec.
Check @node_eq_laws. Print Assumptions node_eq_laws.
Check @node_ord_laws. Print Assumptions node_ord_laws.
Check @node_minmax_laws. Print Assumptions node_minmax_laws.
Check @map_eq_laws. Print Assumptions map_eq_laws.
Check @map_ord_laws. Print Assumptions map_ord_laws.
Check @map_minmax_laws. Print Assumptions map_minmax_laws.
Check @interval_eq_laws. Print Assumptions interval_eq_laws.
Check @interval_ord_laws. Print Assumptions interval_ord_laws.
Check @interval_minmax_laws. Print Assumptions interval_minmax_laws.
Check @fmap_liftA2. Print Assumptions fmap_liftA2.
Check @liftA2_fmap_left. Print Assumptions liftA2_fmap_left.
Check @liftA2_fmap_right. Print Assumptions liftA2_fmap_right.
Check @liftA2_associate. Print Assumptions liftA2_associate.
Check @compose_functor_laws. Print Assumptions compose_functor_laws.
Check @compose_applicative_laws. Print Assumptions compose_applicative_laws.
Check @identity_functor_laws. Print Assumptions identity_functor_laws.
Check @identity_applicative_laws. Print Assumptions identity_applicative_laws.
Check @ApplicativeMorphism. Print Assumptions ApplicativeMorphism.
Check @Build_ApplicativeMorphism. Print Assumptions Build_ApplicativeMorphism.
Check @morphism_pure. Print Assumptions morphism_pure.
Check @morphism_liftA2. Print Assumptions morphism_liftA2.
Check @morphism_fmap. Print Assumptions morphism_fmap.
Check @traverse_list_naturality. Print Assumptions traverse_list_naturality.
Check @traverse_list_input_map. Print Assumptions traverse_list_input_map.
Check @traverse_list_output_map. Print Assumptions traverse_list_output_map.
Check @compose_get_pure. Print Assumptions compose_get_pure.
Check @compose_get_fmap. Print Assumptions compose_get_fmap.
Check @compose_get_liftA2. Print Assumptions compose_get_liftA2.
Check @traverse_list_composition. Print Assumptions traverse_list_composition.
Check @traverse_list_identity. Print Assumptions traverse_list_identity.
Check @entryEffect. Print Assumptions entryEffect.
Check @map_traverse_reference. Print Assumptions map_traverse_reference.
Check @node_traversal_identity. Print Assumptions node_traversal_identity.
Check @map_traversal_identity. Print Assumptions map_traversal_identity.
Check @node_traversal_naturality. Print Assumptions node_traversal_naturality.
Check @map_traversal_naturality. Print Assumptions map_traversal_naturality.
Check @entryEffect_composition. Print Assumptions entryEffect_composition.
Check @node_traversal_composition. Print Assumptions node_traversal_composition.
Check @map_traversal_composition. Print Assumptions map_traversal_composition.
Check @node_traversal_holds. Print Assumptions node_traversal_holds.
