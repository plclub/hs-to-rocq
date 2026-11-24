From Stdlib Require Import Lists.List Bool.Bool Sorting.Permutation Sorting.Sorted.
Require Import Data.PriorityQueue.FingerTree.
Import ListNotations.
Set Implicit Arguments.

Module Queue := Data.PriorityQueue.FingerTree.

(* These are propositional laws of the EXISTING translated dictionary, not a
   replacement dictionary. A total preorder suffices, even when equivalent
   priorities are not propositionally equal. Payloads need neither Eq nor Default. *)
Section Order.
Context {K : Type} `{GHC.Base.Ord K}.
Local Abbreviation leq := GHC.Base.op_zlze__.

Record PriorityOrderLaws : Prop := {
  priority_le_refl : forall x : K, leq x x = true;
  priority_le_trans : forall x y z : K,
    leq x y = true -> leq y z = true -> leq x z = true;
  priority_le_total : forall x y : K, leq x y = true \/ leq y x = true
}.

(* Optional stronger coherence, not required by the summary or stable model. *)
Definition PriorityEqualityCoherence : Prop :=
  forall x y : K, (leq x y = true /\ leq y x = true) <-> x = y.

Context (laws : PriorityOrderLaws).

Lemma priority_reverse_of_false (x y : K) :
  leq x y = false -> leq y x = true.
Proof.
  intro E. destruct (priority_le_total laws x y); [congruence | assumption].
Qed.

Section Summary.
Context {V : Type}.

Lemma unionPrio_left_identity (p : Queue.Prio K V) :
  Queue.unionPrio Queue.NoPrio p = p.
Proof. destruct p; reflexivity. Qed.

Lemma unionPrio_right_identity (p : Queue.Prio K V) :
  Queue.unionPrio p Queue.NoPrio = p.
Proof. destruct p; reflexivity. Qed.

Lemma unionPrio_associative (p q r : Queue.Prio K V) :
  Queue.unionPrio p (Queue.unionPrio q r) =
  Queue.unionPrio (Queue.unionPrio p q) r.
Proof.
  destruct p as [|a u]; [rewrite !unionPrio_left_identity; reflexivity |].
  destruct q as [|b v];
    [rewrite unionPrio_left_identity, unionPrio_right_identity; reflexivity |].
  destruct r as [|c w]; [rewrite !unionPrio_right_identity; reflexivity |].
  cbn [Queue.unionPrio].
  destruct (leq a b) eqn:Hab; destruct (leq b c) eqn:Hbc;
    destruct (leq a c) eqn:Hac; cbn [Queue.unionPrio];
    rewrite ?Hab, ?Hbc, ?Hac; try reflexivity.
  - pose proof (priority_le_trans laws Hab Hbc). congruence.
  - pose proof (priority_reverse_of_false Hbc) as Hcb.
    pose proof (priority_le_trans laws Hac Hcb). congruence.
Qed.

Lemma unionPrio_left_winner (k k' : K) (v v' : V) :
  leq k k' = true ->
  Queue.unionPrio (Queue.MkPrio k v) (Queue.MkPrio k' v') = Queue.MkPrio k v.
Proof. intro E. cbn [Queue.unionPrio]. rewrite E. reflexivity. Qed.

Lemma unionPrio_right_winner (k k' : K) (v v' : V) :
  leq k k' = false ->
  Queue.unionPrio (Queue.MkPrio k v) (Queue.MkPrio k' v') = Queue.MkPrio k' v'.
Proof. intro E. cbn [Queue.unionPrio]. rewrite E. reflexivity. Qed.

Lemma prio_semigroup_behavior (p q : Queue.Prio K V) :
  GHC.Base.op_zlzlzgzg__ p q = Queue.unionPrio p q.
Proof. reflexivity. Qed.

Lemma prio_monoid_append_behavior (p q : Queue.Prio K V) :
  GHC.Base.mappend p q = Queue.unionPrio p q.
Proof. reflexivity. Qed.

Lemma prio_monoid_empty_behavior :
  (GHC.Base.mempty : Queue.Prio K V) = Queue.NoPrio.
Proof. reflexivity. Qed.

Lemma prio_monoid_concat_behavior (ps : list (Queue.Prio K V)) :
  GHC.Base.mconcat ps = fold_right Queue.unionPrio Queue.NoPrio ps.
Proof. reflexivity. Qed.

Lemma prio_monoid_propositional_laws :
  (forall p q r : Queue.Prio K V,
    GHC.Base.mappend p (GHC.Base.mappend q r) =
    GHC.Base.mappend (GHC.Base.mappend p q) r) /\
  (forall p : Queue.Prio K V, GHC.Base.mappend GHC.Base.mempty p = p) /\
  (forall p : Queue.Prio K V, GHC.Base.mappend p GHC.Base.mempty = p).
Proof.
  split; [apply unionPrio_associative |].
  split; [apply unionPrio_left_identity | apply unionPrio_right_identity].
Qed.

Lemma entry_measure_behavior (k : K) (v : V) :
  Data.FingerTree.measure (Queue.MkEntry k v) = Queue.MkPrio k v.
Proof. reflexivity. Qed.

Definition entry_summary (e : K * V) : Queue.Prio K V :=
  Queue.MkPrio (fst e) (snd e).

Definition summary (xs : list (K * V)) : Queue.Prio K V :=
  fold_right (fun e p => Queue.unionPrio (entry_summary e) p) Queue.NoPrio xs.

Lemma summary_nil : summary [] = Queue.NoPrio.
Proof. reflexivity. Qed.

Lemma summary_cons (e : K * V) xs :
  summary (e :: xs) = Queue.unionPrio (entry_summary e) (summary xs).
Proof. reflexivity. Qed.

Lemma summary_app xs ys :
  summary (xs ++ ys) = Queue.unionPrio (summary xs) (summary ys).
Proof.
  induction xs as [|e xs IH]; cbn [app].
  - symmetry. apply unionPrio_left_identity.
  - rewrite !summary_cons, IH. apply unionPrio_associative.
Qed.

Lemma summary_empty_iff xs : summary xs = Queue.NoPrio <-> xs = [].
Proof.
  destruct xs as [|[k v] xs]; [split; reflexivity |].
  rewrite summary_cons. cbn [entry_summary fst snd].
  destruct (summary xs) as [|k' v']; cbn [Queue.unionPrio entry_summary fst snd];
    try destruct (leq k k'); split; discriminate.
Qed.

Lemma summary_minimum xs k v :
  summary xs = Queue.MkPrio k v ->
  In (k, v) xs /\ Forall (fun e => leq k (fst e) = true) xs.
Proof.
  revert k v. induction xs as [|[a u] xs IH]; intros k v; [discriminate |].
  rewrite summary_cons. cbn [entry_summary].
  destruct (summary xs) as [|b w] eqn:Es.
  - intro E. cbn [Queue.unionPrio entry_summary fst snd] in E. inversion E; subst.
    apply summary_empty_iff in Es. subst. split; [left; reflexivity |].
    constructor; [apply priority_le_refl; exact laws | constructor].
  - specialize (IH b w eq_refl).
    destruct IH as [Hin Hall]. cbn [Queue.unionPrio entry_summary fst snd].
    destruct (leq a b) eqn:Eab; intro E; inversion E; subst.
    + split; [left; reflexivity |]. constructor.
      * apply priority_le_refl; exact laws.
      * eapply Forall_impl; [|exact Hall].
        intros [c z] Hc. eapply priority_le_trans; eauto.
    + split; [right; exact Hin |]. constructor; [|exact Hall].
      apply priority_reverse_of_false. exact Eab.
Qed.

(* The selected full entry is the FIRST minimum in raw sequence order. *)
Lemma summary_first_minimum xs k v :
  summary xs = Queue.MkPrio k v ->
  exists pre post,
    xs = pre ++ (k, v) :: post /\
    Forall (fun e => leq (fst e) k = false) pre /\
    Forall (fun e => leq k (fst e) = true) (pre ++ post).
Proof.
  revert k v. induction xs as [|[a u] xs IH]; intros k v; [discriminate |].
  rewrite summary_cons. cbn [entry_summary].
  destruct (summary xs) as [|b w] eqn:Es.
  - intro E. cbn [Queue.unionPrio entry_summary fst snd] in E. inversion E; subst.
    apply summary_empty_iff in Es. subst. exists [], []. repeat split; constructor.
  - cbn [Queue.unionPrio entry_summary fst snd]. destruct (leq a b) eqn:Eab; intro E;
      inversion E; subst.
    + exists [], xs. split; [reflexivity |]. split; [constructor |].
      destruct (summary_minimum xs Es) as [_ Hall].
      eapply Forall_impl; [|exact Hall]. intros [c z] Hc.
      eapply priority_le_trans; eauto.
    + destruct (IH _ _ eq_refl) as [pre [post [Heq [Hpre Hall]]]].
      exists ((a,u) :: pre), post. split; [cbn; now rewrite Heq |].
      split; constructor; try assumption.
      apply priority_reverse_of_false. exact Eab.
Qed.

Lemma below_unionPrio (k : K) (p q : Queue.Prio K V) :
  Queue.below k (Queue.unionPrio p q) = orb (Queue.below k p) (Queue.below k q).
Proof.
  destruct p as [|a u], q as [|b v]; cbn [Queue.unionPrio Queue.below];
    try now rewrite ?orb_false_r.
  destruct (leq a b) eqn:Eab; cbn [Queue.below];
    destruct (leq a k) eqn:Eak; destruct (leq b k) eqn:Ebk;
    try reflexivity.
  - pose proof (priority_le_trans laws Eab Ebk). congruence.
  - pose proof (priority_reverse_of_false Eab) as Eba.
    pose proof (priority_le_trans laws Eba Eak). congruence.
Qed.

Lemma below_summary k xs :
  Queue.below k (summary xs) = existsb (fun e => leq (fst e) k) xs.
Proof.
  induction xs as [|[a u] xs IH]; [reflexivity |].
  rewrite summary_cons, below_unionPrio, IH.
  reflexivity.
Qed.

Lemma below_summary_app k xs ys :
  Queue.below k (summary (xs ++ ys)) =
  orb (Queue.below k (summary xs)) (Queue.below k (summary ys)).
Proof. rewrite summary_app, below_unionPrio. reflexivity. Qed.

Lemma below_summary_monotone k xs ys :
  Queue.below k (summary xs) = true -> Queue.below k (summary (xs ++ ys)) = true.
Proof. intro E. rewrite below_summary_app, E. reflexivity. Qed.

Lemma below_summary_first_winner xs k v :
  summary xs = Queue.MkPrio k v ->
  exists pre post,
    xs = pre ++ (k,v) :: post /\
    Queue.below k (summary pre) = false /\
    Queue.below k (summary (pre ++ [(k,v)])) = true.
Proof.
  intro E. destruct (summary_first_minimum xs E)
    as [pre [post [Heq [Hpre Hrest]]]].
  exists pre, post. split; [exact Heq |].
  assert (Queue.below k (summary pre) = false) as Hfalse.
  { rewrite below_summary. clear Heq Hrest E.
    induction Hpre as [|e pre He Hpre IH]; cbn [existsb]; [reflexivity |].
    rewrite He, IH. reflexivity. }
  split; [exact Hfalse |]. rewrite below_summary_app, Hfalse.
  cbn [summary fold_right Queue.unionPrio Queue.below entry_summary fst snd].
  apply priority_le_refl; exact laws.
Qed.

End Summary.

Section StableModel.
Context {V : Type}.

Definition entry_le (a b : K * V) : Prop := leq (fst a) (fst b) = true.

Definition tied (k : K) (e : K * V) : bool :=
  andb (leq k (fst e)) (leq (fst e) k).

Fixpoint insert_before (e : K * V) (xs : list (K * V)) : list (K * V) :=
  match xs with
  | [] => [e]
  | h :: t => if leq (fst e) (fst h) then e :: xs else h :: insert_before e t
  end.

(* Stable insertion sort of FULL entries, entirely independent of the source
   queue's folds, extraction, and assocs. No raw-tree sortedness is assumed. *)
Definition ordered (xs : list (K * V)) : list (K * V) :=
  fold_right insert_before [] xs.

Definition stable_merge (xs ys : list (K * V)) : list (K * V) :=
  fold_right insert_before ys xs.

Lemma insert_before_permutation e xs : Permutation (e :: xs) (insert_before e xs).
Proof.
  induction xs as [|h t IH]; cbn [insert_before]; [reflexivity |].
  destruct (leq (fst e) (fst h)); [reflexivity |].
  eapply Permutation_trans; [apply perm_swap | now apply perm_skip].
Qed.

Lemma insert_before_forall (P : K * V -> Prop) e xs :
  P e -> Forall P xs -> Forall P (insert_before e xs).
Proof.
  intros He Hxs. induction Hxs; cbn [insert_before]; [now constructor |].
  destruct (leq (fst e) (fst x)); repeat constructor; assumption.
Qed.

Lemma insert_before_sorted e xs :
  StronglySorted entry_le xs -> StronglySorted entry_le (insert_before e xs).
Proof.
  intro Hs. induction Hs as [|h t Hs IH Hall]; cbn [insert_before].
  - constructor; constructor.
  - destruct (leq (fst e) (fst h)) eqn:E.
    + constructor; [now constructor |]. constructor; [exact E |].
      eapply Forall_impl; [|exact Hall]. intros x Hx.
      unfold entry_le in *. eapply priority_le_trans; eauto.
    + constructor; [exact IH |]. apply insert_before_forall; [|exact Hall].
      unfold entry_le. now apply priority_reverse_of_false.
Qed.

Lemma ordered_permutation xs : Permutation xs (ordered xs).
Proof.
  induction xs as [|e xs IH]; cbn [ordered fold_right]; [reflexivity |].
  eapply Permutation_trans; [apply perm_skip; exact IH |].
  apply insert_before_permutation.
Qed.

Lemma ordered_sorted xs : StronglySorted entry_le (ordered xs).
Proof.
  induction xs as [|e xs IH]; cbn [ordered fold_right];
    [constructor | now apply insert_before_sorted].
Qed.

Lemma ordered_cons e xs : ordered (e :: xs) = insert_before e (ordered xs).
Proof. reflexivity. Qed.

Lemma ordered_sorted_identity xs : StronglySorted entry_le xs -> ordered xs = xs.
Proof.
  intro Hs. induction Hs as [|h t Hs IH Hall]; [reflexivity |].
  rewrite ordered_cons, IH. destruct t as [|h' t']; [reflexivity |].
  inversion Hall as [|? ? Hhead Htail]; subst.
  cbn [insert_before]. unfold entry_le in *. now rewrite Hhead.
Qed.

Lemma ordered_idempotent xs : ordered (ordered xs) = ordered xs.
Proof. apply ordered_sorted_identity, ordered_sorted. Qed.

Lemma insert_before_ties k e xs :
  filter (tied k) (insert_before e xs) =
  if tied k e then e :: filter (tied k) xs else filter (tied k) xs.
Proof.
  induction xs as [|h t IH]; cbn [insert_before filter]; [now destruct (tied k e) |].
  destruct (leq (fst e) (fst h)) eqn:E; cbn [filter].
  - now destruct (tied k e).
  - rewrite IH. destruct (tied k e) eqn:Te; destruct (tied k h) eqn:Th;
      try reflexivity.
    unfold tied in Te, Th. apply andb_true_iff in Te, Th.
    destruct Te as [Tke Tek], Th as [Tkh Thk].
    pose proof (priority_le_trans laws Tek Tkh). congruence.
Qed.

Lemma ordered_ties k xs : filter (tied k) (ordered xs) = filter (tied k) xs.
Proof.
  induction xs as [|e xs IH]; [reflexivity |].
  rewrite ordered_cons, insert_before_ties, IH.
  cbn [filter]. now destruct (tied k e).
Qed.

Lemma ordered_app xs ys : ordered (xs ++ ys) = stable_merge xs (ordered ys).
Proof.
  induction xs as [|e xs IH]; [reflexivity |].
  cbn [app]. rewrite ordered_cons, IH. reflexivity.
Qed.

Lemma stable_merge_permutation xs ys : Permutation (xs ++ ys) (stable_merge xs ys).
Proof.
  induction xs as [|e xs IH]; [reflexivity |].
  cbn [app stable_merge fold_right].
  eapply Permutation_trans; [apply perm_skip; exact IH |].
  apply insert_before_permutation.
Qed.

Lemma stable_merge_sorted xs ys :
  StronglySorted entry_le ys -> StronglySorted entry_le (stable_merge xs ys).
Proof.
  intro Hs. induction xs as [|e xs IH]; cbn [stable_merge fold_right];
    [exact Hs | now apply insert_before_sorted].
Qed.

Lemma stable_merge_ties k xs ys :
  filter (tied k) (stable_merge xs ys) = filter (tied k) xs ++ filter (tied k) ys.
Proof.
  induction xs as [|e xs IH]; [reflexivity |].
  change (filter (tied k) (insert_before e (stable_merge xs ys)) =
    filter (tied k) (e :: xs) ++ filter (tied k) ys).
  rewrite insert_before_ties, IH. cbn [filter]. now destruct (tied k e).
Qed.

Lemma ordered_add_ties k xs e :
  filter (tied k) (ordered (xs ++ [e])) =
  filter (tied k) xs ++ if tied k e then [e] else [].
Proof. rewrite ordered_ties, filter_app. cbn. now destruct (tied k e). Qed.

Lemma ordered_insert_ties k xs e :
  filter (tied k) (ordered (e :: xs)) =
  if tied k e then e :: filter (tied k) xs else filter (tied k) xs.
Proof. rewrite ordered_ties. reflexivity. Qed.

Lemma ordered_union_ties k xs ys :
  filter (tied k) (ordered (xs ++ ys)) = filter (tied k) xs ++ filter (tied k) ys.
Proof. rewrite ordered_ties, filter_app. reflexivity. Qed.

Lemma summary_dominated k v xs :
  Forall (fun e : K * V => leq k (fst e) = true) xs ->
  Queue.unionPrio (Queue.MkPrio k v) (summary xs) = Queue.MkPrio k v.
Proof.
  intro Hall. induction Hall as [|[a u] xs Ha Hall IH].
  - reflexivity.
  - rewrite summary_cons, unionPrio_associative by exact laws.
    cbn [entry_summary fst snd Queue.unionPrio]. cbn in Ha. rewrite Ha. exact IH.
Qed.

Lemma summary_sorted_head e xs :
  StronglySorted entry_le (e :: xs) -> summary (e :: xs) = entry_summary e.
Proof.
  intro Hs. inversion Hs; subst. destruct e as [k v].
  rewrite summary_cons. apply summary_dominated. assumption.
Qed.

Lemma unionPrio_exchange_strict a u b v (p : Queue.Prio K V) :
  leq a b = false ->
  Queue.unionPrio (Queue.MkPrio a u) (Queue.unionPrio (Queue.MkPrio b v) p) =
  Queue.unionPrio (Queue.MkPrio b v) (Queue.unionPrio (Queue.MkPrio a u) p).
Proof.
  intro E. rewrite !unionPrio_associative by exact laws.
  rewrite unionPrio_right_winner by exact E.
  rewrite unionPrio_left_winner by (now apply priority_reverse_of_false).
  reflexivity.
Qed.

Lemma summary_insert_before e xs :
  summary (insert_before e xs) = Queue.unionPrio (entry_summary e) (summary xs).
Proof.
  induction xs as [|h xs IH]; cbn [insert_before]; [reflexivity |].
  destruct (leq (fst e) (fst h)) eqn:E; [reflexivity |].
  rewrite !summary_cons, IH.
  destruct e as [a u], h as [b v].
  symmetry. apply unionPrio_exchange_strict. exact E.
Qed.

Lemma summary_ordered xs : summary (ordered xs) = summary xs.
Proof.
  induction xs as [|e xs IH]; [reflexivity |].
  rewrite ordered_cons, summary_insert_before, IH. reflexivity.
Qed.

Lemma ordered_head_summary xs e rest :
  ordered xs = e :: rest -> summary xs = entry_summary e.
Proof.
  intro E. rewrite <- summary_ordered, E. apply summary_sorted_head.
  rewrite <- E. apply ordered_sorted.
Qed.

Lemma ordered_empty_iff xs : ordered xs = [] <-> xs = [].
Proof.
  split; [|now intros ->]. intro E.
  pose proof (Permutation_length (ordered_permutation xs)) as Hlen.
  rewrite E in Hlen. destruct xs; [reflexivity | discriminate].
Qed.

Lemma ordered_nonempty_winner xs : xs <> [] ->
  exists k v rest, ordered xs = (k, v) :: rest /\ summary xs = Queue.MkPrio k v.
Proof.
  intro Hne. destruct (ordered xs) as [|[k v] rest] eqn:E.
  - exfalso. apply Hne. apply (proj1 (ordered_empty_iff xs)). exact E.
  - exists k, v, rest. split; [reflexivity |]. now apply ordered_head_summary in E.
Qed.

Lemma insert_before_minimum e xs :
  Forall (entry_le e) xs -> insert_before e xs = e :: xs.
Proof.
  destruct xs as [|h xs]; [reflexivity |]. intro Hall.
  inversion Hall as [|? ? He Htail]; subst. cbn [insert_before].
  unfold entry_le in He. now rewrite He.
Qed.

Lemma ordered_minimum e xs :
  Forall (entry_le e) xs -> ordered (e :: xs) = e :: ordered xs.
Proof.
  intro Hall. rewrite ordered_cons. apply insert_before_minimum.
  rewrite Forall_forall in *. intros x Hin. apply Hall.
  eapply Permutation_in; [apply Permutation_sym, ordered_permutation | exact Hin].
Qed.

Lemma ordered_remove_first_minimum k v pre post :
  Forall (fun e : K * V => leq (fst e) k = false) pre ->
  Forall (fun e : K * V => leq k (fst e) = true) post ->
  ordered (pre ++ (k,v) :: post) = (k,v) :: ordered (pre ++ post).
Proof.
  intros Hpre Hpost. induction Hpre as [|e pre He Hpre IH].
  - cbn [app]. now apply ordered_minimum.
  - cbn [app]. rewrite !ordered_cons, IH. cbn [insert_before fst].
    now rewrite He.
Qed.

Lemma ordered_winner_removal xs k v :
  summary xs = Queue.MkPrio k v ->
  exists pre post,
    xs = pre ++ (k,v) :: post /\
    ordered xs = (k,v) :: ordered (pre ++ post) /\
    Queue.below k (summary pre) = false.
Proof.
  intro E. destruct (summary_first_minimum xs E)
    as [pre [post [Heq [Hpre Hall]]]].
  exists pre, post. split; [exact Heq |]. split.
  - rewrite Heq. apply ordered_remove_first_minimum; [exact Hpre |].
    apply Forall_app in Hall. exact (proj2 Hall).
  - rewrite below_summary by exact laws. clear Heq Hall E.
    induction Hpre as [|e pre He Hpre IH]; cbn [existsb]; [reflexivity |].
    now rewrite He, IH.
Qed.

Lemma insert_before_exchange_strict (a b : K * V) xs :
  leq (fst a) (fst b) = false ->
  insert_before a (insert_before b xs) = insert_before b (insert_before a xs).
Proof.
  intro Eab. pose proof (priority_reverse_of_false Eab) as Eba.
  induction xs as [|c xs IH]; cbn [insert_before].
  - now rewrite Eab, Eba.
  - destruct (leq (fst a) (fst c)) eqn:Eac;
      destruct (leq (fst b) (fst c)) eqn:Ebc;
      cbn [insert_before]; rewrite ?Eab, ?Eba, ?Eac, ?Ebc; try reflexivity.
    + pose proof (priority_le_trans laws Eba Eac). congruence.
    + now rewrite IH.
Qed.

Lemma ordered_insert_before_app e xs ys :
  ordered (insert_before e xs ++ ys) = insert_before e (ordered (xs ++ ys)).
Proof.
  induction xs as [|h xs IH]; [reflexivity |].
  cbn [insert_before]. destruct (leq (fst e) (fst h)) eqn:E;
    cbn [app]; rewrite !ordered_cons; [reflexivity |].
  rewrite IH. symmetry. now apply insert_before_exchange_strict.
Qed.

Lemma ordered_insert_before e xs :
  ordered (insert_before e xs) = insert_before e (ordered xs).
Proof.
  pose proof (ordered_insert_before_app e xs []) as E.
  now rewrite !app_nil_r in E.
Qed.

Lemma ordered_normalize_left xs ys :
  ordered (ordered xs ++ ys) = ordered (xs ++ ys).
Proof.
  induction xs as [|e xs IH]; [reflexivity |].
  rewrite ordered_cons, ordered_insert_before_app, IH. reflexivity.
Qed.

Lemma stable_merge_models xs ys :
  stable_merge (ordered xs) (ordered ys) = ordered (xs ++ ys).
Proof. rewrite <- ordered_app, ordered_normalize_left. reflexivity. Qed.

Lemma stable_merge_left_identity xs : stable_merge [] xs = xs.
Proof. reflexivity. Qed.

Lemma stable_merge_right_identity xs :
  StronglySorted entry_le xs -> stable_merge xs [] = xs.
Proof. apply ordered_sorted_identity. Qed.

Lemma stable_merge_associative xs ys zs :
  StronglySorted entry_le xs -> StronglySorted entry_le ys ->
  StronglySorted entry_le zs ->
  stable_merge xs (stable_merge ys zs) = stable_merge (stable_merge xs ys) zs.
Proof.
  intros Hx Hy Hz.
  rewrite <- (ordered_sorted_identity Hx), <- (ordered_sorted_identity Hy),
    <- (ordered_sorted_identity Hz).
  rewrite !stable_merge_models.
  rewrite <- (stable_merge_models xs (ys ++ zs)),
    <- (stable_merge_models (xs ++ ys) zs).
  rewrite !stable_merge_models, app_assoc. reflexivity.
Qed.

Lemma stable_merge_summary xs ys :
  summary (stable_merge xs ys) = Queue.unionPrio (summary xs) (summary ys).
Proof.
  induction xs as [|e xs IH].
  - symmetry. apply unionPrio_left_identity.
  - change (summary (insert_before e (stable_merge xs ys)) =
      Queue.unionPrio (summary (e :: xs)) (summary ys)).
    rewrite summary_insert_before, IH, summary_cons.
    apply unionPrio_associative; exact laws.
Qed.

Lemma summary_measure_entries xs :
  fold_right GHC.Base.mappend GHC.Base.mempty
    (map (fun e : K * V => Data.FingerTree.measure
      (Queue.MkEntry (fst e) (snd e))) xs) = summary xs.
Proof.
  induction xs as [|e xs IH]; [reflexivity |].
  change (Queue.unionPrio (entry_summary e)
    (fold_right GHC.Base.mappend GHC.Base.mempty
      (map (fun x : K * V => Data.FingerTree.measure
        (Queue.MkEntry (fst x) (snd x))) xs)) =
    Queue.unionPrio (entry_summary e) (summary xs)).
  now rewrite IH.
Qed.

End StableModel.
End Order.

Section PayloadMaps.
Context {K : Type} `{GHC.Base.Ord K} {A B : Type} (f : A -> B).

Definition map_prio (p : Queue.Prio K A) : Queue.Prio K B :=
  match p with Queue.NoPrio => Queue.NoPrio | Queue.MkPrio k v => Queue.MkPrio k (f v) end.

Definition map_entry (e : K * A) : K * B := (fst e, f (snd e)).

Lemma map_prio_union p q :
  map_prio (Queue.unionPrio p q) = Queue.unionPrio (map_prio p) (map_prio q).
Proof.
  destruct p as [|a u], q as [|b v]; cbn [map_prio Queue.unionPrio];
    try reflexivity. now destruct (GHC.Base.op_zlze__ a b).
Qed.

Lemma summary_map_payload xs :
  summary (map map_entry xs) = map_prio (summary xs).
Proof.
  induction xs as [|[k v] xs IH]; [reflexivity |].
  cbn [map]. rewrite !summary_cons, IH, map_prio_union. reflexivity.
Qed.

Lemma insert_before_map_payload e xs :
  insert_before (map_entry e) (map map_entry xs) = map map_entry (insert_before e xs).
Proof.
  induction xs as [|h xs IH]; cbn [insert_before map map_entry fst snd];
    [reflexivity |].
  destruct (GHC.Base.op_zlze__ (fst e) (fst h)); cbn [map];
    [reflexivity | now rewrite IH].
Qed.

Lemma ordered_map_payload xs : ordered (map map_entry xs) = map map_entry (ordered xs).
Proof.
  induction xs as [|e xs IH]; [reflexivity |].
  cbn [map]. rewrite !ordered_cons, IH, insert_before_map_payload. reflexivity.
Qed.

End PayloadMaps.

Section EntryInstances.
Context {K A B : Type}.

Lemma entry_fmap_behavior (f : A -> B) k v :
  GHC.Base.fmap f (Queue.MkEntry k v : Queue.Entry K A) = Queue.MkEntry k (f v).
Proof. reflexivity. Qed.

Lemma entry_replace_behavior (b : B) k (v : A) :
  GHC.Base.op_zlzd__ b (Queue.MkEntry k v : Queue.Entry K A) = Queue.MkEntry k b.
Proof. reflexivity. Qed.

Lemma entry_fmap_identity (e : Queue.Entry K A) : GHC.Base.fmap (fun x => x) e = e.
Proof. destruct e; reflexivity. Qed.

Lemma entry_fmap_composition {C : Type} (f : A -> B) (g : B -> C) (e : Queue.Entry K A) :
  GHC.Base.fmap (fun x => g (f x)) e = GHC.Base.fmap g (GHC.Base.fmap f e).
Proof. destruct e; reflexivity. Qed.

Lemma entry_foldMap_behavior {M : Type} `{GHC.Base.Monoid M} (f : A -> M) k v :
  Data.Foldable.foldMap f (Queue.MkEntry k v : Queue.Entry K A) = f v.
Proof. reflexivity. Qed.

Lemma entry_fold_behavior `{GHC.Base.Monoid A} k v :
  Data.Foldable.fold (Queue.MkEntry k v : Queue.Entry K A) = v.
Proof. reflexivity. Qed.

Lemma entry_foldr_behavior (f : A -> B -> B) z k v :
  Data.Foldable.foldr f z (Queue.MkEntry k v : Queue.Entry K A) = f v z.
Proof. reflexivity. Qed.

Lemma entry_foldl_behavior (f : B -> A -> B) z k v :
  Data.Foldable.foldl f z (Queue.MkEntry k v : Queue.Entry K A) = f z v.
Proof. reflexivity. Qed.

Lemma entry_foldr_strict_behavior (f : A -> B -> B) z k v :
  Data.Foldable.foldr' f z (Queue.MkEntry k v : Queue.Entry K A) = f v z.
Proof. reflexivity. Qed.

Lemma entry_foldl_strict_behavior (f : B -> A -> B) z k v :
  Data.Foldable.foldl' f z (Queue.MkEntry k v : Queue.Entry K A) = f z v.
Proof. reflexivity. Qed.

(* This inherited default starts at mempty; simplifying it to f v requires
   the explicit propositional monoid identity, not a Boolean-equality class. *)
Lemma entry_foldMap_strict_behavior {M : Type} `{GHC.Base.Monoid M} (f : A -> M) k v :
  Data.Foldable.foldMap' f (Queue.MkEntry k v : Queue.Entry K A) =
  GHC.Base.op_zlzlzgzg__ GHC.Base.mempty (f v).
Proof. reflexivity. Qed.

Lemma entry_foldMap_strict_identity {M : Type} `{GHC.Base.Monoid M}
  (identity : forall x : M, GHC.Base.op_zlzlzgzg__ GHC.Base.mempty x = x)
  (f : A -> M) k v :
  Data.Foldable.foldMap' f (Queue.MkEntry k v : Queue.Entry K A) = f v.
Proof. rewrite entry_foldMap_strict_behavior. apply identity. Qed.

Lemma entry_toList_behavior k v :
  Data.Foldable.toList (Queue.MkEntry k v : Queue.Entry K A) = [v].
Proof. reflexivity. Qed.

Lemma entry_null_behavior (e : Queue.Entry K A) : Data.Foldable.null e = false.
Proof. destruct e; reflexivity. Qed.

Lemma entry_length_behavior (e : Queue.Entry K A) :
  Data.Foldable.length e = GHC.Num.fromInteger (BinNums.Zpos BinNums.xH).
Proof. destruct e; reflexivity. Qed.

Lemma entry_product_behavior `{GHC.Num.Num A} k v :
  Data.Foldable.product (Queue.MkEntry k v : Queue.Entry K A) =
  GHC.Num.op_zt__ (GHC.Num.fromInteger (BinNums.Zpos BinNums.xH)) v.
Proof. reflexivity. Qed.

Lemma entry_sum_behavior `{GHC.Num.Num A} k v :
  Data.Foldable.sum (Queue.MkEntry k v : Queue.Entry K A) =
  GHC.Num.op_zp__ (GHC.Num.fromInteger BinNums.Z0) v.
Proof. reflexivity. Qed.

End EntryInstances.

(* Audit every declaration, including the explicit order-law record and its
   projections. All reports must be closed: laws remain visible theorem
   parameters, never global axioms. *)
Check @PriorityOrderLaws.
Print Assumptions PriorityOrderLaws.
Check @Build_PriorityOrderLaws.
Print Assumptions Build_PriorityOrderLaws.
Check @priority_le_refl.
Print Assumptions priority_le_refl.
Check @priority_le_trans.
Print Assumptions priority_le_trans.
Check @priority_le_total.
Print Assumptions priority_le_total.
Check @PriorityEqualityCoherence.
Print Assumptions PriorityEqualityCoherence.
Check @priority_reverse_of_false.
Print Assumptions priority_reverse_of_false.
Check @unionPrio_left_identity.
Print Assumptions unionPrio_left_identity.
Check @unionPrio_right_identity.
Print Assumptions unionPrio_right_identity.
Check @unionPrio_associative.
Print Assumptions unionPrio_associative.
Check @unionPrio_left_winner.
Print Assumptions unionPrio_left_winner.
Check @unionPrio_right_winner.
Print Assumptions unionPrio_right_winner.
Check @prio_semigroup_behavior.
Print Assumptions prio_semigroup_behavior.
Check @prio_monoid_append_behavior.
Print Assumptions prio_monoid_append_behavior.
Check @prio_monoid_empty_behavior.
Print Assumptions prio_monoid_empty_behavior.
Check @prio_monoid_concat_behavior.
Print Assumptions prio_monoid_concat_behavior.
Check @prio_monoid_propositional_laws.
Print Assumptions prio_monoid_propositional_laws.
Check @entry_measure_behavior.
Print Assumptions entry_measure_behavior.
Check @entry_summary.
Print Assumptions entry_summary.
Check @summary.
Print Assumptions summary.
Check @summary_nil.
Print Assumptions summary_nil.
Check @summary_cons.
Print Assumptions summary_cons.
Check @summary_app.
Print Assumptions summary_app.
Check @summary_empty_iff.
Print Assumptions summary_empty_iff.
Check @summary_minimum.
Print Assumptions summary_minimum.
Check @summary_first_minimum.
Print Assumptions summary_first_minimum.
Check @below_unionPrio.
Print Assumptions below_unionPrio.
Check @below_summary.
Print Assumptions below_summary.
Check @below_summary_app.
Print Assumptions below_summary_app.
Check @below_summary_monotone.
Print Assumptions below_summary_monotone.
Check @below_summary_first_winner.
Print Assumptions below_summary_first_winner.
Check @entry_le.
Print Assumptions entry_le.
Check @tied.
Print Assumptions tied.
Check @insert_before.
Print Assumptions insert_before.
Check @ordered.
Print Assumptions ordered.
Check @stable_merge.
Print Assumptions stable_merge.
Check @insert_before_permutation.
Print Assumptions insert_before_permutation.
Check @insert_before_forall.
Print Assumptions insert_before_forall.
Check @insert_before_sorted.
Print Assumptions insert_before_sorted.
Check @ordered_permutation.
Print Assumptions ordered_permutation.
Check @ordered_sorted.
Print Assumptions ordered_sorted.
Check @ordered_cons.
Print Assumptions ordered_cons.
Check @ordered_sorted_identity.
Print Assumptions ordered_sorted_identity.
Check @ordered_idempotent.
Print Assumptions ordered_idempotent.
Check @insert_before_ties.
Print Assumptions insert_before_ties.
Check @ordered_ties.
Print Assumptions ordered_ties.
Check @ordered_app.
Print Assumptions ordered_app.
Check @stable_merge_permutation.
Print Assumptions stable_merge_permutation.
Check @stable_merge_sorted.
Print Assumptions stable_merge_sorted.
Check @stable_merge_ties.
Print Assumptions stable_merge_ties.
Check @ordered_add_ties.
Print Assumptions ordered_add_ties.
Check @ordered_insert_ties.
Print Assumptions ordered_insert_ties.
Check @ordered_union_ties.
Print Assumptions ordered_union_ties.
Check @summary_dominated.
Print Assumptions summary_dominated.
Check @summary_sorted_head.
Print Assumptions summary_sorted_head.
Check @unionPrio_exchange_strict.
Print Assumptions unionPrio_exchange_strict.
Check @summary_insert_before.
Print Assumptions summary_insert_before.
Check @summary_ordered.
Print Assumptions summary_ordered.
Check @ordered_head_summary.
Print Assumptions ordered_head_summary.
Check @ordered_empty_iff.
Print Assumptions ordered_empty_iff.
Check @ordered_nonempty_winner.
Print Assumptions ordered_nonempty_winner.
Check @insert_before_minimum.
Print Assumptions insert_before_minimum.
Check @ordered_minimum.
Print Assumptions ordered_minimum.
Check @ordered_remove_first_minimum.
Print Assumptions ordered_remove_first_minimum.
Check @ordered_winner_removal.
Print Assumptions ordered_winner_removal.
Check @insert_before_exchange_strict.
Print Assumptions insert_before_exchange_strict.
Check @ordered_insert_before_app.
Print Assumptions ordered_insert_before_app.
Check @ordered_insert_before.
Print Assumptions ordered_insert_before.
Check @ordered_normalize_left.
Print Assumptions ordered_normalize_left.
Check @stable_merge_models.
Print Assumptions stable_merge_models.
Check @stable_merge_left_identity.
Print Assumptions stable_merge_left_identity.
Check @stable_merge_right_identity.
Print Assumptions stable_merge_right_identity.
Check @stable_merge_associative.
Print Assumptions stable_merge_associative.
Check @stable_merge_summary.
Print Assumptions stable_merge_summary.
Check @summary_measure_entries.
Print Assumptions summary_measure_entries.
Check @map_prio.
Print Assumptions map_prio.
Check @map_entry.
Print Assumptions map_entry.
Check @map_prio_union.
Print Assumptions map_prio_union.
Check @summary_map_payload.
Print Assumptions summary_map_payload.
Check @insert_before_map_payload.
Print Assumptions insert_before_map_payload.
Check @ordered_map_payload.
Print Assumptions ordered_map_payload.
Check @entry_fmap_behavior.
Print Assumptions entry_fmap_behavior.
Check @entry_replace_behavior.
Print Assumptions entry_replace_behavior.
Check @entry_fmap_identity.
Print Assumptions entry_fmap_identity.
Check @entry_fmap_composition.
Print Assumptions entry_fmap_composition.
Check @entry_foldMap_behavior.
Print Assumptions entry_foldMap_behavior.
Check @entry_fold_behavior.
Print Assumptions entry_fold_behavior.
Check @entry_foldr_behavior.
Print Assumptions entry_foldr_behavior.
Check @entry_foldl_behavior.
Print Assumptions entry_foldl_behavior.
Check @entry_foldr_strict_behavior.
Print Assumptions entry_foldr_strict_behavior.
Check @entry_foldl_strict_behavior.
Print Assumptions entry_foldl_strict_behavior.
Check @entry_foldMap_strict_behavior.
Print Assumptions entry_foldMap_strict_behavior.
Check @entry_foldMap_strict_identity.
Print Assumptions entry_foldMap_strict_identity.
Check @entry_toList_behavior.
Print Assumptions entry_toList_behavior.
Check @entry_null_behavior.
Print Assumptions entry_null_behavior.
Check @entry_length_behavior.
Print Assumptions entry_length_behavior.
Check @entry_product_behavior.
Print Assumptions entry_product_behavior.
Check @entry_sum_behavior.
Print Assumptions entry_sum_behavior.
