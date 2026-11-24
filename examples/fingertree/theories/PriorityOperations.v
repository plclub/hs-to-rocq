From Stdlib Require Import Lists.List Bool.Bool Lia Arith.Wf_nat Wellfounded.Inclusion Classes.RelationClasses ZArith.ZArith.
Require Import FingerTreeProofs.CoreModel FingerTreeProofs.CoreOperations
  FingerTreeProofs.CoreSearch FingerTreeProofs.CoreSize FingerTreeProofs.PriorityModel.
Require Import HsToRocq.DeferredFix.
Import ListNotations.
Set Implicit Arguments.
Module PQ := Data.PriorityQueue.FingerTree.
Module FT := Data.FingerTree.

Definition entryPair {K V} (e : PQ.Entry K V) : K * V :=
  match e with PQ.MkEntry k v => (k,v) end.
Definition treeEntries {K V} (t : FT.FingerTree (PQ.Prio K V) (PQ.Entry K V)) :=
  map entryPair (CoreModel.contents t).
Definition rawEntries {K V} (q : PQ.PQueue K V) :=
  match q with PQ.MkPQueue t => treeEntries t end.

Section Queue.
Context {K : Type} `{GHC.Base.Ord K}.
Context (laws : PriorityOrderLaws).
Context {V : Type}.
Local Abbreviation M := (@PQ.Measured__Prio__Entry K V H H0).
Local Abbreviation leq := GHC.Base.op_zlze__.

Definition valid (q : PQ.PQueue K V) : Prop :=
  PriorityOrderLaws /\ match q with PQ.MkPQueue t => CoreModel.validity M t end.
Definition model (q : PQ.PQueue K V) : list (K * V) := ordered (rawEntries q).

Lemma prio_assoc (p q r : PQ.Prio K V) :
  GHC.Base.mappend (GHC.Base.mappend p q) r = GHC.Base.mappend p (GHC.Base.mappend q r).
Proof. symmetry. apply unionPrio_associative; exact laws. Qed.
Lemma prio_left_id (p : PQ.Prio K V) : GHC.Base.mappend GHC.Base.mempty p = p.
Proof. apply unionPrio_left_identity. Qed.
Lemma prio_right_id (p : PQ.Prio K V) : GHC.Base.mappend p GHC.Base.mempty = p.
Proof. apply unionPrio_right_identity. Qed.

Lemma listMeasure_pairs xs :
  CoreModel.listMeasure (@FT.measure _ _ _ _ M) xs = summary (map entryPair xs).
Proof.
  induction xs as [|[k v] xs IH]; [reflexivity |].
  change (PQ.unionPrio (PQ.MkPrio k v) (CoreModel.listMeasure (@FT.measure _ _ _ _ M) xs) =
    PQ.unionPrio (PQ.MkPrio k v) (summary (map entryPair xs))). now rewrite IH.
Qed.

Lemma measure_entries t : CoreModel.validity M t -> FT.measure t = summary (treeEntries t).
Proof.
  intro W. rewrite (CoreModel.measure_contents prio_assoc prio_left_id prio_right_id M t W).
  apply listMeasure_pairs.
Qed.

Lemma empty_raw : rawEntries (PQ.empty : PQ.PQueue K V) = [].
Proof. reflexivity. Qed.
Lemma singleton_raw (k : K) (v : V) : rawEntries (PQ.singleton k v) = [(k,v)].
Proof. reflexivity. Qed.
Lemma insert_raw k v (q : PQ.PQueue K V) : rawEntries (PQ.insert k v q) = (k,v) :: rawEntries q.
Proof. destruct q as [t]. unfold rawEntries, treeEntries, PQ.insert. now rewrite consTree_contents. Qed.
Lemma add_raw k v (q : PQ.PQueue K V) : rawEntries (PQ.add k v q) = rawEntries q ++ [(k,v)].
Proof. destruct q as [t]. unfold rawEntries, treeEntries, PQ.add. now rewrite snocTree_contents, map_app. Qed.
Lemma union_raw (q r : PQ.PQueue K V) : rawEntries (PQ.union q r) = rawEntries q ++ rawEntries r.
Proof. destruct q as [t], r as [u]. unfold rawEntries, treeEntries, PQ.union. now rewrite append_contents, map_app. Qed.
Lemma fromList_raw (xs : list (K * V)) : rawEntries (PQ.fromList xs) = xs.
Proof.
  induction xs as [|[k v] xs IH]; [reflexivity |].
  change (rawEntries (PQ.insert k v (PQ.fromList xs)) = (k,v) :: xs).
  now rewrite insert_raw, IH.
Qed.

Lemma empty_valid : valid (PQ.empty : PQ.PQueue K V).
Proof. split; [exact laws | exact I]. Qed.
Lemma singleton_valid k v : valid (PQ.singleton k v).
Proof. split; [exact laws | exact I]. Qed.
Lemma insert_valid k v (q : PQ.PQueue K V) : valid q -> valid (PQ.insert k v q).
Proof.
  destruct q as [t]. intros [L W]. split; [exact L |].
  apply consTree_validity; [exact prio_assoc | exact prio_right_id | exact W].
Qed.
Lemma add_valid k v (q : PQ.PQueue K V) : valid q -> valid (PQ.add k v q).
Proof.
  destruct q as [t]. intros [L W]. split; [exact L |].
  apply snocTree_validity; [exact prio_assoc | exact prio_left_id | exact prio_right_id | exact W].
Qed.
Lemma union_valid (q r : PQ.PQueue K V) : valid q -> valid r -> valid (PQ.union q r).
Proof.
  destruct q as [t], r as [u]. intros [L W] [_ U]. split; [exact L |].
  apply append_validity; [exact prio_assoc | exact prio_left_id | exact prio_right_id | exact W | exact U].
Qed.
Lemma fromList_valid xs : valid (@PQ.fromList K V _ _ xs).
Proof.
  induction xs as [|[k v] xs IH]; [apply empty_valid |].
  change (valid (PQ.insert k v (PQ.fromList xs))). now apply insert_valid.
Qed.

Lemma empty_model : model (PQ.empty : PQ.PQueue K V) = [].
Proof. reflexivity. Qed.
Lemma singleton_model k v : model (PQ.singleton k v) = [(k,v)].
Proof. reflexivity. Qed.
Lemma insert_model k v q : model (PQ.insert k v q) = insert_before (k,v) (model q).
Proof. unfold model. rewrite insert_raw. reflexivity. Qed.
Lemma add_model k v q : model (PQ.add k v q) = ordered (rawEntries q ++ [(k,v)]).
Proof. unfold model. now rewrite add_raw. Qed.
Lemma union_model q r : model (PQ.union q r) = stable_merge (model q) (model r).
Proof. unfold model. rewrite union_raw. symmetry. apply stable_merge_models; exact laws. Qed.
Lemma fromList_model xs : model (@PQ.fromList K V _ _ xs) = ordered xs.
Proof. unfold model. now rewrite fromList_raw. Qed.
Lemma null_model q : PQ.null q = true <-> model q = [].
Proof.
  destruct q as [t]. change (FT.null t = true <-> ordered (map entryPair (contents t)) = []).
  rewrite ordered_empty_iff, null_contents.
  split; intro E; [now rewrite E | now apply map_eq_nil in E].
Qed.

Lemma insert_ties k v q : filter (tied k) (model (PQ.insert k v q)) =
  (k,v) :: filter (tied k) (model q).
Proof.
  rewrite insert_model, insert_before_ties by exact laws.
  unfold tied. cbn [fst]. rewrite (priority_le_refl laws). reflexivity.
Qed.
Lemma add_ties k v q : filter (tied k) (model (PQ.add k v q)) =
  filter (tied k) (model q) ++ [(k,v)].
Proof.
  rewrite add_model, ordered_add_ties by exact laws.
  unfold model. rewrite ordered_ties by exact laws.
  unfold tied. cbn [fst]. rewrite (priority_le_refl laws). reflexivity.
Qed.
Lemma union_ties k q r : filter (tied k) (model (PQ.union q r)) =
  filter (tied k) (model q) ++ filter (tied k) (model r).
Proof. rewrite union_model, stable_merge_ties by exact laws. reflexivity. Qed.
Lemma fromList_ties k xs : filter (tied k) (model (@PQ.fromList K V _ _ xs)) = filter (tied k) xs.
Proof. rewrite fromList_model. apply ordered_ties; exact laws. Qed.

(* A triggered split really selects the cached full entry, not merely an
   equivalent priority. The proof uses the global winning summary and the
   false-prefix/true-extension boundary, with no raw sortedness assumption. *)
Lemma winner_at_cut (pre : list (K * V)) (a : K * V) post k v :
  summary (pre ++ a :: post) = PQ.MkPrio k v ->
  PQ.below k (summary pre) = false ->
  PQ.below k (summary (pre ++ [a])) = true ->
  a = (k,v) /\ ordered (pre ++ a :: post) = (k,v) :: ordered (pre ++ post).
Proof.
  intros Es Ef Et.
  assert (Ex : leq (fst a) k = true).
  { rewrite below_summary_app, Ef in Et by exact laws. exact Et. }
  destruct (summary_minimum laws (pre ++ a :: post) Es) as [_ Hall].
  rewrite Forall_app in Hall. destruct Hall as [Hp Hs].
  inversion Hs as [|? ? Ha Hpost]; subst.
  assert (Da : Forall (fun e : K * V => leq (fst a) (fst e) = true) post).
  { eapply Forall_impl; [|exact Hpost]. intros e He. eapply priority_le_trans; eauto. }
  rewrite summary_app, summary_cons in Es by exact laws.
  destruct a as [ak av]. cbn [fst snd entry_summary] in *.
  change (PQ.unionPrio (summary pre) (PQ.unionPrio (PQ.MkPrio ak av) (summary post)) = PQ.MkPrio k v) in Es.
  rewrite (summary_dominated laws ak av Da) in Es.
  assert (Win : PQ.unionPrio (summary pre) (PQ.MkPrio ak av) = PQ.MkPrio ak av).
  { destruct (summary pre) as [|b w]; [reflexivity |].
    cbn [PQ.below] in Ef. cbn [PQ.unionPrio].
    destruct (leq b ak) eqn:Eba; [|reflexivity].
    assert (leq b k = true) by (eapply priority_le_trans; eauto). congruence. }
  rewrite Win in Es. inversion Es; subst ak av. split; [reflexivity |].
  apply ordered_remove_first_minimum; [|exact Hpost].
  rewrite below_summary in Ef by exact laws.
  apply Forall_forall. intros e Hin.
  destruct (leq (fst e) k) eqn:E; [|reflexivity].
  assert (existsb (fun e : K * V => leq (fst e) k) pre = true).
  { apply existsb_exists. exists e. auto. } congruence.
Qed.

Lemma minViewWithKey_nonempty t :
  CoreModel.validity M t -> t <> FT.Empty ->
  exists k v l r x rest,
    FT.measure t = PQ.MkPrio k v /\
    FT.split (PQ.below k) t = (l,r) /\ FT.viewl r = FT.op_ZCzl__ x rest /\
    entryPair x = (k,v) /\
    PQ.minViewWithKey (PQ.MkPQueue t) = Some ((k,v), PQ.MkPQueue (FT.op_zgzl__ l rest)) /\
    valid (PQ.MkPQueue (FT.op_zgzl__ l rest)) /\
    model (PQ.MkPQueue t) = (k,v) :: model (PQ.MkPQueue (FT.op_zgzl__ l rest)) /\
    PQ.pqueue_size (PQ.MkPQueue (FT.op_zgzl__ l rest)) < PQ.pqueue_size (PQ.MkPQueue t).
Proof.
  intros W NE.
  assert (NT : FT.null t = false).
  { destruct (FT.null t) eqn:E; [|reflexivity].
    apply null_contents, contents_empty_iff in E. contradiction. }
  assert (Ns : summary (treeEntries t) <> PQ.NoPrio).
  { intro E. apply summary_empty_iff in E.
    unfold treeEntries in E. apply map_eq_nil, contents_empty_iff in E. contradiction. }
  destruct (FT.measure t) as [|k v] eqn:Em.
  { rewrite measure_entries in Em by exact W. contradiction. }
  destruct (FT.split (PQ.below k) t) as [l r] eqn:Esp.
  assert (Trigger : PQ.below k (FT.measure t) = true).
  { rewrite Em. apply priority_le_refl; exact laws. }
  destruct (split_trigger_contract prio_assoc prio_left_id prio_right_id M (PQ.below k)
    t l r W eq_refl Trigger Esp) as [Wl [Wr [Nr [Fl [y [rr [Cr [Wrr [Ct T]]]]]]]]].
  pose proof (viewl_contentsWith _ r M _ (fun z => [z])) as Cv.
  destruct (FT.viewl r) as [|x rest] eqn:Ev.
  { change (contents r = []) in Cv. apply contents_empty_iff in Cv. contradiction. }
  change (contents r = x :: contents rest) in Cv.
  destruct (viewl_contract M prio_assoc prio_right_id r x rest Wr Ev) as [Wrest _].
  destruct (split_contract M prio_assoc prio_left_id prio_right_id (PQ.below k) t l r W Esp)
    as [_ [_ Csplit]].
  assert (Cpair : treeEntries t = treeEntries l ++ entryPair x :: treeEntries rest).
  { unfold treeEntries. rewrite Csplit, Cv, map_app. reflexivity. }
  assert (Tpair : PQ.below k (summary (treeEntries l ++ [entryPair x])) = true).
  { pose proof (eq_trans (eq_sym Cr) Cv) as Ec. inversion Ec; subst y.
    rewrite summary_app by exact laws.
    rewrite <- (measure_entries l Wl). destruct x; exact T. }
  assert (Fpair : PQ.below k (summary (treeEntries l)) = false).
  { now rewrite <- (measure_entries l Wl). }
  assert (Spair : summary (treeEntries l ++ entryPair x :: treeEntries rest) = PQ.MkPrio k v).
  { rewrite <- Cpair, <- (measure_entries t W). exact Em. }
  destruct (winner_at_cut (treeEntries l) (entryPair x) (treeEntries rest) Spair Fpair Tpair) as [X O].
  exists k, v, l, r, x, rest.
  refine (conj eq_refl (conj Esp (conj Ev (conj X (conj _ (conj _ (conj _ _))))))).
  - unfold PQ.minViewWithKey. rewrite NT, Em, Esp, Ev. reflexivity.
  - split; [exact laws |].
    apply append_validity; [exact prio_assoc | exact prio_left_id | exact prio_right_id | exact Wl | exact Wrest].
  - unfold model, rawEntries. unfold treeEntries at 2.
    rewrite append_contents, map_app. rewrite Cpair. exact O.
  - apply (split_viewl_append_lt prio_right_id M (PQ.below k) t l r x rest Esp Ev).
Qed.

Definition extractionSpec (q : PQ.PQueue K V) : Prop :=
  match PQ.minViewWithKey q with
  | None => model q = []
  | Some (e, q') => valid q' /\ model q = e :: model q' /\ PQ.pqueue_size q' < PQ.pqueue_size q
  end.

Lemma minViewWithKey_correct q : valid q -> extractionSpec q.
Proof.
  destruct q as [t]. intros [L W]. destruct t as [|a|c pr mid sf] eqn:E.
  - reflexivity.
  - destruct (minViewWithKey_nonempty W ltac:(discriminate))
      as [k [v [l [r [x [rest [_ [_ [_ [_ [Ev [Vr [Co Sz]]]]]]]]]]]]].
    unfold extractionSpec. rewrite Ev. auto.
  - destruct (minViewWithKey_nonempty W ltac:(discriminate))
      as [k [v [l [r [x [rest [_ [_ [_ [_ [Ev [Vr [Co Sz]]]]]]]]]]]]].
    unfold extractionSpec. rewrite Ev. auto.
Qed.

Lemma minViewWithKey_some q e q' : valid q -> PQ.minViewWithKey q = Some (e,q') ->
  valid q' /\ model q = e :: model q' /\ PQ.pqueue_size q' < PQ.pqueue_size q.
Proof. intros W E. pose proof (minViewWithKey_correct W) as C. unfold extractionSpec in C. now rewrite E in C. Qed.

Lemma minViewWithKey_none q : valid q ->
  (PQ.minViewWithKey q = None <-> model q = []).
Proof.
  intro W. pose proof (minViewWithKey_correct W) as C. unfold extractionSpec in C.
  destruct (PQ.minViewWithKey q) as [[e q']|] eqn:E.
  - destruct C as [_ [Co _]]. rewrite Co. split; discriminate.
  - split; auto.
Qed.

Lemma minView_correct q : valid q ->
  match PQ.minView q with
  | None => model q = []
  | Some (v,q') => valid q' /\ (exists k, model q = (k,v) :: model q') /\
      PQ.pqueue_size q' < PQ.pqueue_size q
  end.
Proof.
  intro W. pose proof (minViewWithKey_correct W) as C.
  unfold extractionSpec in C. unfold PQ.minView.
  destruct (PQ.minViewWithKey q) as [[[k v] q']|]; [|exact C].
  cbn. destruct C as [Vr [Co Sz]]. split; [exact Vr |]. split; [now exists k |exact Sz].
Qed.

Lemma minView_some q v q' : valid q -> PQ.minView q = Some (v,q') ->
  valid q' /\ (exists k, model q = (k,v) :: model q') /\ PQ.pqueue_size q' < PQ.pqueue_size q.
Proof. intros W E. pose proof (minView_correct W) as C. now rewrite E in C. Qed.

Lemma minView_none q : valid q -> (PQ.minView q = None <-> model q = []).
Proof.
  intro W. pose proof (minView_correct W) as C.
  destruct (PQ.minView q) as [[v q']|]; [|tauto].
  destruct C as [_ [[k Co] _]]. rewrite Co. split; discriminate.
Qed.

Definition extractionStep (q' q : PQ.PQueue K V) : Prop :=
  valid q /\ exists e, PQ.minViewWithKey q = Some (e,q').

Lemma extraction_well_founded : well_founded extractionStep.
Proof.
  apply (wf_incl _ extractionStep (ltof _ (@PQ.pqueue_size K V))).
  - intros q' q [W [e E]]. exact (proj2 (proj2 (minViewWithKey_some W E))).
  - apply well_founded_ltof.
Qed.

Definition assocsBody (go : PQ.PQueue K V -> list (K * V)) (q : PQ.PQueue K V) :=
  match PQ.minViewWithKey q with Some (e,q') => e :: go q' | None => [] end.

Lemma assocs_definition q : PQ.assocs q = DeferredFix.deferredFix assocsBody q.
Proof. reflexivity. Qed.

Lemma assocs_recurses_on : DeferredFix.recurses_on valid (ltof _ (@PQ.pqueue_size K V)) assocsBody.
Proof.
  intros g h q W Agree. unfold assocsBody.
  destruct (PQ.minViewWithKey q) as [[e q']|] eqn:E; [|reflexivity].
  destruct (minViewWithKey_some W E) as [Vr [_ Sz]].
  f_equal. apply Agree; assumption.
Qed.

Lemma assocs_unfold q : valid q -> PQ.assocs q =
  match PQ.minViewWithKey q with Some (e,q') => e :: PQ.assocs q' | None => [] end.
Proof.
  intro W. rewrite assocs_definition.
  apply (DeferredFix.deferredFix_eq_on assocsBody valid (ltof _ (@PQ.pqueue_size K V))
    (well_founded_ltof _ _) assocs_recurses_on q W).
Qed.

Lemma assocs_model q : valid q -> PQ.assocs q = model q.
Proof.
  induction q as [q IH] using (well_founded_induction (well_founded_ltof _ (@PQ.pqueue_size K V))).
  intro W. rewrite assocs_unfold by exact W.
  destruct (PQ.minViewWithKey q) as [[e q']|] eqn:E.
  - destruct (minViewWithKey_some W E) as [Vr [Co Sz]].
    rewrite Co, (IH q' Sz Vr). reflexivity.
  - symmetry. now apply (proj1 (minViewWithKey_none W)).
Qed.

Section FoldMap.
Context {R : Type} `{GHC.Base.Monoid R}.

Definition foldMapBody (go : ((V -> R) * PQ.PQueue K V) -> R)
  (input : (V -> R) * PQ.PQueue K V) : R :=
  let '(f,q) := input in match PQ.minView q with
    | None => GHC.Base.mempty
    | Some (v,q') => GHC.Base.mappend (f v) (go (f,q')) end.

Lemma foldMap_definition f q : PQ.Foldable__PQueue_foldMap f q =
  DeferredFix.deferredFix foldMapBody (f,q).
Proof. reflexivity. Qed.

Lemma foldMap_recurses_on : DeferredFix.recurses_on
  (fun input => valid (snd input))
  (ltof _ (fun input => PQ.pqueue_size (snd input))) foldMapBody.
Proof.
  intros g h [f q] W Agree. unfold foldMapBody.
  destruct (PQ.minView q) as [[v q']|] eqn:E; [|reflexivity].
  destruct (minView_some W E) as [Vr [_ Sz]].
  f_equal. apply Agree; assumption.
Qed.

Lemma foldMap_unfold f q : valid q -> PQ.Foldable__PQueue_foldMap f q =
  match PQ.minView q with
  | None => GHC.Base.mempty
  | Some (v,q') => GHC.Base.mappend (f v) (PQ.Foldable__PQueue_foldMap f q') end.
Proof.
  intro W. rewrite foldMap_definition.
  apply (DeferredFix.deferredFix_eq_on foldMapBody
    (fun input => valid (snd input)) (ltof _ (fun input => PQ.pqueue_size (snd input)))
    (well_founded_ltof _ _) foldMap_recurses_on (f,q) W).
Qed.

Lemma foldMap_model f q : valid q -> Data.Foldable.foldMap f q =
  fold_right (fun e acc => GHC.Base.mappend (f (snd e)) acc) GHC.Base.mempty (model q).
Proof.
  induction q as [q IH] using (well_founded_induction (well_founded_ltof _ (@PQ.pqueue_size K V))).
  intro W. change (PQ.Foldable__PQueue_foldMap f q =
    fold_right (fun e acc => GHC.Base.mappend (f (snd e)) acc) GHC.Base.mempty (model q)).
  rewrite foldMap_unfold by exact W.
  destruct (PQ.minView q) as [[v q']|] eqn:E.
  - destruct (minView_some W E) as [Vr [[k Co] Sz]].
    rewrite Co. cbn [fold_right snd]. rewrite <- (IH q' Sz Vr). reflexivity.
  - apply minView_none in E; [|exact W]. rewrite E. reflexivity.
Qed.

End FoldMap.

Lemma foldr_model {B} (f : V -> B -> B) z q : valid q ->
  Data.Foldable.foldr f z q = fold_right (fun e acc => f (snd e) acc) z (model q).
Proof.
  intro W. change (Data.SemigroupInternal.appEndo
    (Data.Foldable.foldMap (fun v => Data.SemigroupInternal.Mk_Endo (f v)) q) z =
    fold_right (fun e acc => f (snd e) acc) z (model q)).
  rewrite foldMap_model by exact W.
  induction (model q); cbn in *; [reflexivity | now rewrite IHl].
Qed.

Lemma foldl_model {B} (f : B -> V -> B) z q : valid q ->
  Data.Foldable.foldl f z q = fold_left (fun acc e => f acc (snd e)) (model q) z.
Proof.
  intro W. change (Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
    (Data.Foldable.foldMap (fun v => Data.SemigroupInternal.Mk_Dual
      (Data.SemigroupInternal.Mk_Endo (fun z => f z v))) q)) z =
    fold_left (fun acc e => f acc (snd e)) (model q) z).
  rewrite foldMap_model by exact W.
  revert z. induction (model q) as [|[k v] xs IH]; intro z; [reflexivity |].
  cbn [fold_right fold_left].
  destruct (fold_right
    (fun e acc => GHC.Base.mappend (Data.SemigroupInternal.Mk_Dual
      (Data.SemigroupInternal.Mk_Endo (fun z => f z (snd e)))) acc)
    GHC.Base.mempty xs) as [[g]] eqn:E.
  exact (IH (f z v)).
Qed.

Lemma foldl_strict_model {B} (f : B -> V -> B) z q : valid q ->
  Data.Foldable.foldl' f z q = fold_left (fun acc e => f acc (snd e)) (model q) z.
Proof.
  intro W. change (Data.Foldable.foldr (fun v k z => k (f z v)) (fun z => z) q z =
    fold_left (fun acc e => f acc (snd e)) (model q) z).
  rewrite foldr_model by exact W.
  revert z. induction (model q); cbn; intro z; [reflexivity | apply IHl].
Qed.

Lemma foldr_strict_model {B} (f : V -> B -> B) z q : valid q ->
  Data.Foldable.foldr' f z q = fold_right (fun e acc => f (snd e) acc) z (model q).
Proof.
  intro W. change (Data.Foldable.foldl (fun k v z => k (f v z)) (fun z => z) q z =
    fold_right (fun e acc => f (snd e) acc) z (model q)).
  rewrite foldl_model by exact W.
  assert (C : forall xs (k : B -> B) z,
    fold_left (fun k (e : K * V) z => k (f (snd e) z)) xs k z =
    k (fold_right (fun e acc => f (snd e) acc) z xs)).
  { induction xs; cbn; intros; [reflexivity | rewrite IHxs; reflexivity]. }
  apply C.
Qed.

Lemma toList_model q : valid q -> Data.Foldable.toList q = map snd (model q).
Proof.
  intro W. change (Data.Foldable.foldr (@cons V) [] q = map snd (model q)).
  rewrite foldr_model by exact W. induction (model q); cbn; congruence.
Qed.

Lemma foldable_null_model q : Data.Foldable.null q = true <-> model q = [].
Proof. apply null_model. Qed.

Lemma foldMap_strict_model {R} `{GHC.Base.Monoid R} (f : V -> R) q : valid q ->
  Data.Foldable.foldMap' f q =
  fold_left (fun acc e => GHC.Base.op_zlzlzgzg__ acc (f (snd e))) (model q) GHC.Base.mempty.
Proof.
  intro W. change (Data.Foldable.foldl' (fun acc v => GHC.Base.op_zlzlzgzg__ acc (f v)) GHC.Base.mempty q =
    fold_left (fun acc e => GHC.Base.op_zlzlzgzg__ acc (f (snd e))) (model q) GHC.Base.mempty).
  apply foldl_strict_model; exact W.
Qed.

Lemma fold_behavior `{GHC.Base.Monoid V} q : valid q -> Data.Foldable.fold q =
  fold_right (fun e acc => GHC.Base.mappend (snd e) acc) GHC.Base.mempty (model q).
Proof. apply foldMap_model. Qed.

Lemma length_fold_model q : valid q -> Data.Foldable.length q =
  fold_left (fun acc (_ : K * V) => GHC.Num.op_zp__ acc (GHC.Num.fromInteger (BinNums.Zpos BinNums.xH)))
    (model q) (GHC.Num.fromInteger BinNums.Z0).
Proof. apply foldl_strict_model. Qed.

Lemma product_fold_model `{GHC.Num.Num V} q : valid q ->
  Data.Foldable.product q = Data.SemigroupInternal.getProduct
    (fold_left (fun acc e => GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Product (snd e)))
      (model q) GHC.Base.mempty).
Proof.
  intro W. change (Data.SemigroupInternal.getProduct
    (Data.Foldable.foldMap' Data.SemigroupInternal.Mk_Product q) =
    Data.SemigroupInternal.getProduct
      (fold_left (fun acc e => GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Product (snd e)))
        (model q) GHC.Base.mempty)).
  now rewrite foldMap_strict_model by exact W.
Qed.

Lemma sum_fold_model `{GHC.Num.Num V} q : valid q ->
  Data.Foldable.sum q = Data.SemigroupInternal.getSum
    (fold_left (fun acc e => GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Sum (snd e)))
      (model q) GHC.Base.mempty).
Proof.
  intro W. change (Data.SemigroupInternal.getSum
    (Data.Foldable.foldMap' Data.SemigroupInternal.Mk_Sum q) =
    Data.SemigroupInternal.getSum
      (fold_left (fun acc e => GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Sum (snd e)))
        (model q) GHC.Base.mempty)).
  now rewrite foldMap_strict_model by exact W.
Qed.

Definition equivalent (q r : PQ.PQueue K V) : Prop := model q = model r.

Lemma equivalent_equivalence : Equivalence equivalent.
Proof. split; unfold Reflexive, Symmetric, Transitive, equivalent; congruence. Qed.

Lemma semigroup_behavior (q r : PQ.PQueue K V) : GHC.Base.op_zlzlzgzg__ q r = PQ.union q r.
Proof. reflexivity. Qed.
Lemma monoid_append_behavior (q r : PQ.PQueue K V) : GHC.Base.mappend q r = PQ.union q r.
Proof. reflexivity. Qed.
Lemma monoid_empty_behavior : (GHC.Base.mempty : PQ.PQueue K V) = PQ.empty.
Proof. reflexivity. Qed.
Lemma monoid_concat_raw qs : rawEntries (GHC.Base.mconcat qs : PQ.PQueue K V) = concat (map rawEntries qs).
Proof.
  induction qs as [|q qs IH]; [reflexivity |].
  change (rawEntries (PQ.union q (GHC.Base.mconcat qs)) = rawEntries q ++ concat (map rawEntries qs)).
  now rewrite union_raw, IH.
Qed.
Lemma monoid_concat_valid qs : Forall valid qs -> valid (GHC.Base.mconcat qs).
Proof.
  intro W. induction W; [apply empty_valid |].
  change (valid (PQ.union x (GHC.Base.mconcat l))). now apply union_valid.
Qed.
Lemma monoid_concat_model qs : model (GHC.Base.mconcat qs : PQ.PQueue K V) = ordered (concat (map rawEntries qs)).
Proof. unfold model. now rewrite monoid_concat_raw. Qed.
Lemma union_associative q r s : equivalent (PQ.union q (PQ.union r s)) (PQ.union (PQ.union q r) s).
Proof. unfold equivalent, model. rewrite !union_raw, app_assoc. reflexivity. Qed.
Lemma union_left_identity q : equivalent (PQ.union PQ.empty q) q.
Proof. unfold equivalent, model. rewrite union_raw. reflexivity. Qed.
Lemma union_right_identity q : equivalent (PQ.union q PQ.empty) q.
Proof. unfold equivalent, model. rewrite union_raw, empty_raw, app_nil_r. reflexivity. Qed.
Lemma union_congruence q q' r r' : equivalent q q' -> equivalent r r' ->
  equivalent (PQ.union q r) (PQ.union q' r').
Proof. unfold equivalent. rewrite !union_model. now intros -> ->. Qed.

End Queue.

Section Functor.
Context {K : Type} `{GHC.Base.Ord K} (laws : PriorityOrderLaws) {A B : Type}.

Lemma fmap_raw (f : A -> B) (q : PQ.PQueue K A) :
  rawEntries (GHC.Base.fmap f q) = map (map_entry f) (rawEntries q).
Proof.
  destruct q as [t]. unfold rawEntries, treeEntries.
  change (map entryPair (contents
    (FT.fmap' (GHC.Base.fmap f) t : FT.FingerTree (PQ.Prio K B) (PQ.Entry K B))) =
    map (map_entry f) (map entryPair (contents t))).
  rewrite fmap'_contents, !map_map. apply map_ext. intros [k v]. reflexivity.
Qed.

Lemma fmap_valid (f : A -> B) (q : PQ.PQueue K A) : valid (GHC.Base.fmap f q).
Proof.
  destruct q as [t]. split; [exact laws |].
  apply fmap'_validity.
Qed.

Lemma fmap_model (f : A -> B) (q : PQ.PQueue K A) :
  model (GHC.Base.fmap f q) = map (map_entry f) (model q).
Proof. unfold model. rewrite fmap_raw. apply ordered_map_payload. Qed.

End Functor.

Section FunctorLaws.
Context {K : Type} `{GHC.Base.Ord K} {A B : Type}.

Lemma fmap_identity_model (q : PQ.PQueue K A) : equivalent (GHC.Base.fmap (fun x => x) q) q.
Proof.
  unfold equivalent. rewrite fmap_model. rewrite <- (map_id (model q)) at 2.
  apply map_ext. intros [k v]. reflexivity.
Qed.

Lemma fmap_composition_model {C} (f : A -> B) (g : B -> C) (q : PQ.PQueue K A) :
  equivalent (GHC.Base.fmap (fun x => g (f x)) q) (GHC.Base.fmap g (GHC.Base.fmap f q)).
Proof.
  unfold equivalent. rewrite !fmap_model, map_map. apply map_ext. intros [k v]. reflexivity.
Qed.

Lemma replace_model (b : B) (q : PQ.PQueue K A) :
  model (GHC.Base.op_zlzd__ b q) = map (map_entry (fun _ => b)) (model q).
Proof. apply fmap_model. Qed.

End FunctorLaws.

(* Laws on the supplied element dictionaries. These are parameters, not new
   instances. The pair/list bridges below prove the laws of the actual library
   comparisons, rather than postulating laws of a queue comparison. *)
Record ComparisonLaws {A : Type} (cmp : A -> A -> comparison) : Prop := {
  comparison_eq : forall x y, cmp x y = Eq <-> x = y;
  comparison_opposite : forall x y, cmp y x = CompOpp (cmp x y);
  comparison_lt_trans : forall x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt
}.

Lemma pair_comparison_laws {A B} `{GHC.Base.Ord A} `{GHC.Base.Ord B}
  (LA : ComparisonLaws (@GHC.Base.compare A _ _))
  (LB : ComparisonLaws (@GHC.Base.compare B _ _)) :
  ComparisonLaws (@GHC.Base.compare (A * B) _ _).
Proof.
  constructor.
  - intros [a b] [c d]. change ((match GHC.Base.compare a c with
      | Eq => GHC.Base.compare b d | Lt => Lt | Gt => Gt end) = Eq <-> (a,b) = (c,d)).
    destruct (GHC.Base.compare a c) eqn:Eac.
    + apply (comparison_eq LA) in Eac. subst c.
      rewrite (comparison_eq LB). split; intro E; [now subst | now inversion E].
    + split; [discriminate |]. intro E; injection E as Ea Eb. rewrite Ea in Eac.
      pose proof (proj2 (comparison_eq LA c c) eq_refl). congruence.
    + split; [discriminate |]. intro E; injection E as Ea Eb. rewrite Ea in Eac.
      pose proof (proj2 (comparison_eq LA c c) eq_refl). congruence.
  - intros [a b] [c d]. change (GHC.Base.compare_pair (c,d) (a,b) = CompOpp (GHC.Base.compare_pair (a,b) (c,d))).
    unfold GHC.Base.compare_pair. rewrite (comparison_opposite LA a c), (comparison_opposite LB b d).
    now destruct (GHC.Base.compare a c).
  - intros [a b] [c d] [e f]. change ((match GHC.Base.compare a c with
      | Eq => GHC.Base.compare b d | Lt => Lt | Gt => Gt end) = Lt ->
      (match GHC.Base.compare c e with | Eq => GHC.Base.compare d f | Lt => Lt | Gt => Gt end) = Lt ->
      (match GHC.Base.compare a e with | Eq => GHC.Base.compare b f | Lt => Lt | Gt => Gt end) = Lt).
    destruct (GHC.Base.compare a c) eqn:Eac; destruct (GHC.Base.compare c e) eqn:Ece;
      intros Ebd Edf; try discriminate.
    + apply (comparison_eq LA) in Eac, Ece. subst c e.
      rewrite (proj2 (comparison_eq LA a a) eq_refl).
      eapply comparison_lt_trans; eauto.
    + apply (comparison_eq LA) in Eac. subst c. now rewrite Ece.
    + apply (comparison_eq LA) in Ece. subst e. now rewrite Eac.
    + now rewrite (comparison_lt_trans LA a c e Eac Ece).
Qed.

Lemma list_comparison_laws {A} `{GHC.Base.Ord A}
  (LA : ComparisonLaws (@GHC.Base.compare A _ _)) :
  ComparisonLaws (@GHC.Base.compare (list A) _ _).
Proof.
  constructor.
  - intros xs. induction xs as [|x xs IH]; intros [|y ys]; cbn; try (split; discriminate); [tauto |].
    change ((match GHC.Base.compare x y with Eq => GHC.Base.compare_list xs ys | Lt => Lt | Gt => Gt end) = Eq <-> x :: xs = y :: ys).
    destruct (GHC.Base.compare x y) eqn:E.
    + apply (comparison_eq LA) in E. subst y.
      specialize (IH ys). change (GHC.Base.compare_list xs ys = Eq <-> xs = ys) in IH.
      rewrite IH. split; intro E; [now subst | now inversion E].
    + split; [discriminate |]. intro C; inversion C; subst y.
      pose proof (proj2 (comparison_eq LA x x) eq_refl). congruence.
    + split; [discriminate |]. intro C; inversion C; subst y.
      pose proof (proj2 (comparison_eq LA x x) eq_refl). congruence.
  - intros xs. induction xs as [|x xs IH]; intros [|y ys]; try reflexivity.
    change (GHC.Base.compare_list (y :: ys) (x :: xs) = CompOpp (GHC.Base.compare_list (x :: xs) (y :: ys))).
    cbn [GHC.Base.compare_list]. rewrite (comparison_opposite LA x y).
    destruct (GHC.Base.compare x y); [apply IH | reflexivity | reflexivity].
  - intros xs. induction xs as [|x xs IH]; intros [|y ys] [|z zs];
      cbn; intros E1 E2; try discriminate; try reflexivity.
    change (GHC.Base.compare_list (x :: xs) (z :: zs) = Lt).
    change ((match GHC.Base.compare x y with Eq => GHC.Base.compare_list xs ys | Lt => Lt | Gt => Gt end) = Lt) in E1.
    change ((match GHC.Base.compare y z with Eq => GHC.Base.compare_list ys zs | Lt => Lt | Gt => Gt end) = Lt) in E2.
    destruct (GHC.Base.compare x y) eqn:Exy; destruct (GHC.Base.compare y z) eqn:Eyz;
      try discriminate; cbn [GHC.Base.compare_list].
    + apply (comparison_eq LA) in Exy, Eyz. subst y z.
      rewrite (proj2 (comparison_eq LA x x) eq_refl). eapply IH; eauto.
    + apply (comparison_eq LA) in Exy. subst y. now rewrite Eyz.
    + apply (comparison_eq LA) in Eyz. subst z. now rewrite Exy.
    + now rewrite (comparison_lt_trans LA x y z Exy Eyz).
Qed.

Lemma list_equality_coherence {A} `{GHC.Base.Eq_ A}
  (EA : forall x y : A, GHC.Base.op_zeze__ x y = true <-> x = y) :
  forall xs ys : list A, GHC.Base.op_zeze__ xs ys = true <-> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys]; cbn; try (split; discriminate); [tauto |].
  change (andb (GHC.Base.op_zeze__ x y) (GHC.Base.eqlist xs ys) = true <-> x :: xs = y :: ys).
  rewrite andb_true_iff, EA. specialize (IH ys). change (GHC.Base.eqlist xs ys = true <-> xs = ys) in IH.
  rewrite IH. split; [intros [-> ->]; reflexivity | intro E; inversion E; auto].
Qed.

Section Comparison.
Context {K : Type} `{GHC.Base.Ord K} (laws : PriorityOrderLaws).
Context {V : Type} `{GHC.Base.Eq_ V}.

Lemma eq_model (q r : PQ.PQueue K V) : valid q -> valid r ->
  GHC.Base.op_zeze__ q r = GHC.Base.op_zeze__ (model q) (model r).
Proof.
  intros W U. change (GHC.Base.op_zeze__ (PQ.assocs q) (PQ.assocs r) = GHC.Base.op_zeze__ (model q) (model r)).
  now rewrite !assocs_model by assumption.
Qed.

Lemma neq_model (q r : PQ.PQueue K V) : valid q -> valid r ->
  GHC.Base.op_zsze__ q r = negb (GHC.Base.op_zeze__ (model q) (model r)).
Proof.
  intros W U. change (negb (GHC.Base.op_zeze__ q r) = negb (GHC.Base.op_zeze__ (model q) (model r))).
  now rewrite eq_model by assumption.
Qed.

Context (eqK : forall x y : K, GHC.Base.op_zeze__ x y = true <-> x = y).
Context (eqV : forall x y : V, GHC.Base.op_zeze__ x y = true <-> x = y).

Lemma entry_equality_coherence (a b : K * V) : GHC.Base.op_zeze__ a b = true <-> a = b.
Proof.
  destruct a as [a u], b as [b v]. change (andb (GHC.Base.op_zeze__ a b) (GHC.Base.op_zeze__ u v) = true <-> (a,u)=(b,v)).
  rewrite andb_true_iff, eqK, eqV. split; [intros [-> ->]; reflexivity | intro E; inversion E; auto].
Qed.

Lemma eq_equivalent (q r : PQ.PQueue K V) : valid q -> valid r ->
  (GHC.Base.op_zeze__ q r = true <-> equivalent q r).
Proof.
  intros W U. rewrite eq_model by assumption.
  apply list_equality_coherence. exact entry_equality_coherence.
Qed.

Lemma eq_reflexive (q : PQ.PQueue K V) : valid q -> GHC.Base.op_zeze__ q q = true.
Proof. intro W. apply (proj2 (eq_equivalent W W)). reflexivity. Qed.
Lemma eq_symmetric (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.op_zeze__ q r = GHC.Base.op_zeze__ r q.
Proof.
  intros W U. destruct (GHC.Base.op_zeze__ q r) eqn:E, (GHC.Base.op_zeze__ r q) eqn:F; try reflexivity.
  - apply (proj1 (eq_equivalent W U)) in E.
    assert (GHC.Base.op_zeze__ r q = true).
    { apply (proj2 (eq_equivalent U W)). symmetry. exact E. } congruence.
  - apply (proj1 (eq_equivalent U W)) in F.
    assert (GHC.Base.op_zeze__ q r = true).
    { apply (proj2 (eq_equivalent W U)). symmetry. exact F. } congruence.
Qed.
Lemma eq_transitive (q r s : PQ.PQueue K V) : valid q -> valid r -> valid s ->
  GHC.Base.op_zeze__ q r = true -> GHC.Base.op_zeze__ r s = true -> GHC.Base.op_zeze__ q s = true.
Proof.
  intros W U T E F. apply (proj2 (eq_equivalent W T)).
  apply (proj1 (eq_equivalent W U)) in E. apply (proj1 (eq_equivalent U T)) in F.
  unfold equivalent in *. congruence.
Qed.

End Comparison.

Lemma comparison_not_gt_trans {A} (cmp : A -> A -> comparison) (L : ComparisonLaws cmp) x y z :
  cmp x y <> Gt -> cmp y z <> Gt -> cmp x z <> Gt.
Proof.
  intros E F. destruct (cmp x y) eqn:Cxy; [| |contradiction].
  - apply (comparison_eq L) in Cxy. now subst y.
  - destruct (cmp y z) eqn:Cyz; [| |contradiction].
    + apply (comparison_eq L) in Cyz. subst z. congruence.
    + rewrite (comparison_lt_trans L x y z Cxy Cyz). discriminate.
Qed.

Section QueueOrd.
Context {K : Type} `{GHC.Base.Ord K} (laws : PriorityOrderLaws).
Context {V : Type} `{GHC.Base.Ord V}.

Lemma compare_model (q r : PQ.PQueue K V) : valid q -> valid r ->
  GHC.Base.compare q r = GHC.Base.compare (model q) (model r).
Proof.
  intros W U. change (GHC.Base.compare (PQ.assocs q) (PQ.assocs r) = GHC.Base.compare (model q) (model r)).
  now rewrite !assocs_model by assumption.
Qed.

Lemma lt_behavior (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.op_zl__ q r =
  GHC.Base.eq_comparison (GHC.Base.compare (model q) (model r)) Lt.
Proof. intros W U. change (GHC.Base.op_zl__ q r) with (GHC.Base.eq_comparison (GHC.Base.compare q r) Lt).
  now rewrite compare_model by assumption. Qed.
Lemma le_behavior (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.op_zlze__ q r =
  negb (GHC.Base.eq_comparison (GHC.Base.compare (model q) (model r)) Gt).
Proof. intros W U. change (GHC.Base.op_zlze__ q r) with (negb (GHC.Base.eq_comparison (GHC.Base.compare q r) Gt)).
  now rewrite compare_model by assumption. Qed.
Lemma gt_behavior (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.op_zg__ q r =
  GHC.Base.eq_comparison (GHC.Base.compare (model q) (model r)) Gt.
Proof. intros W U. change (GHC.Base.op_zg__ q r) with (GHC.Base.eq_comparison (GHC.Base.compare q r) Gt).
  now rewrite compare_model by assumption. Qed.
Lemma ge_behavior (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.op_zgze__ q r =
  negb (GHC.Base.eq_comparison (GHC.Base.compare (model q) (model r)) Lt).
Proof. intros W U. change (GHC.Base.op_zgze__ q r) with (negb (GHC.Base.eq_comparison (GHC.Base.compare q r) Lt)).
  now rewrite compare_model by assumption. Qed.

Lemma min_model (q r : PQ.PQueue K V) : valid q -> valid r -> model (GHC.Base.min q r) =
  match GHC.Base.compare (model q) (model r) with Gt => model r | _ => model q end.
Proof.
  intros W U. change (GHC.Base.min q r) with (if GHC.Base.op_zlze__ q r then q else r).
  rewrite le_behavior by assumption. now destruct (GHC.Base.compare (model q) (model r)).
Qed.
Lemma max_model (q r : PQ.PQueue K V) : valid q -> valid r -> model (GHC.Base.max q r) =
  match GHC.Base.compare (model q) (model r) with Gt => model q | _ => model r end.
Proof.
  intros W U. change (GHC.Base.max q r) with (if GHC.Base.op_zlze__ q r then r else q).
  rewrite le_behavior by assumption. now destruct (GHC.Base.compare (model q) (model r)).
Qed.
Lemma min_valid (q r : PQ.PQueue K V) : valid q -> valid r -> valid (GHC.Base.min q r).
Proof. intros W U. change (valid (if GHC.Base.op_zlze__ q r then q else r)). now destruct (GHC.Base.op_zlze__ q r). Qed.
Lemma max_valid (q r : PQ.PQueue K V) : valid q -> valid r -> valid (GHC.Base.max q r).
Proof. intros W U. change (valid (if GHC.Base.op_zlze__ q r then r else q)). now destruct (GHC.Base.op_zlze__ q r). Qed.

Context (ordK : ComparisonLaws (@GHC.Base.compare K _ _)).
Context (ordV : ComparisonLaws (@GHC.Base.compare V _ _)).

Lemma model_comparison_laws : ComparisonLaws (@GHC.Base.compare (list (K * V)) _ _).
Proof. apply list_comparison_laws, pair_comparison_laws; assumption. Qed.

Lemma compare_equal_equivalent (q r : PQ.PQueue K V) : valid q -> valid r ->
  (GHC.Base.compare q r = Eq <-> equivalent q r).
Proof. intros W U. rewrite compare_model by assumption. apply (comparison_eq model_comparison_laws). Qed.

Lemma compare_reflexive (q : PQ.PQueue K V) : valid q -> GHC.Base.compare q q = Eq.
Proof. intro W. apply (proj2 (compare_equal_equivalent W W)). reflexivity. Qed.

Lemma compare_opposite (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.compare r q = CompOpp (GHC.Base.compare q r).
Proof. intros W U. rewrite !compare_model by assumption. apply (comparison_opposite model_comparison_laws). Qed.

Lemma compare_less_transitive (q r s : PQ.PQueue K V) : valid q -> valid r -> valid s ->
  GHC.Base.compare q r = Lt -> GHC.Base.compare r s = Lt -> GHC.Base.compare q s = Lt.
Proof.
  intros W U T. rewrite !compare_model by assumption. apply (comparison_lt_trans model_comparison_laws).
Qed.

Lemma le_iff (q r : PQ.PQueue K V) : valid q -> valid r ->
  (GHC.Base.op_zlze__ q r = true <-> GHC.Base.compare (model q) (model r) <> Gt).
Proof. intros W U. rewrite le_behavior by assumption.
  destruct (GHC.Base.compare (model q) (model r)); cbn; intuition discriminate. Qed.

Lemma le_reflexive (q : PQ.PQueue K V) : valid q -> GHC.Base.op_zlze__ q q = true.
Proof. intro W. apply (proj2 (le_iff W W)).
  rewrite (proj2 (comparison_eq model_comparison_laws _ _) eq_refl). discriminate. Qed.

Lemma le_total (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.op_zlze__ q r = true \/ GHC.Base.op_zlze__ r q = true.
Proof.
  intros W U. destruct (GHC.Base.compare (model q) (model r)) eqn:E.
  - left. apply (proj2 (le_iff W U)). congruence.
  - left. apply (proj2 (le_iff W U)). congruence.
  - right. apply (proj2 (le_iff U W)). rewrite (comparison_opposite model_comparison_laws _ _), E. discriminate.
Qed.

Lemma le_transitive (q r s : PQ.PQueue K V) : valid q -> valid r -> valid s ->
  GHC.Base.op_zlze__ q r = true -> GHC.Base.op_zlze__ r s = true -> GHC.Base.op_zlze__ q s = true.
Proof.
  intros W U T E F. apply (proj2 (le_iff W T)).
  apply (proj1 (le_iff W U)) in E. apply (proj1 (le_iff U T)) in F.
  eapply comparison_not_gt_trans; [exact model_comparison_laws |exact E |exact F].
Qed.

Lemma le_antisymmetric (q r : PQ.PQueue K V) : valid q -> valid r ->
  GHC.Base.op_zlze__ q r = true -> GHC.Base.op_zlze__ r q = true -> equivalent q r.
Proof.
  intros W U E F. apply (proj1 (le_iff W U)) in E. apply (proj1 (le_iff U W)) in F.
  unfold equivalent. apply (comparison_eq model_comparison_laws).
  rewrite (comparison_opposite model_comparison_laws _ _) in F.
  destruct (GHC.Base.compare (model q) (model r)); cbn in *; congruence.
Qed.

Lemma lt_model (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.op_zl__ q r = GHC.Base.op_zl__ (model q) (model r).
Proof. apply lt_behavior. Qed.
Lemma le_model (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.op_zlze__ q r = GHC.Base.op_zlze__ (model q) (model r).
Proof.
  intros W U. rewrite le_behavior by assumption.
  change (negb (GHC.Base.eq_comparison (GHC.Base.compare (model q) (model r)) Gt) =
    negb (GHC.Base.eq_comparison (GHC.Base.compare (model r) (model q)) Lt)).
  rewrite (comparison_opposite model_comparison_laws (model q) (model r)).
  now destruct (GHC.Base.compare (model q) (model r)).
Qed.
Lemma gt_model (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.op_zg__ q r = GHC.Base.op_zg__ (model q) (model r).
Proof.
  intros W U. rewrite gt_behavior by assumption.
  change (GHC.Base.eq_comparison (GHC.Base.compare (model q) (model r)) Gt =
    GHC.Base.eq_comparison (GHC.Base.compare (model r) (model q)) Lt).
  rewrite (comparison_opposite model_comparison_laws (model q) (model r)).
  now destruct (GHC.Base.compare (model q) (model r)).
Qed.
Lemma ge_model (q r : PQ.PQueue K V) : valid q -> valid r -> GHC.Base.op_zgze__ q r = GHC.Base.op_zgze__ (model q) (model r).
Proof. apply ge_behavior. Qed.

End QueueOrd.

Section Observations.
Context {K : Type} `{GHC.Base.Ord K} (laws : PriorityOrderLaws) {V : Type}.

Lemma minViewWithKey_none_null (q : PQ.PQueue K V) : valid q ->
  (PQ.minViewWithKey q = None <-> PQ.null q = true).
Proof. intro W. rewrite (minViewWithKey_none laws W), null_model. reflexivity. Qed.
Lemma minView_none_null (q : PQ.PQueue K V) : valid q ->
  (PQ.minView q = None <-> PQ.null q = true).
Proof. intro W. rewrite (minView_none laws W), null_model. reflexivity. Qed.

Lemma default_behavior : @HsToRocq.Err.default (PQ.PQueue K V) PQ.DefaultPQueue = PQ.empty.
Proof. reflexivity. Qed.
Lemma default_valid : valid (@HsToRocq.Err.default (PQ.PQueue K V) PQ.DefaultPQueue).
Proof. apply empty_valid; exact laws. Qed.

Lemma length_model (q : PQ.PQueue K V) : valid q ->
  Data.Foldable.length q = Z.of_nat (Datatypes.length (model q)).
Proof.
  intro W. rewrite (length_fold_model laws W).
  change (fold_left (fun acc (_ : K * V) => (acc + 1)%Z) (model q) 0%Z = Z.of_nat (Datatypes.length (model q))).
  assert (C : forall xs (z : Z), fold_left (fun acc (_ : K * V) => (acc + 1)%Z) xs z =
    (z + Z.of_nat (Datatypes.length xs))%Z).
  { induction xs; intros z; cbn [fold_left Datatypes.length];
      [cbn; lia | rewrite IHxs, Nat2Z.inj_succ; lia]. }
  rewrite C. lia.
Qed.

Lemma product_model `{GHC.Num.Num V} (q : PQ.PQueue K V) : valid q ->
  Data.Foldable.product q =
  fold_left (fun acc e => GHC.Num.op_zt__ acc (snd e)) (model q)
    (GHC.Num.fromInteger (BinNums.Zpos BinNums.xH)).
Proof.
  intro W. rewrite (product_fold_model laws W).
  assert (C : forall xs (z : V), Data.SemigroupInternal.getProduct
    (fold_left (fun acc (e : K * V) => GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Product (snd e)))
      xs (Data.SemigroupInternal.Mk_Product z)) =
    fold_left (fun acc e => GHC.Num.op_zt__ acc (snd e)) xs z).
  { induction xs; intros; cbn [fold_left]; [reflexivity | apply IHxs]. }
  apply C.
Qed.

Lemma sum_model `{GHC.Num.Num V} (q : PQ.PQueue K V) : valid q ->
  Data.Foldable.sum q =
  fold_left (fun acc e => GHC.Num.op_zp__ acc (snd e)) (model q)
    (GHC.Num.fromInteger BinNums.Z0).
Proof.
  intro W. rewrite (sum_fold_model laws W).
  assert (C : forall xs (z : V), Data.SemigroupInternal.getSum
    (fold_left (fun acc (e : K * V) => GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Sum (snd e)))
      xs (Data.SemigroupInternal.Mk_Sum z)) =
    fold_left (fun acc e => GHC.Num.op_zp__ acc (snd e)) xs z).
  { induction xs; intros; cbn [fold_left]; [reflexivity | apply IHxs]. }
  apply C.
Qed.

Lemma foldMap_strict_agrees {R} `{GHC.Base.Monoid R}
  (consistent : forall x y : R, GHC.Base.op_zlzlzgzg__ x y = GHC.Base.mappend x y)
  (assocR : forall x y z : R, GHC.Base.mappend (GHC.Base.mappend x y) z = GHC.Base.mappend x (GHC.Base.mappend y z))
  (leftR : forall x : R, GHC.Base.mappend GHC.Base.mempty x = x)
  (rightR : forall x : R, GHC.Base.mappend x GHC.Base.mempty = x)
  (f : V -> R) (q : PQ.PQueue K V) : valid q ->
  Data.Foldable.foldMap' f q = Data.Foldable.foldMap f q.
Proof.
  intro W. rewrite (foldMap_strict_model laws f W), (foldMap_model laws f W).
  assert (C : forall xs acc,
    fold_left (fun acc (e : K * V) => GHC.Base.op_zlzlzgzg__ acc (f (snd e))) xs acc =
    GHC.Base.mappend acc (fold_right (fun e r => GHC.Base.mappend (f (snd e)) r) GHC.Base.mempty xs)).
  { induction xs; cbn [fold_left fold_right]; intros.
    - symmetry. apply rightR.
    - rewrite IHxs, consistent, assocR. reflexivity. }
  rewrite C, leftR. reflexivity.
Qed.

End Observations.

Section PublicObservations.
Context {K : Type} `{GHC.Base.Ord K} (laws : PriorityOrderLaws) {V : Type}.

Lemma minViewWithKey_model (q : PQ.PQueue K V) : valid q ->
  option_map (fun '(e,q') => (e,model q')) (PQ.minViewWithKey q) =
  match model q with [] => None | e :: rest => Some (e,rest) end.
Proof.
  intro W. pose proof (minViewWithKey_correct laws W) as C.
  unfold extractionSpec in C. destruct (PQ.minViewWithKey q) as [[e q']|].
  - destruct C as [_ [Co _]]. now rewrite Co.
  - now rewrite C.
Qed.

Lemma minView_model (q : PQ.PQueue K V) : valid q ->
  option_map (fun '(v,q') => (v,model q')) (PQ.minView q) =
  match model q with [] => None | (_,v) :: rest => Some (v,rest) end.
Proof.
  intro W. pose proof (minView_correct laws W) as C.
  destruct (PQ.minView q) as [[v q']|].
  - destruct C as [_ [[k Co] _]]. now rewrite Co.
  - now rewrite C.
Qed.

Lemma unfoldr_valid_eq (q : PQ.PQueue K V) : valid q ->
  Data.OldList.unfoldr PQ.minViewWithKey q =
    match PQ.minViewWithKey q with
    | None => []
    | Some (e,q') => e :: Data.OldList.unfoldr PQ.minViewWithKey q'
    end.
Proof. apply assocs_unfold; exact laws. Qed.

Lemma unfoldr_valid_model (q : PQ.PQueue K V) : valid q ->
  Data.OldList.unfoldr PQ.minViewWithKey q = model q.
Proof. apply assocs_model; exact laws. Qed.

End PublicObservations.

Section CoherentEqualityOrder.
Context {K : Type} `{GHC.Base.Ord K} (laws : PriorityOrderLaws).
Context {V : Type} `{GHC.Base.Ord V}.
Context (eqK : forall x y : K, GHC.Base.op_zeze__ x y = true <-> x = y).
Context (eqV : forall x y : V, GHC.Base.op_zeze__ x y = true <-> x = y).
Context (ordK : ComparisonLaws (@GHC.Base.compare K _ _)).
Context (ordV : ComparisonLaws (@GHC.Base.compare V _ _)).

Lemma compare_eq_boolean (q r : PQ.PQueue K V) : valid q -> valid r ->
  (GHC.Base.compare q r = Eq <-> GHC.Base.op_zeze__ q r = true).
Proof.
  intros W U. rewrite (compare_equal_equivalent laws ordK ordV W U), (eq_equivalent laws eqK eqV W U).
  reflexivity.
Qed.

End CoherentEqualityOrder.

Lemma add_model_ordered {K : Type} `{GHC.Base.Ord K} (laws : PriorityOrderLaws)
  {V : Type} k v (q : PQ.PQueue K V) :
  model (PQ.add k v q) = ordered (model q ++ [(k,v)]).
Proof.
  rewrite add_model. unfold model. symmetry. apply ordered_normalize_left; exact laws.
Qed.

(* Complete exported API/assumption inventory. Closed reports retain explicit
   law hypotheses in their types. Recursive correctness uses precisely the
   authorized deferredFix and guarded deferredFix_eq_on interface. *)
Check @entryPair. Print Assumptions entryPair.
Check @treeEntries. Print Assumptions treeEntries.
Check @rawEntries. Print Assumptions rawEntries.
Check @valid. Print Assumptions valid.
Check @model. Print Assumptions model.
Check @prio_assoc. Print Assumptions prio_assoc.
Check @prio_left_id. Print Assumptions prio_left_id.
Check @prio_right_id. Print Assumptions prio_right_id.
Check @listMeasure_pairs. Print Assumptions listMeasure_pairs.
Check @measure_entries. Print Assumptions measure_entries.
Check @empty_raw. Print Assumptions empty_raw.
Check @singleton_raw. Print Assumptions singleton_raw.
Check @insert_raw. Print Assumptions insert_raw.
Check @add_raw. Print Assumptions add_raw.
Check @union_raw. Print Assumptions union_raw.
Check @fromList_raw. Print Assumptions fromList_raw.
Check @empty_valid. Print Assumptions empty_valid.
Check @singleton_valid. Print Assumptions singleton_valid.
Check @insert_valid. Print Assumptions insert_valid.
Check @add_valid. Print Assumptions add_valid.
Check @union_valid. Print Assumptions union_valid.
Check @fromList_valid. Print Assumptions fromList_valid.
Check @empty_model. Print Assumptions empty_model.
Check @singleton_model. Print Assumptions singleton_model.
Check @insert_model. Print Assumptions insert_model.
Check @add_model. Print Assumptions add_model.
Check @add_model_ordered. Print Assumptions add_model_ordered.
Check @union_model. Print Assumptions union_model.
Check @fromList_model. Print Assumptions fromList_model.
Check @null_model. Print Assumptions null_model.
Check @insert_ties. Print Assumptions insert_ties.
Check @add_ties. Print Assumptions add_ties.
Check @union_ties. Print Assumptions union_ties.
Check @fromList_ties. Print Assumptions fromList_ties.
Check @winner_at_cut. Print Assumptions winner_at_cut.
Check @minViewWithKey_nonempty. Print Assumptions minViewWithKey_nonempty.
Check @extractionSpec. Print Assumptions extractionSpec.
Check @minViewWithKey_correct. Print Assumptions minViewWithKey_correct.
Check @minViewWithKey_some. Print Assumptions minViewWithKey_some.
Check @minViewWithKey_none. Print Assumptions minViewWithKey_none.
Check @minView_correct. Print Assumptions minView_correct.
Check @minView_some. Print Assumptions minView_some.
Check @minView_none. Print Assumptions minView_none.
Check @extractionStep. Print Assumptions extractionStep.
Check @extraction_well_founded. Print Assumptions extraction_well_founded.
Check @assocsBody. Print Assumptions assocsBody.
Check @assocs_definition. Print Assumptions assocs_definition.
Check @assocs_recurses_on. Print Assumptions assocs_recurses_on.
Check @assocs_unfold. Print Assumptions assocs_unfold.
Check @assocs_model. Print Assumptions assocs_model.
Check @foldMapBody. Print Assumptions foldMapBody.
Check @foldMap_definition. Print Assumptions foldMap_definition.
Check @foldMap_recurses_on. Print Assumptions foldMap_recurses_on.
Check @foldMap_unfold. Print Assumptions foldMap_unfold.
Check @foldMap_model. Print Assumptions foldMap_model.
Check @foldr_model. Print Assumptions foldr_model.
Check @foldl_model. Print Assumptions foldl_model.
Check @foldl_strict_model. Print Assumptions foldl_strict_model.
Check @foldr_strict_model. Print Assumptions foldr_strict_model.
Check @toList_model. Print Assumptions toList_model.
Check @foldable_null_model. Print Assumptions foldable_null_model.
Check @foldMap_strict_model. Print Assumptions foldMap_strict_model.
Check @fold_behavior. Print Assumptions fold_behavior.
Check @length_fold_model. Print Assumptions length_fold_model.
Check @product_fold_model. Print Assumptions product_fold_model.
Check @sum_fold_model. Print Assumptions sum_fold_model.
Check @equivalent. Print Assumptions equivalent.
Check @equivalent_equivalence. Print Assumptions equivalent_equivalence.
Check @semigroup_behavior. Print Assumptions semigroup_behavior.
Check @monoid_append_behavior. Print Assumptions monoid_append_behavior.
Check @monoid_empty_behavior. Print Assumptions monoid_empty_behavior.
Check @monoid_concat_raw. Print Assumptions monoid_concat_raw.
Check @monoid_concat_valid. Print Assumptions monoid_concat_valid.
Check @monoid_concat_model. Print Assumptions monoid_concat_model.
Check @union_associative. Print Assumptions union_associative.
Check @union_left_identity. Print Assumptions union_left_identity.
Check @union_right_identity. Print Assumptions union_right_identity.
Check @union_congruence. Print Assumptions union_congruence.
Check @fmap_raw. Print Assumptions fmap_raw.
Check @fmap_valid. Print Assumptions fmap_valid.
Check @fmap_model. Print Assumptions fmap_model.
Check @fmap_identity_model. Print Assumptions fmap_identity_model.
Check @fmap_composition_model. Print Assumptions fmap_composition_model.
Check @replace_model. Print Assumptions replace_model.
Check @ComparisonLaws. Print Assumptions ComparisonLaws.
Check @Build_ComparisonLaws. Print Assumptions Build_ComparisonLaws.
Check @comparison_eq. Print Assumptions comparison_eq.
Check @comparison_opposite. Print Assumptions comparison_opposite.
Check @comparison_lt_trans. Print Assumptions comparison_lt_trans.
Check @pair_comparison_laws. Print Assumptions pair_comparison_laws.
Check @list_comparison_laws. Print Assumptions list_comparison_laws.
Check @list_equality_coherence. Print Assumptions list_equality_coherence.
Check @eq_model. Print Assumptions eq_model.
Check @neq_model. Print Assumptions neq_model.
Check @entry_equality_coherence. Print Assumptions entry_equality_coherence.
Check @eq_equivalent. Print Assumptions eq_equivalent.
Check @eq_reflexive. Print Assumptions eq_reflexive.
Check @eq_symmetric. Print Assumptions eq_symmetric.
Check @eq_transitive. Print Assumptions eq_transitive.
Check @comparison_not_gt_trans. Print Assumptions comparison_not_gt_trans.
Check @compare_model. Print Assumptions compare_model.
Check @lt_behavior. Print Assumptions lt_behavior.
Check @le_behavior. Print Assumptions le_behavior.
Check @gt_behavior. Print Assumptions gt_behavior.
Check @ge_behavior. Print Assumptions ge_behavior.
Check @min_model. Print Assumptions min_model.
Check @max_model. Print Assumptions max_model.
Check @min_valid. Print Assumptions min_valid.
Check @max_valid. Print Assumptions max_valid.
Check @model_comparison_laws. Print Assumptions model_comparison_laws.
Check @compare_equal_equivalent. Print Assumptions compare_equal_equivalent.
Check @compare_reflexive. Print Assumptions compare_reflexive.
Check @compare_opposite. Print Assumptions compare_opposite.
Check @compare_less_transitive. Print Assumptions compare_less_transitive.
Check @le_iff. Print Assumptions le_iff.
Check @le_reflexive. Print Assumptions le_reflexive.
Check @le_total. Print Assumptions le_total.
Check @le_transitive. Print Assumptions le_transitive.
Check @le_antisymmetric. Print Assumptions le_antisymmetric.
Check @lt_model. Print Assumptions lt_model.
Check @le_model. Print Assumptions le_model.
Check @gt_model. Print Assumptions gt_model.
Check @ge_model. Print Assumptions ge_model.
Check @minViewWithKey_none_null. Print Assumptions minViewWithKey_none_null.
Check @minView_none_null. Print Assumptions minView_none_null.
Check @default_behavior. Print Assumptions default_behavior.
Check @default_valid. Print Assumptions default_valid.
Check @length_model. Print Assumptions length_model.
Check @product_model. Print Assumptions product_model.
Check @sum_model. Print Assumptions sum_model.
Check @foldMap_strict_agrees. Print Assumptions foldMap_strict_agrees.
Check @minViewWithKey_model. Print Assumptions minViewWithKey_model.
Check @minView_model. Print Assumptions minView_model.
Check @unfoldr_valid_eq. Print Assumptions unfoldr_valid_eq.
Check @unfoldr_valid_model. Print Assumptions unfoldr_valid_model.
Check @compare_eq_boolean. Print Assumptions compare_eq_boolean.
