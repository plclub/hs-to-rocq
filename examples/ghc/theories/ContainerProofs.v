(* Properties of the translated IntMap operations. Structural invariants are
   explicit: semantic equality is not an invariant of arbitrary raw trees. *)
From Coq Require Import ssreflect ssrfun ssrbool NArith Lia Program.Equality.
Require Import GHC.Base Proofs.Prelude Data.IntMap.Internal.
Require IntMap IntMapProofs IntMapRecursion IntMapUnionProofs.
Require Import DyadicIntervals MapProofs.Bounds IntSetProofs.
Set Bullet Behavior "Strict Subproofs".

Local Lemma Eq_refl_Word (x : GHC.Num.Word) : (x == x) = true.
Proof. apply N.eqb_refl. Qed.

Lemma null_empty : forall A, (@Data.IntMap.Internal.null A empty).
Proof. reflexivity. Qed.
Lemma lookup_eq : forall A k k' (i : IntMap.IntMap A),
  k == k' -> lookup k i = lookup k' i.
Proof. intros A k k' i. move => /Eq_eq_Word ->. reflexivity. Qed.
Lemma member_eq : forall A k k' (i : IntMap.IntMap A),
  k == k' -> member k i = member k' i.
Proof. intros A k k' i. move => /Eq_eq_Word ->. reflexivity. Qed.
Lemma member_singleton : forall A k k' (v : A),
  member k (singleton k' v) = (k == k').
Proof. reflexivity. Qed.
Lemma lookup_singleton_key : forall {A} x y (a b : A),
  lookup x (singleton y a) = Some b -> x == y.
Proof. intros A x y a b. simpl. destruct (x == y); congruence. Qed.
Lemma lookup_singleton_val : forall {A} x y (a b : A),
  lookup x (singleton y a) = Some b -> a = b.
Proof. intros A x y a b. simpl. destruct (x == y); congruence. Qed.
Local Lemma lookup_link_self : forall A key (val : A) p2 t2,
  lookup key (link key (Tip key val) p2 t2) = Some val.
Proof.
  intros. unfold link, linkWithMask.
  destruct (Data.IntSet.Internal.zero key (branchMask key p2)) eqn:Hz;
    simpl; rewrite Hz Eq_refl_Word; reflexivity.
Qed.
Lemma lookup_insert : forall A key (val:A) i,
  lookup key (insert key val i) = Some val.
Proof.
  intros A key val. induction i as [p m l IHl r IHr | ky vy | ].
  - simpl. destruct (nomatch key p m).
    + apply lookup_link_self.
    + destruct (Data.IntSet.Internal.zero key m) eqn:Hz; simpl; rewrite Hz; auto.
  - simpl. destruct (key == ky).
    + simpl. rewrite Eq_refl_Word. reflexivity.
    + apply lookup_link_self.
  - simpl. rewrite Eq_refl_Word. reflexivity.
Qed.

(* Guarded equations hold on raw trees too; these boundary cases need no WF. *)
Lemma difference_nil_l : forall B A (i : IntMap.IntMap A),
  difference (@empty B) i = (@empty B).
Proof. intros. apply IntMapUnionProofs.difference_Nil_l. Qed.
Lemma difference_nil_r : forall A B (i : IntMap.IntMap A),
  difference i (@empty B) = i.
Proof. intros. apply IntMapUnionProofs.difference_Nil_r. Qed.
Lemma disjoint_empty_l : forall A B (j : IntMap.IntMap B),
  disjoint (@empty A) j = true.
Proof. intros. rewrite IntMapRecursion.disjoint_eq. reflexivity. Qed.
Lemma disjoint_empty_r : forall A B (i : IntMap.IntMap A),
  disjoint i (@empty B) = true.
Proof. intros. rewrite IntMapRecursion.disjoint_eq. destruct i; reflexivity. Qed.
Lemma intersection_empty : forall A B (i : IntMap.IntMap A) (j : IntMap.IntMap B),
  j = empty -> Data.IntMap.Internal.null (intersection i j).
Proof.
  intros A B i j ->. unfold intersection.
  rewrite IntMapRecursion.mergeWithKey'_eq. destruct i; reflexivity.
Qed.

Lemma non_member_lookup : forall A key (i : IntMap.IntMap A),
  IntMapProofs.WF i -> (member key i = false <-> lookup key i = None).
Proof.
  intros A key i [f S].
  rewrite (IntMapProofs.lookup_Sem S) (IntMapProofs.member_Sem S).
  destruct (f key); split; intro H; try discriminate; reflexivity.
Qed.
Lemma member_lookup : forall A key (i : IntMap.IntMap A),
  IntMapProofs.WF i -> (is_true (member key i) <-> exists val, lookup key i = Some val).
Proof.
  intros A key i [f S].
  rewrite (IntMapProofs.lookup_Sem S) (IntMapProofs.member_Sem S).
  destruct (f key) as [v|]; split; try discriminate; eauto.
  intros [v H]. discriminate.
Qed.
Lemma member_lookup_some : forall A k (m : IntMap.IntMap A),
  member k m = true -> exists v, lookup k m = Some v.
Proof.
  intros A k m. induction m as [p m l IHl r IHr | k' v' | ]; simpl.
  - destruct (nomatch k p m); [discriminate|].
    destruct (Data.IntSet.Internal.zero k m); assumption.
  - intro H. rewrite H. eauto.
  - discriminate.
Qed.
Lemma null_member : forall A (m : IntMap.IntMap A),
  IntMapProofs.WF m -> (Data.IntMap.Internal.null m = true <-> forall k, member k m = false).
Proof.
  intros A m [f S]. rewrite (IntMapProofs.null_Sem S). split.
  - intros H k. rewrite (IntMapProofs.member_Sem S) H. reflexivity.
  - intros H k. specialize (H k). rewrite (IntMapProofs.member_Sem S) in H.
    destruct (f k); [discriminate | reflexivity].
Qed.
Local Lemma member_isSome : forall A k (m : IntMap.IntMap A),
  IntMapProofs.WF m -> member k m = isSome (lookup k m).
Proof.
  intros A k m [f S].
  rewrite (IntMapProofs.member_Sem S) (IntMapProofs.lookup_Sem S). reflexivity.
Qed.
Lemma lookup_insert_neq : forall b key1 key2 (val:b) m,
  IntMapProofs.WF m -> key1 <> key2 ->
  lookup key1 (insert key2 val m) = lookup key1 m.
Proof.
  intros b key1 key2 val m [f S] Hne.
  pose proof (IntMapProofs.insert_Sem _ key2 val m f _ S (fun i => eq_refl)) as T.
  rewrite (IntMapProofs.lookup_Sem T) (IntMapProofs.lookup_Sem S).
  destruct (N.eqb_spec key1 key2); congruence.
Qed.
Lemma member_insert : forall A k k' v (i : IntMap.IntMap A),
  IntMapProofs.WF i -> member k (insert k' v i) = (k == k') || member k i.
Proof.
  intros A k k' v i [f S].
  pose proof (IntMapProofs.insert_Sem _ k' v i f _ S (fun j => eq_refl)) as T.
  rewrite (IntMapProofs.member_Sem T) (IntMapProofs.member_Sem S).
  change (k == k') with ((k =? k')%N). destruct (k =? k')%N; reflexivity.
Qed.

Local Lemma lookup_delete : forall A k k' (m : IntMap.IntMap A),
  IntMapProofs.WF m -> lookup k (delete k' m) = if (k =? k')%N then None else lookup k m.
Proof.
  intros A k k' m [f S].
  pose proof (IntMapProofs.delete_Sem k' m f _ S (fun j => eq_refl)) as T.
  rewrite (IntMapProofs.lookup_Sem T) (IntMapProofs.lookup_Sem S). reflexivity.
Qed.
Lemma delete_eq : forall key b (i : IntMap.IntMap b),
  IntMapProofs.WF i -> lookup key (delete key i) = None.
Proof. intros key b i W. rewrite (lookup_delete _ _ _ _ W) N.eqb_refl. reflexivity. Qed.
Lemma delete_neq : forall key1 key2 b (i : IntMap.IntMap b),
  IntMapProofs.WF i -> key1 <> key2 -> lookup key1 (delete key2 i) = lookup key1 i.
Proof.
  intros key1 key2 b i W H. rewrite (lookup_delete _ _ _ _ W).
  destruct (N.eqb_spec key1 key2); congruence.
Qed.
Lemma member_delete : forall A k k' (m : IntMap.IntMap A),
  IntMapProofs.WF m -> member k (delete k' m) = negb (k == k') && member k m.
Proof.
  intros A k k' m W.
  rewrite (member_isSome _ _ _ (IntMapProofs.delete_WF _ _ W)).
  rewrite (lookup_delete _ _ _ _ W) (member_isSome _ _ _ W).
  change (k == k') with ((k =? k')%N). destruct (k =? k')%N; reflexivity.
Qed.
Lemma member_delete_neq : forall k1 k2 b (i : IntMap.IntMap b),
  IntMapProofs.WF i -> k1 <> k2 -> member k2 (delete k1 i) = member k2 i.
Proof.
  intros k1 k2 b i W H. rewrite (member_delete _ _ _ _ W).
  change (k2 == k1) with ((k2 =? k1)%N).
  destruct (N.eqb_spec k2 k1); [congruence | reflexivity].
Qed.

Local Lemma lookup_filter : forall A (p : A -> bool) k (m : IntMap.IntMap A),
  IntMapProofs.WF m -> lookup k (Data.IntMap.Internal.filter p m) =
    match lookup k m with Some v => if p v then Some v else None | None => None end.
Proof.
  intros A p k m [f S].
  pose proof (IntMapProofs.filter_Sem p m f _ S (fun j => eq_refl)) as T.
  rewrite (IntMapProofs.lookup_Sem T) (IntMapProofs.lookup_Sem S). reflexivity.
Qed.
Lemma lookup_filter_Some : forall A (p : A -> bool) key val (m : IntMap.IntMap A),
  IntMapProofs.WF m -> lookup key (Data.IntMap.Internal.filter p m) = Some val ->
  p val = true /\ lookup key m = Some val.
Proof.
  intros A p key val m W. rewrite (lookup_filter _ _ _ _ W).
  destruct (lookup key m) as [v|]; [destruct (p v) eqn:P|]; try discriminate.
  intro H. inversion H; subst. auto.
Qed.
Lemma member_filter : forall A (p : A -> bool) key val (m : IntMap.IntMap A),
  IntMapProofs.WF m -> lookup key m = Some val -> p val = true ->
  member key (Data.IntMap.Internal.filter p m) = true.
Proof.
  intros A p key val m W H P.
  rewrite (member_isSome _ _ _ (IntMapProofs.filter_WF _ _ W)).
  rewrite (lookup_filter _ _ _ _ W) H P. reflexivity.
Qed.

(* Equality of WF maps follows from semantic uniqueness, not raw extensionality. *)
Local Lemma maps_eq_of_lookup_eq : forall A (m1 m2 : IntMap.IntMap A),
  IntMapProofs.WF m1 -> IntMapProofs.WF m2 ->
  (forall k, lookup k m1 = lookup k m2) -> m1 = m2.
Proof.
  intros A m1 m2 [f1 S1] [f2 S2] H.
  eapply IntMapProofs.Sem_unique; [exact S1|exact S2|].
  intro k. rewrite -(IntMapProofs.lookup_Sem S1) -(IntMapProofs.lookup_Sem S2). apply H.
Qed.
Local Lemma IntMap_Eq_refl : forall A `{EqLaws A} (m : IntMap.IntMap A), m == m.
Proof.
  intros A E L m. induction m as [p mask l IHl r IHr|k v|].
  - change ((mask == mask) && ((p == p) && ((l == l) && (r == r))) = true).
    rewrite !Eq_refl_Word IHl IHr. reflexivity.
  - change ((k == k) && (v == v) = true). rewrite Eq_refl_Word Eq_refl. reflexivity.
  - reflexivity.
Qed.
Lemma delete_commute : forall A `{EqLaws A} kx ky (i : IntMap.IntMap A),
  IntMapProofs.WF i -> delete ky (delete kx i) == delete kx (delete ky i).
Proof.
  intros A E L kx ky i W.
  assert (H : delete ky (delete kx i) = delete kx (delete ky i)).
  { apply maps_eq_of_lookup_eq; try (repeat apply IntMapProofs.delete_WF; assumption).
    intro k. rewrite !lookup_delete; try (try apply IntMapProofs.delete_WF; assumption).
    destruct (k =? kx)%N, (k =? ky)%N; reflexivity. }
  rewrite H. exact (@IntMap_Eq_refl A E L _).
Qed.
Local Lemma filter_bin {A} (f : A -> bool) p mask (l r : IntMap.IntMap A) :
  Data.IntMap.Internal.filter f (bin p mask l r) =
  bin p mask (Data.IntMap.Internal.filter f l) (Data.IntMap.Internal.filter f r).
Proof.
  destruct l; destruct r; simpl;
    rewrite ?IntMapUnionProofs.bin_Nil_l ?IntMapUnionProofs.bin_Nil_r;
    repeat match goal with
    | |- context [match ?t with Nil => _ | _ => _ end] => destruct t
    end; reflexivity.
Qed.
Lemma filter_comp : forall A `{EqLaws A} f f' (i : IntMap.IntMap A),
  Data.IntMap.Internal.filter f (Data.IntMap.Internal.filter f' i) ==
  Data.IntMap.Internal.filter (fun v => f v && f' v) i.
Proof.
  intros A E L f f' i.
  assert (H : Data.IntMap.Internal.filter f (Data.IntMap.Internal.filter f' i) =
    Data.IntMap.Internal.filter (fun v => f v && f' v) i).
  { induction i as [p mask l IHl r IHr|k v|].
    - change (Data.IntMap.Internal.filter f
        (bin p mask (Data.IntMap.Internal.filter f' l) (Data.IntMap.Internal.filter f' r)) =
        bin p mask (Data.IntMap.Internal.filter (fun v => f v && f' v) l)
                   (Data.IntMap.Internal.filter (fun v => f v && f' v) r)).
      rewrite filter_bin IHl IHr. reflexivity.
    - unfold Data.IntMap.Internal.filter, Data.IntMap.Internal.filterWithKey. simpl.
      destruct (f' v), (f v); reflexivity.
    - reflexivity. }
  rewrite H. exact (@IntMap_Eq_refl A E L _).
Qed.
Lemma filter_true : forall A `{EqLaws A} (m : IntMap.IntMap A),
  IntMapProofs.WF m -> Data.IntMap.Internal.filter (const true) m == m.
Proof.
  intros A E L m W.
  assert (H : Data.IntMap.Internal.filter (const true) m = m).
  { apply maps_eq_of_lookup_eq; try apply IntMapProofs.filter_WF; try assumption.
    intro k. rewrite (lookup_filter _ _ _ _ W). destruct (lookup k m); reflexivity. }
  rewrite H. exact (@IntMap_Eq_refl A E L _).
Qed.

Lemma Eq_membership : forall A (HeqA : Eq_ A) (HlawsA : EqLaws A) (m1 m2 : IntMap.IntMap A),
  m1 == m2 -> forall k, member k m1 = member k m2.
Proof.
  intros A E L. induction m1 as [p1 mask1 l1 IHl r1 IHr|kx vx|];
    destruct m2 as [p2 mask2 l2 r2|ky vy|]; intros H k; simpl in H; try discriminate.
  - apply andb_true_iff in H. destruct H as [Hm H].
    apply andb_true_iff in H. destruct H as [Hp H].
    apply andb_true_iff in H. destruct H as [Hl Hr].
    move: Hm => /Eq_eq_Word Hm. move: Hp => /Eq_eq_Word Hp. subst.
    simpl. destruct (nomatch k p2 mask2); [reflexivity|].
    destruct (Data.IntSet.Internal.zero k mask2); auto.
  - apply andb_true_iff in H. destruct H as [Hk Hv].
    move: Hk => /Eq_eq_Word Hk. subst. reflexivity.
  - reflexivity.
Qed.

Local Lemma lookup_union_eq : forall A (m1 m2 : IntMap.IntMap A) k,
  IntMapProofs.WF m1 -> IntMapProofs.WF m2 ->
  lookup k (union m1 m2) = oro (lookup k m1) (lookup k m2).
Proof.
  intros A m1 m2 k [f1 S1] [f2 S2].
  rewrite (IntMapProofs.lookup_Sem (IntMapUnionProofs.union_Sem _ _ _ _ S1 S2)).
  rewrite (IntMapProofs.lookup_Sem S1) (IntMapProofs.lookup_Sem S2). reflexivity.
Qed.
Local Lemma lookup_difference_eq : forall A B (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B) k,
  IntMapProofs.WF m1 -> IntMapProofs.WF m2 ->
  lookup k (difference m1 m2) = match lookup k m2 with Some _ => None | None => lookup k m1 end.
Proof.
  intros A B m1 m2 k [f1 S1] [f2 S2].
  rewrite (IntMapProofs.lookup_Sem (IntMapUnionProofs.difference_Sem _ _ _ _ S1 S2)).
  rewrite (IntMapProofs.lookup_Sem S1) (IntMapProofs.lookup_Sem S2). reflexivity.
Qed.
Lemma member_union : forall A key (i i0 : IntMap.IntMap A),
  IntMapProofs.WF i -> IntMapProofs.WF i0 ->
  member key (union i i0) = member key i0 || member key i.
Proof.
  intros A key i i0 W W0.
  rewrite (member_isSome _ _ _ (IntMapUnionProofs.union_WF _ _ W W0)).
  rewrite (lookup_union_eq _ _ _ _ W W0).
  rewrite (member_isSome _ _ _ W) (member_isSome _ _ _ W0).
  destruct (lookup key i), (lookup key i0); reflexivity.
Qed.
Lemma lookup_union : forall A key (val:A) (m1 m2 : IntMap.IntMap A),
  IntMapProofs.WF m1 -> IntMapProofs.WF m2 ->
  (lookup key m1 = Some val \/ (lookup key m1 = None /\ lookup key m2 = Some val)) <->
  lookup key (union m1 m2) = Some val.
Proof.
  intros A key val m1 m2 W1 W2. rewrite (lookup_union_eq _ _ _ _ W1 W2).
  destruct (lookup key m1); simpl; intuition congruence.
Qed.
Lemma lookup_difference_in_snd : forall key b (i i' : IntMap.IntMap b) (y:b),
  IntMapProofs.WF i -> IntMapProofs.WF i' -> lookup key i' = Some y ->
  lookup key (difference i i') = None.
Proof. intros key b i i' y W W' H. rewrite (lookup_difference_eq _ _ _ _ _ W W') H. reflexivity. Qed.
Lemma lookup_difference_not_in_snd : forall key b (i i' : IntMap.IntMap b) (y:b),
  IntMapProofs.WF i -> IntMapProofs.WF i' -> lookup key i' = None ->
  lookup key (difference i i') = lookup key i.
Proof. intros key b i i' y W W' H. rewrite (lookup_difference_eq _ _ _ _ _ W W') H. reflexivity. Qed.
Lemma member_difference : forall A B k (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
  IntMapProofs.WF m1 -> IntMapProofs.WF m2 ->
  member k (difference m1 m2) = member k m1 && negb (member k m2).
Proof.
  intros A B k m1 m2 W1 W2.
  rewrite (member_isSome _ _ _ (IntMapUnionProofs.difference_WF _ _ W1 W2)).
  rewrite (lookup_difference_eq _ _ _ _ _ W1 W2).
  rewrite (member_isSome _ _ _ W1) (member_isSome _ _ _ W2).
  destruct (lookup k m1), (lookup k m2); reflexivity.
Qed.

(* Key-sensitive filtering uses the same invariant-preserving bin constructor.
   Its semantic proof also supplies the lookup implication needed by clients. *)
Local Lemma filterWithKey_Desc {A} (s : IntMap.IntMap A) r f
    (S : IntMapProofs.Desc s r f) : forall p,
  IntMapProofs.Desc0 (filterWithKey p s) r
    (fun i => match f i with Some v => if p i v then Some v else None | None => None end).
Proof.
  induction S as [k v r f F R |
    l rl fl rr tr fr p mask r f Sl IHl Sr IHr Bits SubL SubR P M F]; intro pred.
  - subst r. simpl. destruct (pred k v) eqn:E.
    + apply IntMapProofs.Desc_Desc0. apply IntMapProofs.DescTip; [|reflexivity].
      intro i. rewrite F. destruct (N.eqb_spec i k) as [->|H]; [rewrite E|]; reflexivity.
    + apply IntMapProofs.Desc0Nil. intro i. rewrite F.
      destruct (N.eqb_spec i k) as [->|H]; [rewrite E|]; reflexivity.
  - change (IntMapProofs.Desc0 (bin p mask (filterWithKey pred l) (filterWithKey pred rr)) r
      (fun i => match f i with Some v => if pred i v then Some v else None | None => None end)).
    eapply IntMapProofs.bin_Desc0; try apply IHl; try apply IHr; try eassumption.
    intro i. rewrite F.
    assert (D : rangeDisjoint rl tr = true).
    { eapply isSubrange_disj_disj_r; [exact SubR|].
      eapply isSubrange_disj_disj_l; [exact SubL|]. apply halves_disj. exact Bits. }
    destruct (fl i) as [v|] eqn:L; [|reflexivity].
    assert (R : fr i = None).
    { eapply IntMapProofs.isSubmapOfBy_disjoint1; eassumption. }
    rewrite R. simpl. destruct (pred i v); reflexivity.
Qed.
Local Lemma filterWithKey_Sem {A} (s : IntMap.IntMap A) f
    (S : IntMapProofs.Sem s f) p :
  IntMapProofs.Sem (filterWithKey p s)
    (fun i => match f i with Some v => if p i v then Some v else None | None => None end).
Proof.
  destruct S as [f F|s r f S].
  - apply IntMapProofs.SemNil. intro i. rewrite F. reflexivity.
  - apply IntMapProofs.Desc0_Sem with (r := r). apply filterWithKey_Desc. exact S.
Qed.
Lemma lookup_filterWithKey : forall b key (val:b) m f,
  IntMapProofs.WF m -> lookup key (filterWithKey f m) = Some val -> lookup key m = Some val.
Proof.
  intros b key val m f [g S].
  rewrite (IntMapProofs.lookup_Sem (filterWithKey_Sem m g S f)) (IntMapProofs.lookup_Sem S).
  destruct (g key) as [v|]; [destruct (f key v)|]; congruence.
Qed.

Local Lemma partition_filters {A} (P : A -> bool) (m : IntMap.IntMap A) :
  partition P m = (Data.IntMap.Internal.filter P m,
                  Data.IntMap.Internal.filter (fun v => negb (P v)) m).
Proof.
  induction m as [p mask l IHl r IHr|k v|].
  - change (partition P (Bin p mask l r)) with
      (let '(r1,r2) := partition P r in let '(l1,l2) := partition P l in
       (bin p mask l1 r1, bin p mask l2 r2)).
    rewrite IHl IHr. reflexivity.
  - unfold Data.IntMap.Internal.partition, Data.IntMap.Internal.partitionWithKey,
      Data.IntMap.Internal.filter, Data.IntMap.Internal.filterWithKey. simpl.
    destruct (P v); reflexivity.
  - reflexivity.
Qed.
Lemma lookup_partition : forall A key (val:A) (m m' : IntMap.IntMap A) P,
  IntMapProofs.WF m ->
  ((m' = fst (partition P m) \/ m' = snd (partition P m)) /\ lookup key m' = Some val) ->
  lookup key m = Some val.
Proof.
  intros A key val m m' P W [[Hm|Hm] H]; subst m'; rewrite partition_filters in H; simpl in H.
  - exact (proj2 (lookup_filter_Some _ _ _ _ _ W H)).
  - exact (proj2 (lookup_filter_Some _ _ _ _ _ W H)).
Qed.

Fixpoint tree_elem_kv {a} (k : N) (v : a) (m : IntMap.IntMap a) : Prop :=
  match m with
  | Nil => False
  | Tip k' v' => k = k' /\ v = v'
  | Bin _ _ l r => tree_elem_kv k v l \/ tree_elem_kv k v r
  end.
Lemma lookup_tree_elem_kv : forall A k (v:A) m,
  lookup k m = Some v -> tree_elem_kv k v m.
Proof.
  intros A k v m. induction m as [p mask l IHl r IHr|k' v'|]; simpl.
  - destruct (Data.IntSet.Internal.zero k mask); auto.
  - destruct (k == k') eqn:K; [|discriminate].
    intro H. inversion H; subst. move: K => /Eq_eq_Word K. auto.
  - discriminate.
Qed.
Local Lemma tree_elem_Desc {A} (m : IntMap.IntMap A) r f
    (S : IntMapProofs.Desc m r f) : forall k v,
  tree_elem_kv k v m -> f k = Some v.
Proof.
  induction S as [key val r f F R|
    l rl fl rr tr fr p mask r f Sl IHl Sr IHr Bits SubL SubR P M F]; intros k v H.
  - destruct H as [-> ->]. rewrite F N.eqb_refl. reflexivity.
  - destruct H as [H|H]; rewrite F.
    + rewrite (IHl _ _ H). reflexivity.
    + assert (R : fr k = Some v) by (apply IHr; exact H).
      assert (D : rangeDisjoint tr rl = true).
      { rewrite rangeDisjoint_sym. eapply isSubrange_disj_disj_r; [exact SubR|].
        eapply isSubrange_disj_disj_l; [exact SubL|]. apply halves_disj. exact Bits. }
      assert (L : fl k = None).
      { eapply IntMapProofs.isSubmapOfBy_disjoint1; eassumption. }
      rewrite L. exact R.
Qed.
Lemma tree_elem_kv_lookup : forall A k (v:A) (m : IntMap.IntMap A),
  IntMapProofs.WF m -> tree_elem_kv k v m -> lookup k m = Some v.
Proof.
  intros A k v m [f S] H. rewrite (IntMapProofs.lookup_Sem S).
  destruct S as [f F|m r f S]; [contradiction|]. eapply tree_elem_Desc; eassumption.
Qed.
Lemma IntMap_map_keys_equal {A} `{GHC.Base.Eq_ A}
    (keyof : A -> N)
    (complete : forall x y, keyof x = keyof y -> GHC.Base.op_zeze__ x y = true) :
  forall (m1 m2 : IntMap.IntMap A),
    Data.IntMap.Internal.map keyof m1 = Data.IntMap.Internal.map keyof m2 ->
    GHC.Base.op_zeze__ m1 m2 = true.
Proof.
  induction m1 as [p mask l IHl r IHr|k v|]; intros m2 E;
    destruct m2 as [p' mask' l' r'|k' v'|]; cbn in E; try discriminate.
  - injection E as Hp Hm Hl Hr. subst p' mask'.
    change (andb (N.eqb mask mask) (andb (N.eqb p p)
      (andb (GHC.Base.op_zeze__ l l') (GHC.Base.op_zeze__ r r'))) = true).
    rewrite !N.eqb_refl (IHl _ Hl) (IHr _ Hr). reflexivity.
  - injection E as Hk Hv. subst k'.
    change (andb (N.eqb k k) (GHC.Base.op_zeze__ v v') = true).
    rewrite N.eqb_refl (complete _ _ Hv). reflexivity.
  - reflexivity.
Qed.
Lemma IntMap_equal_by_key_membership {A} `{GHC.Base.Eq_ A}
    (keyof : A -> N)
    (complete : forall x y, keyof x = keyof y -> GHC.Base.op_zeze__ x y = true)
    (m1 m2 : IntMap.IntMap A)
    (WF1 : IntMapProofs.WF m1) (WF2 : IntMapProofs.WF m2)
    (keys1 : forall k v, lookup k m1 = Some v -> keyof v = k)
    (keys2 : forall k v, lookup k m2 = Some v -> keyof v = k)
    (members : forall k, member k m1 = member k m2) :
    GHC.Base.op_zeze__ m1 m2 = true.
Proof.
  apply (IntMap_map_keys_equal keyof complete).
  destruct WF1 as [f1 S1], WF2 as [f2 S2].
  eapply IntMapProofs.Sem_unique.
  - exact (IntMapProofs.map_Sem _ _ _ _ keyof S1).
  - exact (IntMapProofs.map_Sem _ _ _ _ keyof S2).
  - intro k. pose proof (members k) as Hmem.
    rewrite (IntMapProofs.member_Sem S1) (IntMapProofs.member_Sem S2) in Hmem.
    pose proof (@IntMapProofs.lookup_Sem _ _ _ k S1) as L1.
    pose proof (@IntMapProofs.lookup_Sem _ _ _ k S2) as L2.
    destruct (f1 k) as [v1|] eqn:F1; destruct (f2 k) as [v2|] eqn:F2;
      try discriminate; simpl.
    + rewrite F1. simpl. rewrite (keys1 k v1 L1) (keys2 k v2 L2). reflexivity.
    + rewrite F1. reflexivity.
Qed.

Local Lemma lookup_intersection_eq : forall A B (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B) k,
  IntMapProofs.WF m1 -> IntMapProofs.WF m2 ->
  lookup k (intersection m1 m2) = match lookup k m2 with Some _ => lookup k m1 | None => None end.
Proof.
  intros A B m1 m2 k [f1 S1] [f2 S2].
  rewrite (IntMapProofs.lookup_Sem (IntMapUnionProofs.intersection_Sem _ _ _ _ S1 S2)).
  rewrite (IntMapProofs.lookup_Sem S1) (IntMapProofs.lookup_Sem S2). reflexivity.
Qed.
Lemma lookup_intersection : forall a b key (val1:a) (m1 : IntMap.IntMap a) (m2 : IntMap.IntMap b),
  IntMapProofs.WF m1 -> IntMapProofs.WF m2 ->
  (lookup key m1 = Some val1 /\ exists val2, lookup key m2 = Some val2) <->
  lookup key (intersection m1 m2) = Some val1.
Proof.
  intros a b key val1 m1 m2 W1 W2. rewrite (lookup_intersection_eq _ _ _ _ _ W1 W2).
  destruct (lookup key m2) as [v|]; split; try (intros [H [w E]]; discriminate);
    try discriminate; intuition eauto.
Qed.
Lemma member_intersection : forall A B k (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
  IntMapProofs.WF m1 -> IntMapProofs.WF m2 ->
  member k (intersection m1 m2) = member k m1 && member k m2.
Proof.
  intros A B k m1 m2 W1 W2.
  rewrite (member_isSome _ _ _ (IntMapUnionProofs.intersection_WF _ _ W1 W2)).
  rewrite (lookup_intersection_eq _ _ _ _ _ W1 W2).
  rewrite (member_isSome _ _ _ W1) (member_isSome _ _ _ W2).
  destruct (lookup k m1), (lookup k m2); reflexivity.
Qed.
Local Lemma bool_eq_of_iff (b1 b2 : bool) : (b1 <-> b2) -> b1 = b2.
Proof. destruct b1, b2; simpl; intuition. Qed.
Lemma disjoint_spec : forall A B (m1 : IntMap.IntMap A) (m2 : IntMap.IntMap B),
  IntMapProofs.WF m1 -> IntMapProofs.WF m2 ->
  (disjoint m1 m2 = true <-> forall k, member k m1 = true -> member k m2 = false).
Proof.
  intros A B m1 m2 W1 W2.
  rewrite (IntMapUnionProofs.disjoint_spec _ _ W1 W2). split.
  - intros H k M. destruct (H k) as [E|E].
    + apply (proj1 (member_lookup _ _ _ W1)) in M. destruct M as [v V]. congruence.
    + apply (proj2 (non_member_lookup _ _ _ W2)). exact E.
  - intros H k. destruct (member k m1) eqn:M.
    + right. apply (proj1 (non_member_lookup _ _ _ W2)). apply H. exact M.
    + left. apply (proj1 (non_member_lookup _ _ _ W1)). exact M.
Qed.
Lemma disjoint_sym : forall A B (i : IntMap.IntMap A) (j : IntMap.IntMap B),
  disjoint i j = disjoint j i.
Proof.
  intros A B i j. remember (size_nat i + size_nat j)%nat as n eqn:E.
  revert i j E. induction n using lt_wf_ind. intros i j E.
  destruct i as [p1 m1 l1 r1|k1 v1|]; destruct j as [p2 m2 l2 r2|k2 v2|].
  - rewrite !IntMapUnionProofs.disjoint_Bin_Bin.
    destruct (shorter m1 m2) eqn:S1; destruct (shorter m2 m1) eqn:S2.
    + change ((m2 <? m1)%N = true) in S1. change ((m1 <? m2)%N = true) in S2.
      apply N.ltb_lt in S1. apply N.ltb_lt in S2. lia.
    + destruct (nomatch p2 p1 m1); [reflexivity|].
      destruct (Data.IntSet.Internal.zero p2 m1);
        (eapply H; [|reflexivity]); cbn [size_nat] in *; lia.
    + destruct (nomatch p1 p2 m2); [reflexivity|].
      destruct (Data.IntSet.Internal.zero p1 m2);
        (eapply H; [|reflexivity]); cbn [size_nat] in *; lia.
    + change (p2 == p1) with ((p2 =? p1)%N). rewrite N.eqb_sym.
      change (p1 == p2) with ((p1 =? p2)%N). destruct (p1 =? p2)%N; [|reflexivity].
      f_equal; (eapply H; [|reflexivity]); cbn [size_nat] in *; lia.
  - rewrite IntMapUnionProofs.disjoint_Tip_r IntMapUnionProofs.disjoint_Tip_l. reflexivity.
  - rewrite IntMapUnionProofs.disjoint_Nil_r IntMapUnionProofs.disjoint_Nil_l. reflexivity.
  - rewrite IntMapUnionProofs.disjoint_Tip_l IntMapUnionProofs.disjoint_Tip_r. reflexivity.
  - rewrite !IntMapUnionProofs.disjoint_Tip_l.
    change (negb (k1 =? k2)%N = negb (k2 =? k1)%N). rewrite N.eqb_sym. reflexivity.
  - rewrite IntMapUnionProofs.disjoint_Nil_r IntMapUnionProofs.disjoint_Nil_l. reflexivity.
  - rewrite IntMapUnionProofs.disjoint_Nil_l IntMapUnionProofs.disjoint_Nil_r. reflexivity.
  - rewrite IntMapUnionProofs.disjoint_Nil_l IntMapUnionProofs.disjoint_Nil_r. reflexivity.
  - rewrite !IntMapUnionProofs.disjoint_Nil_l. reflexivity.
Qed.
Lemma disjoint_insert : forall b k (v:b) (i1 i2 : IntMap.IntMap b),
  IntMapProofs.WF i1 -> IntMapProofs.WF i2 ->
  disjoint i1 (insert k v i2) = negb (member k i1) && disjoint i1 i2.
Proof.
  intros b k v i1 i2 W1 W2.
  pose proof (IntMapProofs.insert_WF b k v i2 W2) as WI.
  apply bool_eq_of_iff. split.
  - intro H. pose proof (proj1 (disjoint_spec _ _ _ _ W1 WI) H) as S.
    apply andb_true_iff. split.
    + apply negb_true_iff. destruct (member k i1) eqn:K; [|reflexivity].
      specialize (S k K). rewrite (member_insert _ _ _ _ _ W2) Eq_refl_Word in S. discriminate.
    + apply (proj2 (disjoint_spec _ _ _ _ W1 W2)). intros key K.
      specialize (S key K). rewrite (member_insert _ _ _ _ _ W2) in S.
      destruct (key == k); [discriminate|exact S].
  - intro H. apply andb_true_iff in H. destruct H as [K D]. apply negb_true_iff in K.
    apply (proj2 (disjoint_spec _ _ _ _ W1 WI)). intros key M.
    rewrite (member_insert _ _ _ _ _ W2).
    destruct (N.eqb_spec key k) as [E|E].
    + subst key. rewrite K in M. discriminate.
    + change (key == k) with ((key =? k)%N). apply N.eqb_neq in E. rewrite E. simpl.
      exact (proj1 (disjoint_spec _ _ _ _ W1 W2) D key M).
Qed.
Lemma disjoint_non_member : forall b k (v:b) (i1 i2 : IntMap.IntMap b),
  IntMapProofs.WF i1 -> IntMapProofs.WF i2 ->
  (disjoint i1 (insert k v i2) <-> member k i1 = false /\ disjoint i1 i2).
Proof.
  intros b k v i1 i2 W1 W2. rewrite (disjoint_insert _ _ _ _ _ W1 W2).
  change ((negb (member k i1) && disjoint i1 i2 = true) <->
    member k i1 = false /\ disjoint i1 i2 = true).
  rewrite andb_true_iff negb_true_iff. reflexivity.
Qed.
Lemma disjoint_eq : forall b (x1 x2 y1 y2 : IntMap.IntMap b),
  IntMapProofs.WF x1 -> IntMapProofs.WF x2 -> IntMapProofs.WF y1 -> IntMapProofs.WF y2 ->
  (forall a, member a x1 <-> member a y1) ->
  (forall a, member a x2 <-> member a y2) -> disjoint x1 x2 = disjoint y1 y2.
Proof.
  intros b x1 x2 y1 y2 W1 W2 V1 V2 H1 H2. apply bool_eq_of_iff.
  change (disjoint x1 x2 = true <-> disjoint y1 y2 = true).
  rewrite (disjoint_spec _ _ _ _ W1 W2) (disjoint_spec _ _ _ _ V1 V2).
  assert (E1 : forall k, member k x1 = member k y1) by (intro k; apply bool_eq_of_iff; apply H1).
  assert (E2 : forall k, member k x2 = member k y2) by (intro k; apply bool_eq_of_iff; apply H2).
  split; intros H k K.
  - rewrite -E2. apply H. rewrite E1. exact K.
  - rewrite E2. apply H. rewrite -E1. exact K.
Qed.
Lemma disjoint_difference : forall b (i1 i2 i3 : IntMap.IntMap b),
  IntMapProofs.WF i1 -> IntMapProofs.WF i2 -> IntMapProofs.WF i3 ->
  disjoint i2 i3 = true -> Data.IntMap.Internal.null (difference i1 i2) -> disjoint i1 i3 = true.
Proof.
  intros b i1 i2 i3 W1 W2 W3 D N.
  pose proof (proj1 (disjoint_spec _ _ _ _ W2 W3) D) as S.
  pose proof (proj1 (null_member _ _ (IntMapUnionProofs.difference_WF _ _ W1 W2)) N) as E.
  apply (proj2 (disjoint_spec _ _ _ _ W1 W3)). intros k K.
  specialize (E k). rewrite (member_difference _ _ _ _ _ W1 W2) K in E. simpl in E.
  apply negb_false_iff in E. exact (S k E).
Qed.
Lemma null_intersection_non_member : forall b k (v:b) (i1 i2 : IntMap.IntMap b),
  IntMapProofs.WF i1 -> IntMapProofs.WF i2 ->
  (Data.IntMap.Internal.null (intersection i1 (insert k v i2)) <->
   member k i1 = false /\ Data.IntMap.Internal.null (intersection i1 i2)).
Proof.
  intros b k v i1 i2 W1 W2.
  rewrite -(IntMapUnionProofs.disjoint_intersection _ _ W1 (IntMapProofs.insert_WF b k v i2 W2))
    -(IntMapUnionProofs.disjoint_intersection _ _ W1 W2).
  apply disjoint_non_member; assumption.
Qed.
Lemma null_intersection_difference : forall b (i1 i2 i3 : IntMap.IntMap b),
  IntMapProofs.WF i1 -> IntMapProofs.WF i2 -> IntMapProofs.WF i3 ->
  Data.IntMap.Internal.null (intersection i2 i3) ->
  Data.IntMap.Internal.null (difference i1 i2) -> Data.IntMap.Internal.null (intersection i1 i3).
Proof.
  intros b i1 i2 i3 W1 W2 W3.
  rewrite -(IntMapUnionProofs.disjoint_intersection _ _ W2 W3)
    -(IntMapUnionProofs.disjoint_intersection _ _ W1 W3).
  apply disjoint_difference; assumption.
Qed.
Lemma null_intersection_eq : forall b (x1 x2 y1 y2 : IntMap.IntMap b),
  IntMapProofs.WF x1 -> IntMapProofs.WF x2 -> IntMapProofs.WF y1 -> IntMapProofs.WF y2 ->
  (forall a, member a x1 <-> member a y1) -> (forall a, member a x2 <-> member a y2) ->
  Data.IntMap.Internal.null (intersection x1 x2) = Data.IntMap.Internal.null (intersection y1 y2).
Proof.
  intros b x1 x2 y1 y2 W1 W2 V1 V2.
  rewrite -(IntMapUnionProofs.disjoint_intersection _ _ W1 W2)
    -(IntMapUnionProofs.disjoint_intersection _ _ V1 V2).
  apply disjoint_eq; assumption.
Qed.
