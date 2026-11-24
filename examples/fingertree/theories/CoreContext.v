From Stdlib Require Import Lists.List.
Require Import Data.FingerTree FingerTreeProofs.CoreModel FingerTreeProofs.CoreOperations.
Import ListNotations.

Section References.
Context {v : Type} `{GHC.Base.Monoid v}.
(* Left accumulation is in sequence order. Right accumulation prepends each
   original measurement; neither includes the element being visited. *)
Fixpoint contextFlatMap {a b} (mu : a -> v) (f : v -> a -> v -> list b)
  (l : v) (xs : list a) (r : v) : list b :=
  match xs with
  | [] => []
  | x :: tail => f l x (GHC.Base.mappend (listMeasure mu tail) r) ++
      contextFlatMap mu f (GHC.Base.mappend l (mu x)) tail r
  end.
Definition contextMap {a b} (mu : a -> v) (f : v -> a -> v -> b)
  l xs r := contextFlatMap mu (fun l x r => [f l x r]) l xs r.
Definition contextFoldl {a b} (mu : a -> v) (f : b -> v -> a -> v -> b)
  z l xs r := List.fold_left (fun z p => let '(l,x,r) := p in f z l x r)
    (contextMap mu (fun l x r => (l,x,r)) l xs r) z.
Definition contextFoldr {a b} (mu : a -> v) (f : v -> a -> v -> b -> b)
  z l xs r := List.fold_right (fun p z => let '(l,x,r) := p in f l x r z)
    z (contextMap mu (fun l x r => (l,x,r)) l xs r).
Fixpoint positionFlatMap {a b} (mu : a -> v) (f : v -> a -> list b)
  (l : v) (xs : list a) : list b :=
  match xs with [] => [] | x :: tail => f l x ++
    positionFlatMap mu f (GHC.Base.mappend l (mu x)) tail end.
Definition positionMap {a b} (mu : a -> v) (f : v -> a -> b) l xs :=
  positionFlatMap mu (fun l x => [f l x]) l xs.
Definition positionFoldl {a b} (mu : a -> v) (f : b -> v -> a -> b) z l xs :=
  List.fold_left (fun z p => f z (fst p) (snd p))
    (positionMap mu (fun l x => (l,x)) l xs) z.
Definition positionFoldr {a b} (mu : a -> v) (f : v -> a -> b -> b) z l xs :=
  List.fold_right (fun p z => f (fst p) (snd p) z)
    z (positionMap mu (fun l x => (l,x)) l xs).

Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma contextFlatMap_app {a b} (mu : a -> v) (f : v -> a -> v -> list b) xs ys l r :
  contextFlatMap mu f l (xs ++ ys) r =
  contextFlatMap mu f l xs (GHC.Base.mappend (listMeasure mu ys) r) ++
  contextFlatMap mu f (GHC.Base.mappend l (listMeasure mu xs)) ys r.
Proof.
  revert l; induction xs as [|x xs IH]; intro l; cbn [contextFlatMap listMeasure List.fold_right List.app].
  - rewrite right_id; reflexivity.
  - rewrite (listMeasure_app assoc left_id), assoc, IH.
    cbn [listMeasure List.fold_right]; rewrite assoc, List.app_assoc; reflexivity.
Qed.

Lemma contextFlatMap_ext {a b} (mu : a -> v) (f g : v -> a -> v -> list b) xs :
  (forall l x r, List.In x xs -> f l x r = g l x r) ->
  forall l r, contextFlatMap mu f l xs r = contextFlatMap mu g l xs r.
Proof.
  induction xs as [|x xs IH]; intros E l r; cbn [contextFlatMap]; [reflexivity|].
  rewrite E by (left; reflexivity); f_equal; apply IH; intros; apply E; right; assumption.
Qed.

Lemma contextFlatMap_singleton {a b} (mu : a -> v) (f : v -> a -> v -> list b) l x r :
  contextFlatMap mu f l [x] r = f l x r.
Proof. cbn [contextFlatMap listMeasure List.fold_right]; rewrite left_id, List.app_nil_r; reflexivity. Qed.

Lemma contextFlatMap_position {a b} (mu : a -> v) (f : v -> a -> list b) xs l r :
  contextFlatMap mu (fun l x _ => f l x) l xs r = positionFlatMap mu f l xs.
Proof. revert l; induction xs; intros; cbn; congruence. Qed.

(* Exact original prefix and suffix values, with arbitrary external contexts. *)
Lemma contextFlatMap_at {a b} (mu : a -> v) (f : v -> a -> v -> list b) pre x post l r :
  contextFlatMap mu f l (pre ++ x :: post) r =
  contextFlatMap mu f l pre (GHC.Base.mappend (listMeasure mu (x :: post)) r) ++
  f (GHC.Base.mappend l (listMeasure mu pre)) x
    (GHC.Base.mappend (listMeasure mu post) r) ++
  contextFlatMap mu f (GHC.Base.mappend (GHC.Base.mappend l (listMeasure mu pre)) (mu x)) post r.
Proof. rewrite contextFlatMap_app; reflexivity. Qed.
End References.

Section ContextContents.
Context {v : Type} `{GHC.Base.Monoid v}.
Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Local Ltac normalize :=
  repeat rewrite (contextFlatMap_app assoc left_id right_id);
  repeat rewrite (listMeasure_app assoc left_id);
  repeat rewrite assoc; rewrite ?left_id, ?right_id;
  repeat rewrite <- List.app_assoc.

Lemma mapWCDigit_contents {a b c d} (M : Measured v a)
  (P : a -> Prop) (flat : a -> list c) (mu : c -> v)
  (f : v -> a -> v -> b) (g : b -> list d) (h : v -> c -> v -> list d) digit l r :
  (forall x, P x -> measure x = listMeasure mu (flat x)) ->
  (forall l x r, P x -> g (f l x r) = contextFlatMap mu h l (flat x) r) ->
  digitValidity P digit ->
  digitContentsWith g (mapWCDigit f l digit r) =
    contextFlatMap mu h l (digitContentsWith flat digit) r.
Proof.
  intros E F V; destruct digit; cbn [digitValidity] in V;
    cbn [mapWCDigit digitContentsWith]; decompose [and] V;
    repeat rewrite F by assumption; normalize;
    repeat match goal with Hx : P ?x |- _ => rewrite (E x Hx) end;
    repeat rewrite assoc; reflexivity.
Qed.

Lemma mapWCNode_contents {a b c d w} (M : Measured v a)
  (S : GHC.Base.Semigroup w) (N : GHC.Base.Monoid w) (B : Measured w b)
  (P : a -> Prop) (flat : a -> list c) (mu : c -> v)
  (f : v -> a -> v -> b) (g : b -> list d) (h : v -> c -> v -> list d) n l r :
  (forall x, P x -> measure x = listMeasure mu (flat x)) ->
  (forall l x r, P x -> g (f l x r) = contextFlatMap mu h l (flat x) r) ->
  nodeValidity (@measure v a _ _ M) P n ->
  nodeContentsWith g (mapWCNode f l n r) =
    contextFlatMap mu h l (nodeContentsWith flat n) r.
Proof.
  intros E F V; destruct n; cbn [nodeValidity] in V;
    cbn [mapWCNode node2 node3 nodeContentsWith]; decompose [and] V;
    repeat rewrite F by assumption; normalize;
    repeat match goal with Hx : P ?x |- _ => rewrite (E x Hx) end;
    repeat rewrite assoc; reflexivity.
Qed.

Lemma mapWCTree_contents : forall a (t : FingerTree v a) (M : Measured v a)
  P c (flat : a -> list c) (mu : c -> v)
  w b (S : GHC.Base.Semigroup w) (N : GHC.Base.Monoid w) (B : Measured w b)
  d (f : v -> a -> v -> b) (g : b -> list d) (h : v -> c -> v -> list d),
  (forall x, P x -> measure x = listMeasure mu (flat x)) ->
  (forall l x r, P x -> g (f l x r) = contextFlatMap mu h l (flat x) r) ->
  validityWith (@measure v a _ _ M) P t -> forall l r,
  contentsWith g (mapWCTree f l t r) = contextFlatMap mu h l (contentsWith flat t) r.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    P c (flat : a -> list c) (mu : c -> v)
    w b (S : GHC.Base.Semigroup w) (N : GHC.Base.Monoid w) (B : Measured w b)
    d (f : v -> a -> v -> b) (g : b -> list d) (h : v -> c -> v -> list d),
    (forall x, P x -> measure x = listMeasure mu (flat x)) ->
    (forall l x r, P x -> g (f l x r) = contextFlatMap mu h l (flat x) r) ->
    validityWith (@measure v a _ _ M) P t -> forall l r,
    contentsWith g (mapWCTree f l t r) = contextFlatMap mu h l (contentsWith flat t) r) _ _ _).
  - intros; reflexivity.
  - intros; apply H2; assumption.
  - intros a cache pr m IH sf M P c flat mu w b S N B d f g h E F [Vp [Vm [Vs Ec]]] l r.
    cbn [mapWCTree deep contentsWith].
    rewrite (mapWCDigit_contents M P flat mu f g h pr _ _ E F Vp),
      (mapWCDigit_contents M P flat mu f g h sf _ _ E F Vs).
    rewrite (IH Measured__Node__5 (nodeValidity (@measure v a _ _ M) P)
      c (nodeContentsWith flat) mu w (Node w b) S N Measured__Node__5
      d (mapWCNode f) (nodeContentsWith g) h).
    + rewrite (measure_digit_model M pr), (measure_digit_model M sf), measure_tree_model.
      change (treeCacheWith (@measure v (Node v a) _ _ Measured__Node__5) m)
        with (treeCacheWith nodeCache m).
      rewrite (valid_digit_measure assoc left_id (@measure v a _ _ M) P flat mu pr E Vp),
        (valid_digit_measure assoc left_id (@measure v a _ _ M) P flat mu sf E Vs).
      rewrite (valid_tree_measure assoc left_id _ m nodeCache
        (nodeValidity (@measure v a _ _ M) P) c (nodeContentsWith flat) mu).
      * normalize; reflexivity.
      * intros n Vn; eapply valid_node_measure; eassumption.
      * exact Vm.
    + intros n Vn; eapply valid_node_measure; eassumption.
    + intros; eapply mapWCNode_contents; eassumption.
    + exact Vm.
Qed.
End ContextContents.

(* Pure fold/map fusion is structural: it needs no cache or monoid laws. The
   interpretation parameter handles nonregular middle nodes. *)
Section Fusion.
Context {v w : Type} `{GHC.Base.Monoid v} `{GHC.Base.Monoid w}.

Lemma foldlWCTree_fusion : forall a (t : FingerTree v a) (M : Measured v a)
  b (B : Measured w b) c zt (g : b -> list c) (k : zt -> c -> zt)
  (f : zt -> v -> a -> v -> zt) (h : v -> a -> v -> b),
  (forall z l x r, f z l x r = List.fold_left k (g (h l x r)) z) ->
  forall z l r, foldlWCTree f z l t r =
    List.fold_left k (contentsWith g (mapWCTree h l t r)) z.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    b (B : Measured w b) c zt (g : b -> list c) (k : zt -> c -> zt)
    (f : zt -> v -> a -> v -> zt) (h : v -> a -> v -> b),
    (forall z l x r, f z l x r = List.fold_left k (g (h l x r)) z) ->
    forall z l r, foldlWCTree f z l t r =
      List.fold_left k (contentsWith g (mapWCTree h l t r)) z) _ _ _).
  - intros; reflexivity.
  - intros; apply H3.
  - intros a cache pr m IH sf M b B c zt g k f h E z l r.
    cbn [foldlWCTree mapWCTree deep contentsWith].
    assert (D : forall z l d r, foldlWCDigit f z l d r =
      List.fold_left k (digitContentsWith g (mapWCDigit h l d r)) z).
    { intros; destruct d; cbn [foldlWCDigit mapWCDigit digitContentsWith];
        repeat rewrite List.fold_left_app; repeat rewrite E; reflexivity. }
    rewrite !List.fold_left_app, <- !D.
    rewrite (IH Measured__Node__5 (Node w b) Measured__Node__5 c zt (nodeContentsWith g) k
      (foldlWCNode f) (mapWCNode h)).
    + reflexivity.
    + intros; destruct x; cbn [foldlWCNode mapWCNode node2 node3 nodeContentsWith];
        repeat rewrite List.fold_left_app; repeat rewrite E; reflexivity.
Qed.

Lemma foldrWCTree_fusion : forall a (t : FingerTree v a) (M : Measured v a)
  b (B : Measured w b) c zt (g : b -> list c) (k : c -> zt -> zt)
  (f : v -> a -> v -> zt -> zt) (h : v -> a -> v -> b),
  (forall l x r z, f l x r z = List.fold_right k z (g (h l x r))) ->
  forall z l r, foldrWCTree f z l t r =
    List.fold_right k z (contentsWith g (mapWCTree h l t r)).
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    b (B : Measured w b) c zt (g : b -> list c) (k : c -> zt -> zt)
    (f : v -> a -> v -> zt -> zt) (h : v -> a -> v -> b),
    (forall l x r z, f l x r z = List.fold_right k z (g (h l x r))) ->
    forall z l r, foldrWCTree f z l t r =
      List.fold_right k z (contentsWith g (mapWCTree h l t r))) _ _ _).
  - intros; reflexivity.
  - intros; apply H3.
  - intros a cache pr m IH sf M b B c zt g k f h E z l r.
    cbn [foldrWCTree mapWCTree deep contentsWith].
    assert (D : forall z l d r, foldrWCDigit f z l d r =
      List.fold_right k z (digitContentsWith g (mapWCDigit h l d r))).
    { intros; destruct d; cbn [foldrWCDigit mapWCDigit digitContentsWith];
        repeat rewrite List.fold_right_app; repeat rewrite E; reflexivity. }
    rewrite !List.fold_right_app, <- !D.
    rewrite (IH Measured__Node__5 (Node w b) Measured__Node__5 c zt (nodeContentsWith g) k
      (foldrWCNode f) (mapWCNode h)).
    + reflexivity.
    + intros; destruct x; cbn [foldrWCNode mapWCNode node2 node3 nodeContentsWith];
        repeat rewrite List.fold_right_app; repeat rewrite E; reflexivity.
Qed.
End Fusion.

Section RebuiltValidity.
Context {v w : Type} `{GHC.Base.Monoid v} `{GHC.Base.Monoid w}.
Lemma mapWCTree_validityWith : forall a (t : FingerTree v a) (M : Measured v a)
  b (B : Measured w b) (Q : b -> Prop) (f : v -> a -> v -> b),
  (forall l x r, Q (f l x r)) -> forall l r,
  validityWith (@measure w b _ _ B) Q (mapWCTree f l t r).
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    b (B : Measured w b) (Q : b -> Prop) (f : v -> a -> v -> b),
    (forall l x r, Q (f l x r)) -> forall l r,
    validityWith (@measure w b _ _ B) Q (mapWCTree f l t r)) _ _ _).
  - intros; exact I.
  - intros; apply H3.
  - intros a cache pr m IH sf M b B Q f E l r.
    cbn [mapWCTree]; apply deep_validityWith.
    + destruct pr; cbn [mapWCDigit digitValidity]; auto.
    + apply (IH Measured__Node__5 (Node w b) Measured__Node__5
        (nodeValidity (@measure w b _ _ B) Q)).
      intros; destruct x; cbn [mapWCNode];
        [apply node2_validity|apply node3_validity]; auto.
    + destruct sf; cbn [mapWCDigit digitValidity]; auto.
Qed.
End RebuiltValidity.

(* Positional implementations ignore right contexts. These equations compare
   actual source helpers, including their original dictionaries. *)
Section IgnoreRight.
Context {v w : Type} `{GHC.Base.Monoid v} `{GHC.Base.Monoid w}.
Lemma mapWPTree_context : forall a (t : FingerTree v a) (M : Measured v a)
  b (B : Measured w b) (f : v -> a -> b) l r,
  mapWPTree f l t = mapWCTree (fun l x _ => f l x) l t r.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    b (B : Measured w b) (f : v -> a -> b) l r,
    mapWPTree f l t = mapWCTree (fun l x _ => f l x) l t r) _ _ _).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros a cache pr m IH sf M b B f l r.
    cbn [mapWPTree mapWCTree].
    assert (D : forall l d r, mapWPDigit f l d = mapWCDigit (fun l x _ => f l x) l d r).
    { intros; destruct d; reflexivity. }
    rewrite (D l pr (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) r))), (D _ sf r).
    rewrite (IH Measured__Node__5 (Node w b) Measured__Node__5 (mapWPNode f) _
      (GHC.Base.mappend (measure sf) r)).
    assert (N : mapWCNode (fun l x _ => f l x) = (fun l x _ => mapWPNode f l x)).
    { reflexivity. }
    rewrite N; reflexivity.
Qed.
Lemma foldlWPTree_context : forall a (t : FingerTree v a) (M : Measured v a)
  b (f : b -> v -> a -> b) z l r,
  foldlWPTree f z l t = foldlWCTree (fun z l x _ => f z l x) z l t r.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    b (f : b -> v -> a -> b) z l r,
    foldlWPTree f z l t = foldlWCTree (fun z l x _ => f z l x) z l t r) _ _ _).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros a cache pr m IH sf M b f z l r.
    cbn [foldlWPTree foldlWCTree].
    assert (D : forall z l d r, foldlWPDigit f z l d = foldlWCDigit (fun z l x _ => f z l x) z l d r).
    { intros; destruct d; reflexivity. }
    rewrite (D z l pr (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) r))), (D _ _ sf r).
    rewrite (IH Measured__Node__5 b (foldlWPNode f) _ _ (GHC.Base.mappend (measure sf) r)).
    reflexivity.
Qed.
Lemma foldrWPTree_context : forall a (t : FingerTree v a) (M : Measured v a)
  b (f : v -> a -> b -> b) z l r,
  foldrWPTree f z l t = foldrWCTree (fun l x _ z => f l x z) z l t r.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    b (f : v -> a -> b -> b) z l r,
    foldrWPTree f z l t = foldrWCTree (fun l x _ z => f l x z) z l t r) _ _ _).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros a cache pr m IH sf M b f z l r.
    cbn [foldrWPTree foldrWCTree].
    assert (D : forall z l d r, foldrWPDigit f z l d = foldrWCDigit (fun l x _ z => f l x z) z l d r).
    { intros; destruct d; reflexivity. }
    rewrite (D z _ sf r), (D _ l pr (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) r))).
    rewrite (IH Measured__Node__5 b (foldrWPNode f) _ _ (GHC.Base.mappend (measure sf) r)).
    reflexivity.
Qed.
End IgnoreRight.

Section PublicContents.
Context {v : Type} `{GHC.Base.Monoid v}.
Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma fmapWithContext_contents {a w b} (M : Measured v a)
  (S : GHC.Base.Semigroup w) (N : GHC.Base.Monoid w) (B : Measured w b)
  (f : v -> a -> v -> b) (t : FingerTree v a) :
  validity M t -> contents (fmapWithContext f t) =
  contextMap (@measure v a _ _ M) f GHC.Base.mempty (contents t) GHC.Base.mempty.
Proof.
  intro V; unfold fmapWithContext, contents, contextMap.
  eapply (mapWCTree_contents assoc left_id right_id a t M (fun _ => True)
    a (fun x => [x]) (@measure v a _ _ M) w b S N B b f
    (fun x => [x]) (fun l x r => [f l x r])).
  - intros; cbn [listMeasure List.fold_right]; symmetry; apply right_id.
  - intros l x r _; symmetry; exact (contextFlatMap_singleton left_id
      (@measure v a _ _ M) (fun l x r => [f l x r]) l x r).
  - exact V.
Qed.

Lemma fmapWithPos_contents {a w b} (M : Measured v a)
  (S : GHC.Base.Semigroup w) (N : GHC.Base.Monoid w) (B : Measured w b)
  (f : v -> a -> b) (t : FingerTree v a) :
  validity M t -> contents (fmapWithPos f t) =
  positionMap (@measure v a _ _ M) f GHC.Base.mempty (contents t).
Proof.
  intro V; unfold fmapWithPos; rewrite (mapWPTree_context a t M b B f _ GHC.Base.mempty).
  change (contents (fmapWithContext (fun l x _ => f l x) t) =
    positionMap (@measure v a _ _ M) f GHC.Base.mempty (contents t)).
  rewrite (fmapWithContext_contents M S N B _ t V).
  unfold contextMap, positionMap; apply contextFlatMap_position.
Qed.

(* This auxiliary dictionary is used only to label leaves in the fold/map
   fusion proof. It does not replace any operation's source dictionary. *)
Definition contextTagMeasured {a} (M : Measured v a) : Measured v (v * a * v) :=
  fun R k => k {| measure__ := fun p => @measure v a _ _ M (snd (fst p)) |}.

Lemma foldlWithContext_contents {a b} (M : Measured v a)
  (f : b -> v -> a -> v -> b) z (t : FingerTree v a) :
  validity M t -> foldlWithContext f z t =
  contextFoldl (@measure v a _ _ M) f z GHC.Base.mempty (contents t) GHC.Base.mempty.
Proof.
  intro V; unfold foldlWithContext.
  rewrite (foldlWCTree_fusion a t M (v * a * v) (contextTagMeasured M)
    (v * a * v) b (fun x => [x])
    (fun z p => let '(l,x,r) := p in f z l x r) f (fun l x r => (l,x,r)))
    by reflexivity.
  change (List.fold_left (fun z p => let '(l,x,r) := p in f z l x r)
    (contents (@fmapWithContext v a v (v * a * v) H H0 M H H0 (contextTagMeasured M)
      (fun l x r => (l,x,r)) t)) z =
    contextFoldl (@measure v a _ _ M) f z GHC.Base.mempty (contents t) GHC.Base.mempty).
  rewrite (fmapWithContext_contents M H H0 (contextTagMeasured M) _ t V).
  reflexivity.
Qed.

Lemma foldrWithContext_contents {a b} (M : Measured v a)
  (f : v -> a -> v -> b -> b) z (t : FingerTree v a) :
  validity M t -> foldrWithContext f z t =
  contextFoldr (@measure v a _ _ M) f z GHC.Base.mempty (contents t) GHC.Base.mempty.
Proof.
  intro V; unfold foldrWithContext.
  rewrite (foldrWCTree_fusion a t M (v * a * v) (contextTagMeasured M)
    (v * a * v) b (fun x => [x])
    (fun p z => let '(l,x,r) := p in f l x r z) f (fun l x r => (l,x,r)))
    by reflexivity.
  change (List.fold_right (fun p z => let '(l,x,r) := p in f l x r z) z
    (contents (@fmapWithContext v a v (v * a * v) H H0 M H H0 (contextTagMeasured M)
      (fun l x r => (l,x,r)) t)) =
    contextFoldr (@measure v a _ _ M) f z GHC.Base.mempty (contents t) GHC.Base.mempty).
  rewrite (fmapWithContext_contents M H H0 (contextTagMeasured M) _ t V).
  reflexivity.
Qed.

Lemma contextFoldl_position {a b} (mu : a -> v) (f : b -> v -> a -> b) xs z l r :
  contextFoldl mu (fun z l x _ => f z l x) z l xs r = positionFoldl mu f z l xs.
Proof.
  unfold contextFoldl, contextMap, positionFoldl, positionMap.
  revert z l; induction xs as [|x xs IH]; intros; cbn; [reflexivity|apply IH].
Qed.
Lemma contextFoldr_position {a b} (mu : a -> v) (f : v -> a -> b -> b) xs z l r :
  contextFoldr mu (fun l x _ z => f l x z) z l xs r = positionFoldr mu f z l xs.
Proof.
  unfold contextFoldr, contextMap, positionFoldr, positionMap.
  revert l; induction xs as [|x xs IH]; intros; cbn; [reflexivity|rewrite IH; reflexivity].
Qed.
Lemma foldlWithPos_contents {a b} (M : Measured v a)
  (f : b -> v -> a -> b) z (t : FingerTree v a) :
  validity M t -> foldlWithPos f z t =
  positionFoldl (@measure v a _ _ M) f z GHC.Base.mempty (contents t).
Proof.
  intro V; unfold foldlWithPos; rewrite (foldlWPTree_context a t M b f z _ GHC.Base.mempty).
  change (foldlWithContext (fun z l x _ => f z l x) z t =
    positionFoldl (@measure v a _ _ M) f z GHC.Base.mempty (contents t)).
  rewrite (foldlWithContext_contents M _ z t V); apply contextFoldl_position.
Qed.
Lemma foldrWithPos_contents {a b} (M : Measured v a)
  (f : v -> a -> b -> b) z (t : FingerTree v a) :
  validity M t -> foldrWithPos f z t =
  positionFoldr (@measure v a _ _ M) f z GHC.Base.mempty (contents t).
Proof.
  intro V; unfold foldrWithPos; rewrite (foldrWPTree_context a t M b f z _ GHC.Base.mempty).
  change (foldrWithContext (fun l x _ z => f l x z) z t =
    positionFoldr (@measure v a _ _ M) f z GHC.Base.mempty (contents t)).
  rewrite (foldrWithContext_contents M _ z t V); apply contextFoldr_position.
Qed.
End PublicContents.

Section PublicValidity.
Context {v w : Type} `{GHC.Base.Monoid v} `{GHC.Base.Monoid w}.

Lemma mapWCTree_preserves : forall a (t : FingerTree v a) (M : Measured v a)
  b (B : Measured w b) (P : a -> Prop) (Q : b -> Prop) (f : v -> a -> v -> b),
  (forall l x r, P x -> Q (f l x r)) -> validityWith (@measure v a _ _ M) P t ->
  forall l r, validityWith (@measure w b _ _ B) Q (mapWCTree f l t r).
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    b (B : Measured w b) (P : a -> Prop) (Q : b -> Prop) (f : v -> a -> v -> b),
    (forall l x r, P x -> Q (f l x r)) -> validityWith (@measure v a _ _ M) P t ->
    forall l r, validityWith (@measure w b _ _ B) Q (mapWCTree f l t r)) _ _ _).
  - intros; exact I.
  - intros; apply H3; assumption.
  - intros a cache pr m IH sf M b B P Q f E [Vp [Vm [Vs Ec]]] l r.
    cbn [mapWCTree]; apply deep_validityWith.
    + destruct pr; cbn [mapWCDigit digitValidity] in *; repeat split; apply E; tauto.
    + apply (IH Measured__Node__5 (Node w b) Measured__Node__5
        (nodeValidity (@measure v a _ _ M) P) (nodeValidity (@measure w b _ _ B) Q)); [|exact Vm].
      intros l' n r' Vn; destruct n; cbn [nodeValidity] in Vn; cbn [mapWCNode];
        [apply node2_validity|apply node3_validity]; apply E; tauto.
    + destruct sf; cbn [mapWCDigit digitValidity] in *; repeat split; apply E; tauto.
Qed.

Lemma fmapWithContext_validityWith {a b} (M : Measured v a) (B : Measured w b)
  Q (f : v -> a -> v -> b) (t : FingerTree v a) :
  (forall l x r, Q (f l x r)) -> validityWith (@measure w b _ _ B) Q (fmapWithContext f t).
Proof. intro E; exact (mapWCTree_validityWith a t M b B Q f E _ _). Qed.
Lemma fmapWithContext_validity {a b} (M : Measured v a) (B : Measured w b)
  (f : v -> a -> v -> b) (t : FingerTree v a) : validity B (fmapWithContext f t).
Proof. apply fmapWithContext_validityWith; auto. Qed.
Lemma fmapWithContext_preserves {a b} (M : Measured v a) (B : Measured w b)
  P Q (f : v -> a -> v -> b) (t : FingerTree v a) :
  (forall l x r, P x -> Q (f l x r)) -> validityWith (@measure v a _ _ M) P t ->
  validityWith (@measure w b _ _ B) Q (fmapWithContext f t).
Proof. intros E V; exact (mapWCTree_preserves a t M b B P Q f E V _ _). Qed.
Lemma fmapWithPos_validityWith {a b} (M : Measured v a) (B : Measured w b)
  Q (f : v -> a -> b) (t : FingerTree v a) :
  (forall l x, Q (f l x)) -> validityWith (@measure w b _ _ B) Q (fmapWithPos f t).
Proof.
  intro E; unfold fmapWithPos; rewrite (mapWPTree_context a t M b B f _ GHC.Base.mempty).
  apply mapWCTree_validityWith; auto.
Qed.
Lemma fmapWithPos_validity {a b} (M : Measured v a) (B : Measured w b)
  (f : v -> a -> b) (t : FingerTree v a) : validity B (fmapWithPos f t).
Proof. apply fmapWithPos_validityWith; auto. Qed.
Lemma fmapWithPos_preserves {a b} (M : Measured v a) (B : Measured w b)
  P Q (f : v -> a -> b) (t : FingerTree v a) :
  (forall l x, P x -> Q (f l x)) -> validityWith (@measure v a _ _ M) P t ->
  validityWith (@measure w b _ _ B) Q (fmapWithPos f t).
Proof.
  intros E V; unfold fmapWithPos; rewrite (mapWPTree_context a t M b B f _ GHC.Base.mempty).
  eapply mapWCTree_preserves; eauto.
Qed.
End PublicValidity.

Section ReferenceAccuracy.
Context {v : Type} `{GHC.Base.Monoid v}.
Definition leftMeasure {a} (mu : a -> v) (l : v) (xs : list a) : v :=
  List.fold_left (fun l x => GHC.Base.mappend l (mu x)) xs l.
Definition rightMeasure {a} (mu : a -> v) (xs : list a) (r : v) : v :=
  List.fold_right (fun x r => GHC.Base.mappend (mu x) r) r xs.

Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma leftMeasure_value {a} (mu : a -> v) xs l :
  leftMeasure mu l xs = GHC.Base.mappend l (listMeasure mu xs).
Proof.
  unfold leftMeasure; revert l; induction xs; intro l; cbn [List.fold_left listMeasure List.fold_right].
  - symmetry; apply right_id.
  - rewrite IHxs, assoc; reflexivity.
Qed.
Lemma rightMeasure_value {a} (mu : a -> v) xs r :
  rightMeasure mu xs r = GHC.Base.mappend (listMeasure mu xs) r.
Proof.
  unfold rightMeasure; induction xs; cbn [List.fold_right listMeasure].
  - symmetry; apply left_id.
  - rewrite IHxs, assoc; reflexivity.
Qed.

Lemma contextMap_length {a b} (mu : a -> v) (f : v -> a -> v -> b) xs l r :
  Corelib.Init.Datatypes.length (contextMap mu f l xs r) = Corelib.Init.Datatypes.length xs.
Proof.
  unfold contextMap; revert l; induction xs; intros; [reflexivity|].
  change (S (Corelib.Init.Datatypes.length (contextFlatMap mu (fun l x r => [f l x r])
    (GHC.Base.mappend l (mu a0)) xs r)) = S (Corelib.Init.Datatypes.length xs)).
  rewrite IHxs; reflexivity.
Qed.

Lemma contextMap_app {a b} (mu : a -> v) (f : v -> a -> v -> b) xs ys l r :
  contextMap mu f l (xs ++ ys) r =
  contextMap mu f l xs (GHC.Base.mappend (listMeasure mu ys) r) ++
  contextMap mu f (GHC.Base.mappend l (listMeasure mu xs)) ys r.
Proof. apply contextFlatMap_app; assumption. Qed.

Lemma contextMap_original_at {a b} (mu : a -> v) (f : v -> a -> v -> b) pre x post :
  List.nth_error (contextMap mu f GHC.Base.mempty (pre ++ x :: post) GHC.Base.mempty)
    (Corelib.Init.Datatypes.length pre) = Some (f (listMeasure mu pre) x (listMeasure mu post)).
Proof.
  rewrite contextMap_app, List.nth_error_app2 by (rewrite contextMap_length; reflexivity).
  rewrite contextMap_length, PeanoNat.Nat.sub_diag.
  cbn [contextMap contextFlatMap List.nth_error].
  rewrite left_id, right_id; reflexivity.
Qed.

Lemma positionMap_original_at {a b} (mu : a -> v) (f : v -> a -> b) pre x post :
  List.nth_error (positionMap mu f GHC.Base.mempty (pre ++ x :: post))
    (Corelib.Init.Datatypes.length pre) = Some (f (listMeasure mu pre) x).
Proof.
  unfold positionMap.
  rewrite <- (contextFlatMap_position mu (fun l x => [f l x])
    (pre ++ x :: post) GHC.Base.mempty GHC.Base.mempty).
  exact (contextMap_original_at mu (fun l x _ => f l x) pre x post).
Qed.

(* The two equations below make fold association explicit, independently of
   the source folds and without an associativity premise on the callback. *)
Lemma contextFoldl_cons {a b} (mu : a -> v) (f : b -> v -> a -> v -> b) z l x xs r :
  contextFoldl mu f z l (x :: xs) r = contextFoldl mu f
    (f z l x (GHC.Base.mappend (listMeasure mu xs) r))
    (GHC.Base.mappend l (mu x)) xs r.
Proof. reflexivity. Qed.
Lemma contextFoldr_cons {a b} (mu : a -> v) (f : v -> a -> v -> b -> b) z l x xs r :
  contextFoldr mu f z l (x :: xs) r =
  f l x (GHC.Base.mappend (listMeasure mu xs) r)
    (contextFoldr mu f z (GHC.Base.mappend l (mu x)) xs r).
Proof. reflexivity. Qed.
End ReferenceAccuracy.

Section OutputMeasures.
Context {v w : Type} `{GHC.Base.Monoid v} `{GHC.Base.Monoid w}.
Hypothesis assoc_v : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_v : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_v : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.
Hypothesis assoc_w : forall x y z : w, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_w : forall x : w, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_w : forall x : w, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma fmapWithContext_measure {a b} (M : Measured v a) (B : Measured w b)
  (f : v -> a -> v -> b) (t : FingerTree v a) : validity M t ->
  measure (fmapWithContext f t) = listMeasure (@measure w b _ _ B)
    (contextMap (@measure v a _ _ M) f GHC.Base.mempty (contents t) GHC.Base.mempty).
Proof.
  intro V; rewrite (measure_contents assoc_w left_w right_w B _)
    by apply fmapWithContext_validity.
  rewrite (fmapWithContext_contents assoc_v left_v right_v M H1 H2 B f t V); reflexivity.
Qed.
Lemma fmapWithPos_measure {a b} (M : Measured v a) (B : Measured w b)
  (f : v -> a -> b) (t : FingerTree v a) : validity M t ->
  measure (fmapWithPos f t) = listMeasure (@measure w b _ _ B)
    (positionMap (@measure v a _ _ M) f GHC.Base.mempty (contents t)).
Proof.
  intro V; rewrite (measure_contents assoc_w left_w right_w B _)
    by apply fmapWithPos_validity.
  rewrite (fmapWithPos_contents assoc_v left_v right_v M H1 H2 B f t V); reflexivity.
Qed.
End OutputMeasures.

Check @contextFlatMap. Print Assumptions contextFlatMap.
Check @contextMap. Print Assumptions contextMap.
Check @contextFoldl. Print Assumptions contextFoldl.
Check @contextFoldr. Print Assumptions contextFoldr.
Check @positionFlatMap. Print Assumptions positionFlatMap.
Check @positionMap. Print Assumptions positionMap.
Check @positionFoldl. Print Assumptions positionFoldl.
Check @positionFoldr. Print Assumptions positionFoldr.
Check @contextFlatMap_app. Print Assumptions contextFlatMap_app.
Check @contextFlatMap_ext. Print Assumptions contextFlatMap_ext.
Check @contextFlatMap_singleton. Print Assumptions contextFlatMap_singleton.
Check @contextFlatMap_position. Print Assumptions contextFlatMap_position.
Check @contextFlatMap_at. Print Assumptions contextFlatMap_at.
Check @mapWCDigit_contents. Print Assumptions mapWCDigit_contents.
Check @mapWCNode_contents. Print Assumptions mapWCNode_contents.
Check @mapWCTree_contents. Print Assumptions mapWCTree_contents.
Check @foldlWCTree_fusion. Print Assumptions foldlWCTree_fusion.
Check @foldrWCTree_fusion. Print Assumptions foldrWCTree_fusion.
Check @mapWCTree_validityWith. Print Assumptions mapWCTree_validityWith.
Check @mapWPTree_context. Print Assumptions mapWPTree_context.
Check @foldlWPTree_context. Print Assumptions foldlWPTree_context.
Check @foldrWPTree_context. Print Assumptions foldrWPTree_context.
Check @fmapWithContext_contents. Print Assumptions fmapWithContext_contents.
Check @fmapWithPos_contents. Print Assumptions fmapWithPos_contents.
Check @contextTagMeasured. Print Assumptions contextTagMeasured.
Check @foldlWithContext_contents. Print Assumptions foldlWithContext_contents.
Check @foldrWithContext_contents. Print Assumptions foldrWithContext_contents.
Check @contextFoldl_position. Print Assumptions contextFoldl_position.
Check @contextFoldr_position. Print Assumptions contextFoldr_position.
Check @foldlWithPos_contents. Print Assumptions foldlWithPos_contents.
Check @foldrWithPos_contents. Print Assumptions foldrWithPos_contents.
Check @mapWCTree_preserves. Print Assumptions mapWCTree_preserves.
Check @fmapWithContext_validityWith. Print Assumptions fmapWithContext_validityWith.
Check @fmapWithContext_validity. Print Assumptions fmapWithContext_validity.
Check @fmapWithContext_preserves. Print Assumptions fmapWithContext_preserves.
Check @fmapWithPos_validityWith. Print Assumptions fmapWithPos_validityWith.
Check @fmapWithPos_validity. Print Assumptions fmapWithPos_validity.
Check @fmapWithPos_preserves. Print Assumptions fmapWithPos_preserves.
Check @leftMeasure. Print Assumptions leftMeasure.
Check @rightMeasure. Print Assumptions rightMeasure.
Check @leftMeasure_value. Print Assumptions leftMeasure_value.
Check @rightMeasure_value. Print Assumptions rightMeasure_value.
Check @contextMap_length. Print Assumptions contextMap_length.
Check @contextMap_app. Print Assumptions contextMap_app.
Check @contextMap_original_at. Print Assumptions contextMap_original_at.
Check @positionMap_original_at. Print Assumptions positionMap_original_at.
Check @contextFoldl_cons. Print Assumptions contextFoldl_cons.
Check @contextFoldr_cons. Print Assumptions contextFoldr_cons.
Check @fmapWithContext_measure. Print Assumptions fmapWithContext_measure.
Check @fmapWithPos_measure. Print Assumptions fmapWithPos_measure.
