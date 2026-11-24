From Stdlib Require Import Lists.List.
Require Import Data.FingerTree FingerTreeProofs.CoreModel FingerTreeProofs.CoreSize.
Import ListNotations.

Local Ltac lists := repeat rewrite <- List.app_assoc; rewrite ?List.app_nil_r; reflexivity.

Section Raw.
Context {v : Type} `{GHC.Base.Monoid v}.

Lemma digitToTree_contentsWith {a b} (M : Measured v a) (f : a -> list b) d :
  contentsWith f (digitToTree d) = digitContentsWith f d.
Proof. destruct d; cbn [digitToTree deep contentsWith digitContentsWith]; lists. Qed.

Lemma nodeToDigit_contentsWith {a b} (f : a -> list b) (n : Node v a) :
  digitContentsWith f (nodeToDigit n) = nodeContentsWith f n.
Proof. destruct n; reflexivity. Qed.

Lemma consTree_contentsWith : forall a (t : FingerTree v a) (M : Measured v a)
  b (f : a -> list b) x, contentsWith f (consTree x t) = f x ++ contentsWith f t.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    b (f : a -> list b) x, contentsWith f (consTree x t) = f x ++ contentsWith f t) _ _ _).
  - intros; cbn; lists.
  - intros; cbn [consTree deep contentsWith digitContentsWith]; lists.
  - intros a c pr m IH sf M b f x.
    destruct pr; cbn [consTree deep contentsWith digitContentsWith consDigit GHC.Prim.seq];
      try lists.
    rewrite IH; cbn [nodeContentsWith node3]; lists.
Qed.

Lemma mapTree_contentsWith {v1} : forall a (t : FingerTree v1 a)
  v2 b (S : GHC.Base.Semigroup v2) (N : GHC.Base.Monoid v2)
  (M : Measured v2 b) c (f : a -> b) (g : b -> list c) h,
  (forall x, g (f x) = h x) ->
  contentsWith g (mapTree f t) = contentsWith h t.
Proof.
  refine (FingerTree_rect v1 (fun a t => forall v2 b
    (S : GHC.Base.Semigroup v2) (N : GHC.Base.Monoid v2) (M : Measured v2 b)
    c (f : a -> b) (g : b -> list c) h,
    (forall x, g (f x) = h x) ->
    contentsWith g (mapTree f t) = contentsWith h t) _ _ _).
  - intros; reflexivity.
  - intros a x v2 b S N M c f g h E; exact (E x).
  - intros a cache pr m IH sf v2 b S N M c f g h E.
    cbn [mapTree deep contentsWith].
    assert (D : forall d, digitContentsWith g (mapDigit f d) = digitContentsWith h d).
    { intro d; destruct d; cbn [mapDigit digitContentsWith]; repeat rewrite E; reflexivity. }
    rewrite !D; f_equal; f_equal.
    apply IH; intro n; destruct n; cbn [mapNode node2 node3 nodeContentsWith];
      repeat rewrite E; reflexivity.
Qed.

Lemma snocTree_contentsWith : forall a (t : FingerTree v a) (M : Measured v a)
  b (f : a -> list b) x, contentsWith f (snocTree t x) = contentsWith f t ++ f x.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    b (f : a -> list b) x, contentsWith f (snocTree t x) = contentsWith f t ++ f x) _ _ _).
  - intros; reflexivity.
  - intros; cbn [snocTree deep contentsWith digitContentsWith]; lists.
  - intros a c pr m IH sf M b f x.
    destruct sf; cbn [snocTree deep contentsWith digitContentsWith snocDigit GHC.Prim.seq];
      try lists.
    rewrite IH; cbn [nodeContentsWith node3]; lists.
Qed.

Lemma appendTree234_contentsWith : forall a (t : FingerTree v a) (M : Measured v a)
  b (f : a -> list b),
  (forall x y r, contentsWith f (appendTree2 t x y r) =
    contentsWith f t ++ f x ++ f y ++ contentsWith f r) /\
  (forall x y z r, contentsWith f (appendTree3 t x y z r) =
    contentsWith f t ++ f x ++ f y ++ f z ++ contentsWith f r) /\
  (forall x y z w r, contentsWith f (appendTree4 t x y z w r) =
    contentsWith f t ++ f x ++ f y ++ f z ++ f w ++ contentsWith f r).
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) b (f : a -> list b),
    (forall x y r, contentsWith f (appendTree2 t x y r) =
      contentsWith f t ++ f x ++ f y ++ contentsWith f r) /\
    (forall x y z r, contentsWith f (appendTree3 t x y z r) =
      contentsWith f t ++ f x ++ f y ++ f z ++ contentsWith f r) /\
    (forall x y z w r, contentsWith f (appendTree4 t x y z w r) =
      contentsWith f t ++ f x ++ f y ++ f z ++ f w ++ contentsWith f r)) _ _ _).
  - intros a M b f; repeat split; intros;
      cbn [appendTree2 appendTree3 appendTree4 contentsWith];
      repeat rewrite consTree_contentsWith; lists.
  - intros a u M b f; repeat split; intros;
      destruct r; cbn [appendTree2 appendTree3 appendTree4];
      repeat rewrite consTree_contentsWith; repeat rewrite snocTree_contentsWith;
      cbn [contentsWith]; lists.
  - intros a c pr m IH sf M b f.
    destruct (IH Measured__Node__5 b (nodeContentsWith f)) as [I2 [I3 I4]].
    repeat split; intros.
    + destruct r as [|u|c2 pr2 m2 sf2].
      * cbn [appendTree2]; repeat rewrite snocTree_contentsWith; cbn [contentsWith]; lists.
      * cbn [appendTree2]; repeat rewrite snocTree_contentsWith; cbn [contentsWith]; lists.
      * rewrite appendTree2_deep; cbn [deep contentsWith].
        destruct sf; destruct pr2; cbn [addDigits2];
          rewrite ?I2, ?I3, ?I4; cbn [nodeContentsWith node2 node3 digitContentsWith]; lists.
    + destruct r as [|u|c2 pr2 m2 sf2].
      * cbn [appendTree3]; repeat rewrite snocTree_contentsWith; cbn [contentsWith]; lists.
      * cbn [appendTree3]; repeat rewrite snocTree_contentsWith; cbn [contentsWith]; lists.
      * rewrite appendTree3_deep; cbn [deep contentsWith].
        destruct sf; destruct pr2; cbn [addDigits3];
          rewrite ?I2, ?I3, ?I4; cbn [nodeContentsWith node2 node3 digitContentsWith]; lists.
    + destruct r as [|u|c2 pr2 m2 sf2].
      * cbn [appendTree4]; repeat rewrite snocTree_contentsWith; cbn [contentsWith]; lists.
      * cbn [appendTree4]; repeat rewrite snocTree_contentsWith; cbn [contentsWith]; lists.
      * rewrite appendTree4_deep; cbn [deep contentsWith].
        destruct sf; destruct pr2; cbn [addDigits4];
          rewrite ?I2, ?I3, ?I4; cbn [nodeContentsWith node2 node3 digitContentsWith]; lists.
Qed.

Lemma appendTree1_contentsWith : forall a (t : FingerTree v a) (M : Measured v a)
  b (f : a -> list b) x r, contentsWith f (appendTree1 t x r) =
    contentsWith f t ++ f x ++ contentsWith f r.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    b (f : a -> list b) x r, contentsWith f (appendTree1 t x r) =
      contentsWith f t ++ f x ++ contentsWith f r) _ _ _).
  - intros; cbn [appendTree1 contentsWith]; rewrite consTree_contentsWith; reflexivity.
  - intros a u M b f x r; destruct r;
      cbn [appendTree1]; repeat rewrite consTree_contentsWith;
      repeat rewrite snocTree_contentsWith; cbn [contentsWith]; lists.
  - intros a c pr m IH sf M b f x r.
    pose proof (IH Measured__Node__5 b (nodeContentsWith f)) as I1.
    destruct (appendTree234_contentsWith _ m Measured__Node__5 b (nodeContentsWith f))
      as [I2 [I3 I4]].
    destruct r as [|u|c2 pr2 m2 sf2].
    + cbn [appendTree1]; repeat rewrite snocTree_contentsWith; cbn [contentsWith]; lists.
    + cbn [appendTree1]; repeat rewrite snocTree_contentsWith; cbn [contentsWith]; lists.
    + rewrite appendTree1_deep; cbn [deep contentsWith].
      destruct sf; destruct pr2; cbn [addDigits1];
        rewrite ?I1, ?I2, ?I3; cbn [nodeContentsWith node2 node3 digitContentsWith]; lists.
Qed.

Lemma append_contentsWith {a b} (M : Measured v a) (f : a -> list b) l r :
  contentsWith f (op_zgzl__ l r) = contentsWith f l ++ contentsWith f r.
Proof.
  destruct l as [|x|c1 pr1 m1 sf1]; destruct r as [|y|c2 pr2 m2 sf2];
    cbn [op_zgzl__ appendTree0];
    rewrite ?consTree_contentsWith, ?snocTree_contentsWith; cbn [contentsWith]; try lists.
  pose proof (appendTree1_contentsWith _ m1 Measured__Node__5 b (nodeContentsWith f)) as I1.
  destruct (appendTree234_contentsWith _ m1 Measured__Node__5 b (nodeContentsWith f))
    as [I2 [I3 I4]].
  cbn [deep contentsWith]; destruct sf1; destruct pr2; cbn [addDigits0];
    rewrite ?I1, ?I2, ?I3; cbn [nodeContentsWith node2 node3 digitContentsWith]; lists.
Qed.

Lemma viewl_contentsWith : forall a (t : FingerTree v a) (M : Measured v a)
  b (f : a -> list b),
  match @viewl v a _ _ M t with
  | EmptyL => contentsWith f t = []
  | op_ZCzl__ x r => contentsWith f t = f x ++ contentsWith f r
  end.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) b (f : a -> list b),
    match @viewl v a _ _ M t with
    | EmptyL => contentsWith f t = []
    | op_ZCzl__ x r => contentsWith f t = f x ++ contentsWith f r
    end) _ _ _).
  - intros; reflexivity.
  - intros; cbn; lists.
  - intros a c pr m IH sf M b f.
    specialize (IH Measured__Node__5 b (nodeContentsWith f)).
    destruct pr as [x|x y|x y z|x y z w];
      cbn [viewl lheadDigit ltailDigit deep contentsWith digitContentsWith] in *;
      try lists.
    destruct (viewl m) as [|n r] eqn:E.
    + rewrite digitToTree_contentsWith, IH; lists.
    + cbn [contentsWith]; rewrite nodeToDigit_contentsWith, IH; lists.
Qed.

Lemma viewr_contentsWith : forall a (t : FingerTree v a) (M : Measured v a)
  b (f : a -> list b),
  match @viewr v a _ _ M t with
  | EmptyR => contentsWith f t = []
  | op_ZCzg__ l x => contentsWith f t = contentsWith f l ++ f x
  end.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) b (f : a -> list b),
    match @viewr v a _ _ M t with
    | EmptyR => contentsWith f t = []
    | op_ZCzg__ l x => contentsWith f t = contentsWith f l ++ f x
    end) _ _ _).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros a c pr m IH sf M b f.
    specialize (IH Measured__Node__5 b (nodeContentsWith f)).
    destruct sf as [x|x y|x y z|x y z w];
      cbn [viewr rheadDigit rtailDigit deep contentsWith digitContentsWith] in *; try lists.
    destruct (viewr m) as [|r n] eqn:E.
    + rewrite digitToTree_contentsWith, IH; lists.
    + cbn [contentsWith]; rewrite nodeToDigit_contentsWith, IH; lists.
Qed.

Lemma rotL_contentsWith {a b} (M : Measured v a) (f : a -> list b) m sf :
  contentsWith f (rotL m sf) = contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf.
Proof.
  pose proof (viewl_contentsWith _ m Measured__Node__5 b (nodeContentsWith f)) as E.
  unfold rotL; destruct (viewl m) as [|n r].
  - rewrite digitToTree_contentsWith, E; reflexivity.
  - cbn [contentsWith]; rewrite nodeToDigit_contentsWith, E; lists.
Qed.

Lemma rotR_contentsWith {a b} (M : Measured v a) (f : a -> list b) pr m :
  contentsWith f (rotR pr m) = digitContentsWith f pr ++ contentsWith (nodeContentsWith f) m.
Proof.
  pose proof (viewr_contentsWith _ m Measured__Node__5 b (nodeContentsWith f)) as E.
  unfold rotR; destruct (viewr m) as [|r n].
  - rewrite digitToTree_contentsWith, E; lists.
  - cbn [contentsWith]; rewrite nodeToDigit_contentsWith, E; lists.
Qed.

Lemma deepL_contentsWith {a b} (M : Measured v a) (f : a -> list b) pr m sf :
  contentsWith f (deepL pr m sf) =
    (match pr with None => [] | Some d => digitContentsWith f d end) ++
      contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf.
Proof. destruct pr; cbn [deepL deep contentsWith]; [reflexivity|apply rotL_contentsWith]. Qed.

Lemma deepR_contentsWith {a b} (M : Measured v a) (f : a -> list b) pr m sf :
  contentsWith f (deepR pr m sf) = digitContentsWith f pr ++ contentsWith (nodeContentsWith f) m ++
    (match sf with None => [] | Some d => digitContentsWith f d end).
Proof.
  destruct sf; cbn [deepR deep contentsWith]; [reflexivity|].
  rewrite rotR_contentsWith; lists.
Qed.

Lemma splitDigit_contentsWith {a b} (M : Measured v a) (f : a -> list b) p i d :
  let '(MkSplit l x r) := splitDigit p i d in
  digitContentsWith f d = (match l with None => [] | Some d => digitContentsWith f d end) ++
    f x ++ (match r with None => [] | Some d => digitContentsWith f d end).
Proof.
  destruct d; cbn [splitDigit digitContentsWith GHC.Prim.seq];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [digitContentsWith]; lists.
Qed.

Lemma splitNode_contentsWith {a b} (M : Measured v a) (f : a -> list b) p i n :
  let '(MkSplit l x r) := splitNode p i n in
  nodeContentsWith f n = (match l with None => [] | Some d => digitContentsWith f d end) ++
    f x ++ (match r with None => [] | Some d => digitContentsWith f d end).
Proof.
  destruct n; cbn [splitNode nodeContentsWith];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [digitContentsWith]; lists.
Qed.

Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma splitTree_contentsWith : forall a (t : FingerTree v a) (M : Measured v a)
  (D : HsToRocq.Err.Default a) b (f : a -> list b) p i, t <> Empty ->
  let '(MkSplit l x r) := @splitTree v a _ _ M D p i t in
  contentsWith f t = contentsWith f l ++ f x ++ contentsWith f r.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    (D : HsToRocq.Err.Default a) b (f : a -> list b) p i, t <> Empty ->
    let '(MkSplit l x r) := @splitTree v a _ _ M D p i t in
    contentsWith f t = contentsWith f l ++ f x ++ contentsWith f r) _ _ _).
  - intros; contradiction.
  - intros; cbn; lists.
  - intros a c pr m IH sf M D b f p i NE.
    cbn [splitTree].
    destruct (p (GHC.Base.mappend i (measure pr))) eqn:Epr.
    + pose proof (splitDigit_contentsWith M f p i pr) as Ed.
      destruct (splitDigit p i pr) as [l x r].
      rewrite deepL_contentsWith.
      destruct l; cbn [Data.Maybe.maybe contentsWith] in *;
        rewrite ?digitToTree_contentsWith; cbn [contentsWith]; rewrite Ed; lists.
    + destruct (p (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m))) eqn:Em.
      * assert (Nm : m <> Empty).
        { eapply split_middle_nonempty; eassumption. }
        specialize (IH Measured__Node__5 DefaultNode b (nodeContentsWith f) p
          (GHC.Base.mappend i (measure pr)) Nm).
        destruct (splitTree p (GHC.Base.mappend i (measure pr)) m) as [ml n mr].
        pose proof (splitNode_contentsWith M f p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure ml)) n) as En.
        destruct (splitNode p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure ml)) n)
          as [l x r].
        rewrite deepL_contentsWith, deepR_contentsWith; cbn [contentsWith];
          rewrite IH, En; lists.
      * pose proof (splitDigit_contentsWith M f p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m)) sf) as Ed.
        destruct (splitDigit p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m)) sf)
          as [l x r].
        rewrite deepR_contentsWith.
        destruct r; cbn [Data.Maybe.maybe contentsWith] in *;
          rewrite ?digitToTree_contentsWith; cbn [contentsWith]; rewrite Ed; lists.
Qed.

Lemma split_contentsWith {a b} (M : Measured v a) (f : a -> list b) p t :
  let '(l, r) := split p t in contentsWith f t = contentsWith f l ++ contentsWith f r.
Proof.
  unfold split; destruct t as [|u|c pr m sf];
    cbn -[splitTree consTree contentsWith]; try reflexivity;
    match goal with
    | |- context [@splitTree v a _ _ M ?D ?p ?i ?t] =>
        pose proof (splitTree_contentsWith a t M D b f p i ltac:(discriminate)) as E;
        destruct (@splitTree v a _ _ M D p i t) as [l x r]
    end;
    destruct (Bool.Sumbool.sumbool_of_bool _);
    rewrite ?consTree_contentsWith; cbn [contentsWith] in *; try rewrite E; lists.
Qed.
End Raw.

Lemma digitContentsWith_map {a b c} (f : a -> b) (g : b -> list c) h d :
  (forall x, g (f x) = h x) ->
  digitContentsWith g (mapDigit f d) = digitContentsWith h d.
Proof. intro E; destruct d; cbn [digitContentsWith mapDigit]; repeat rewrite E; reflexivity. Qed.

Lemma contentsWith_ext {v} : forall a (t : FingerTree v a) b (f g : a -> list b),
  (forall x, f x = g x) -> contentsWith f t = contentsWith g t.
Proof.
  refine (FingerTree_rect v (fun a t => forall b (f g : a -> list b),
    (forall x, f x = g x) -> contentsWith f t = contentsWith g t) _ _ _).
  - intros; reflexivity.
  - intros a x b f g E; exact (E x).
  - intros a c pr m IH sf b f g E; cbn [contentsWith].
    assert (D : forall d, digitContentsWith f d = digitContentsWith g d).
    { intro d; destruct d; cbn [digitContentsWith]; repeat rewrite E; reflexivity. }
    rewrite !D; f_equal; f_equal; apply IH.
    intro n; destruct n; cbn [nodeContentsWith]; repeat rewrite E; reflexivity.
Qed.

Lemma contentsWith_flat_map {v A B} (F : A -> list B) : forall (t : FingerTree v A),
  contentsWith F t = List.flat_map F (contents t).
Proof.
  (* Generalize the interpretation, since middle elements represent blocks. *)
  assert (G : forall a (t : FingerTree v a) c (g : a -> list c) b (k : c -> list b),
    contentsWith (fun x => List.flat_map k (g x)) t = List.flat_map k (contentsWith g t)).
  { refine (FingerTree_rect v (fun a t => forall c (g : a -> list c) b (k : c -> list b),
      contentsWith (fun x => List.flat_map k (g x)) t = List.flat_map k (contentsWith g t)) _ _ _).
    - intros; reflexivity.
    - intros; reflexivity.
    - intros a cache pr m IH sf c g b k.
      cbn [contentsWith]; rewrite !List.flat_map_app.
      assert (D : forall d, digitContentsWith (fun x => List.flat_map k (g x)) d =
        List.flat_map k (digitContentsWith g d)).
      { intro d; destruct d; cbn [digitContentsWith]; rewrite ?List.flat_map_app; reflexivity. }
      rewrite !D; f_equal; f_equal.
      transitivity (contentsWith (fun n : Node v a => List.flat_map k (nodeContentsWith g n)) m).
      + apply contentsWith_ext; intro n; destruct n; cbn [nodeContentsWith];
          rewrite ?List.flat_map_app; reflexivity.
      + apply IH. }
  intro t; specialize (G A t A (fun x => [x]) B F).
  cbn [List.flat_map List.app] in G.
  unfold contents; rewrite <- G; apply contentsWith_ext; intro x; symmetry; apply List.app_nil_r.
Qed.

Lemma contentsWith_singletons {v a b} (f : a -> b) (t : FingerTree v a) :
  contentsWith (fun x => [f x]) t = List.map f (contents t).
Proof.
  rewrite contentsWith_flat_map.
  induction (contents t); cbn; [reflexivity|rewrite IHl; reflexivity].
Qed.

Lemma fmap'_contents {v1 a v2 b} `{Measured v1 a} `{Measured v2 b}
  (f : a -> b) (t : FingerTree v1 a) :
  contents (fmap' f t) = List.map f (contents t).
Proof.
  unfold contents, fmap'; rewrite (mapTree_contentsWith a t v2 b _ _ _ b f
    (fun x => [x]) (fun x => [f x]) ltac:(reflexivity)).
  apply contentsWith_singletons.
Qed.

Lemma unsafeFmap_contentsWith {v} : forall a (t : FingerTree v a)
  b c (f : a -> b) (g : b -> list c) h,
  (forall x, g (f x) = h x) ->
  contentsWith g (unsafeFmap f t) = contentsWith h t.
Proof.
  refine (FingerTree_rect v (fun a t => forall b c (f : a -> b)
    (g : b -> list c) h, (forall x, g (f x) = h x) ->
    contentsWith g (unsafeFmap f t) = contentsWith h t) _ _ _).
  - intros; reflexivity.
  - intros a x b c f g h E; exact (E x).
  - intros a cache pr m IH sf b c f g h E; cbn [unsafeFmap contentsWith].
    rewrite (digitContentsWith_map f g h pr E), (digitContentsWith_map f g h sf E).
    f_equal; f_equal; apply IH.
    intro n; destruct n; cbn [unsafeFmapNode nodeContentsWith]; repeat rewrite E; reflexivity.
Qed.

Lemma unsafeFmap_contents {v a b} (f : a -> b) (t : FingerTree v a) :
  contents (unsafeFmap f t) = List.map f (contents t).
Proof.
  unfold contents; rewrite (unsafeFmap_contentsWith a t b b f
    (fun x => [x]) (fun x => [f x]) ltac:(reflexivity)).
  apply contentsWith_singletons.
Qed.

Lemma reverseTree_contentsWith {v1} : forall a (t : FingerTree v1 a)
  v2 b (S : GHC.Base.Semigroup v2) (N : GHC.Base.Monoid v2)
  (M : Measured v2 b) c (f : a -> b) (g : b -> list c) h,
  (forall x, g (f x) = List.rev (h x)) ->
  contentsWith g (reverseTree f t) = List.rev (contentsWith h t).
Proof.
  refine (FingerTree_rect v1 (fun a t => forall v2 b
    (S : GHC.Base.Semigroup v2) (N : GHC.Base.Monoid v2) (M : Measured v2 b)
    c (f : a -> b) (g : b -> list c) h,
    (forall x, g (f x) = List.rev (h x)) ->
    contentsWith g (reverseTree f t) = List.rev (contentsWith h t)) _ _ _).
  - intros; reflexivity.
  - intros a x v2 b S N M c f g h E; exact (E x).
  - intros a cache pr m IH sf v2 b S N M c f g h E.
    cbn [reverseTree deep contentsWith].
    assert (D : forall d, digitContentsWith g (reverseDigit f d) = List.rev (digitContentsWith h d)).
    { intro d; destruct d; cbn [reverseDigit digitContentsWith];
        repeat rewrite E; repeat rewrite List.rev_app_distr; lists. }
    rewrite !D; rewrite (IH v2 (Node v2 b) _ _ _ c (reverseNode f)
      (nodeContentsWith g) (nodeContentsWith h)).
    + repeat rewrite List.rev_app_distr; lists.
    + intro n; destruct n; cbn [reverseNode node2 node3 nodeContentsWith];
        repeat rewrite E; repeat rewrite List.rev_app_distr; lists.
Qed.

Lemma reverse_contents {v a} `{Measured v a} (t : FingerTree v a) :
  contents (Data.FingerTree.reverse t) = List.rev (contents t).
Proof.
  unfold contents, Data.FingerTree.reverse.
  apply reverseTree_contentsWith; intro x; reflexivity.
Qed.

Section PublicConstruction.
Context {v a} `{Measured v a}.

Lemma empty_contents : contents (@empty v a _ _ _) = [].
Proof. reflexivity. Qed.
Lemma singleton_contents x : contents (@singleton v a _ _ _ x) = [x].
Proof. reflexivity. Qed.
Lemma consTree_contents x (t : FingerTree v a) : contents (consTree x t) = x :: contents t.
Proof. unfold contents; rewrite consTree_contentsWith; reflexivity. Qed.
Lemma snocTree_contents (t : FingerTree v a) x : contents (snocTree t x) = contents t ++ [x].
Proof. apply snocTree_contentsWith. Qed.
Lemma append_contents (l r : FingerTree v a) : contents (op_zgzl__ l r) = contents l ++ contents r.
Proof. apply append_contentsWith. Qed.
Lemma fromList_contents (xs : list a) : contents (@fromList v a _ _ _ xs) = xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (contents (consTree x (fromList xs)) = x :: xs).
  rewrite consTree_contents, IH; reflexivity.
Qed.
End PublicConstruction.

Section Validity.
Context {v : Type} `{GHC.Base.Monoid v}.
Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma measure_digit_model {a} (M : Measured v a) d :
  measure d = digitMeasure (@measure v a _ _ M) d.
Proof. destruct d; reflexivity. Qed.

Lemma measure_tree_model {a} (M : Measured v a) (t : FingerTree v a) :
  measure t = treeCacheWith (@measure v a _ _ M) t.
Proof. destruct t; reflexivity. Qed.

Lemma node2_validity {a} (M : Measured v a) (P : a -> Prop) x y :
  P x -> P y -> nodeValidity (@measure v a _ _ M) P (node2 x y).
Proof. intros; cbn [nodeValidity node2]; auto. Qed.
Lemma node3_validity {a} (M : Measured v a) (P : a -> Prop) x y z :
  P x -> P y -> P z -> nodeValidity (@measure v a _ _ M) P (node3 x y z).
Proof. intros; cbn [nodeValidity node3]; auto. Qed.

Lemma deep_validityWith {a} (M : Measured v a) P pr m sf :
  digitValidity P pr -> validityWith nodeCache (nodeValidity (@measure v a _ _ M) P) m ->
  digitValidity P sf -> validityWith (@measure v a _ _ M) P (deep pr m sf).
Proof.
  intros Vp Vm Vs; cbn [deep validityWith].
  repeat split; try assumption.
Qed.

Lemma consTree_cache {a} (M : Measured v a) x (t : FingerTree v a) :
  treeCacheWith (@measure v a _ _ M) (consTree x t) =
    GHC.Base.mappend (measure x) (treeCacheWith (@measure v a _ _ M) t).
Proof.
  destruct t as [|y|c pr m sf]; cbn [consTree deep treeCacheWith];
    [symmetry; apply right_id|rewrite measure_digit_model; cbn [digitMeasure];
     change (GHC.Base.mappend (GHC.Base.mappend (measure x) GHC.Base.mempty) (measure y) =
       GHC.Base.mappend (measure x) (measure y));
     rewrite right_id; reflexivity|].
  destruct pr; reflexivity.
Qed.

Lemma snocTree_cache {a} (M : Measured v a) (t : FingerTree v a) x :
  treeCacheWith (@measure v a _ _ M) (snocTree t x) =
    GHC.Base.mappend (treeCacheWith (@measure v a _ _ M) t) (measure x).
Proof.
  destruct t as [|y|c pr m sf]; cbn [snocTree deep treeCacheWith];
    [symmetry; apply left_id|rewrite measure_digit_model; cbn [digitMeasure];
     change (GHC.Base.mappend (GHC.Base.mappend (measure y) GHC.Base.mempty) (measure x) =
       GHC.Base.mappend (measure y) (measure x));
     rewrite right_id; reflexivity|].
  destruct sf; reflexivity.
Qed.

Lemma consTree_validityWith : forall a (t : FingerTree v a) (M : Measured v a) P x,
  P x -> validityWith (@measure v a _ _ M) P t ->
  validityWith (@measure v a _ _ M) P (consTree x t).
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) P x,
    P x -> validityWith (@measure v a _ _ M) P t ->
    validityWith (@measure v a _ _ M) P (consTree x t)) _ _ _).
  - intros; assumption.
  - intros; apply deep_validityWith; cbn [digitValidity validityWith]; assumption || exact I.
  - intros a c pr m IH sf M P x Vx [Vp [Vm [Vs Ec]]].
    destruct pr; cbn [digitValidity] in Vp;
      cbn [consTree GHC.Prim.seq validityWith digitValidity consDigit digitMeasure];
      repeat split; try tauto;
      try (rewrite Ec; cbn [digitMeasure]; repeat rewrite assoc; reflexivity).
    + apply (IH Measured__Node__5 (nodeValidity (@measure v a _ _ M) P)).
      * apply node3_validity; tauto.
      * exact Vm.
    + change (GHC.Base.mappend (measure x) c =
        GHC.Base.mappend
          (GHC.Base.mappend (GHC.Base.mappend (measure x) (measure a0))
            (treeCacheWith (@measure v (Node v a) _ _ Measured__Node__5)
              (consTree (node3 a1 a2 a3) m))) (digitMeasure measure sf)).
      rewrite consTree_cache, Ec; cbn [digitMeasure].
      change (@measure v (Node v a) _ _ Measured__Node__5 (node3 a1 a2 a3)) with
        (GHC.Base.mappend (GHC.Base.mappend (measure a1) (measure a2)) (measure a3)).
      repeat rewrite assoc; reflexivity.
Qed.
Lemma snocTree_validityWith : forall a (t : FingerTree v a) (M : Measured v a) P x,
  P x -> validityWith (@measure v a _ _ M) P t ->
  validityWith (@measure v a _ _ M) P (snocTree t x).
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) P x,
    P x -> validityWith (@measure v a _ _ M) P t ->
    validityWith (@measure v a _ _ M) P (snocTree t x)) _ _ _).
  - intros; assumption.
  - intros; apply deep_validityWith; cbn [digitValidity validityWith]; assumption || exact I.
  - intros a c pr m IH sf M P x Vx [Vp [Vm [Vs Ec]]].
    destruct sf; cbn [digitValidity] in Vs;
      cbn [snocTree GHC.Prim.seq validityWith digitValidity snocDigit digitMeasure];
      repeat split; try tauto;
      try (rewrite Ec; cbn [digitMeasure]; repeat rewrite assoc; reflexivity).
    + apply (IH Measured__Node__5 (nodeValidity (@measure v a _ _ M) P)).
      * apply node3_validity; tauto.
      * exact Vm.
    + change (GHC.Base.mappend c (measure x) =
        GHC.Base.mappend
          (GHC.Base.mappend (digitMeasure measure pr)
            (treeCacheWith (@measure v (Node v a) _ _ Measured__Node__5)
              (snocTree m (node3 a0 a1 a2)))) (GHC.Base.mappend (measure a3) (measure x))).
      rewrite snocTree_cache, Ec; cbn [digitMeasure].
      change (@measure v (Node v a) _ _ Measured__Node__5 (node3 a0 a1 a2)) with
        (GHC.Base.mappend (GHC.Base.mappend (measure a0) (measure a1)) (measure a2)).
      repeat rewrite assoc; reflexivity.
Qed.

Lemma fromList_validityWith {a} (M : Measured v a) P xs :
  List.Forall P xs -> validityWith (@measure v a _ _ M) P (fromList xs).
Proof.
  intro V; induction V; [exact I|].
  change (validityWith (@measure v a _ _ M) P (consTree x (fromList l))).
  apply consTree_validityWith; assumption.
Qed.

Local Ltac valid_nodes :=
  first [assumption | apply node2_validity; tauto | apply node3_validity; tauto].

Lemma appendTree234_validityWith : forall a (t : FingerTree v a) (M : Measured v a) P,
  validityWith (@measure v a _ _ M) P t ->
  (forall x y r, P x -> P y -> validityWith (@measure v a _ _ M) P r ->
    validityWith (@measure v a _ _ M) P (appendTree2 t x y r)) /\
  (forall x y z r, P x -> P y -> P z -> validityWith (@measure v a _ _ M) P r ->
    validityWith (@measure v a _ _ M) P (appendTree3 t x y z r)) /\
  (forall x y z w r, P x -> P y -> P z -> P w -> validityWith (@measure v a _ _ M) P r ->
    validityWith (@measure v a _ _ M) P (appendTree4 t x y z w r)).
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) P,
    validityWith (@measure v a _ _ M) P t ->
    (forall x y r, P x -> P y -> validityWith (@measure v a _ _ M) P r ->
      validityWith (@measure v a _ _ M) P (appendTree2 t x y r)) /\
    (forall x y z r, P x -> P y -> P z -> validityWith (@measure v a _ _ M) P r ->
      validityWith (@measure v a _ _ M) P (appendTree3 t x y z r)) /\
    (forall x y z w r, P x -> P y -> P z -> P w -> validityWith (@measure v a _ _ M) P r ->
      validityWith (@measure v a _ _ M) P (appendTree4 t x y z w r))) _ _ _).
  - intros a M P V; repeat split; intros;
      cbn [appendTree2 appendTree3 appendTree4];
      repeat apply consTree_validityWith; assumption.
  - intros a u M P Vu; repeat split; intros;
      destruct r; cbn [appendTree2 appendTree3 appendTree4];
      repeat first [apply consTree_validityWith | apply snocTree_validityWith];
      assumption || exact I.
  - intros a c pr m IH sf M P [Vp [Vm [Vs Ec]]].
    destruct (IH Measured__Node__5 (nodeValidity (@measure v a _ _ M) P) Vm)
      as [I2 [I3 I4]].
    repeat split; intros.
    + destruct r as [|u|c2 pr2 m2 sf2].
      * cbn [appendTree2]; repeat apply snocTree_validityWith; assumption ||
          (cbn [validityWith]; tauto).
      * cbn [appendTree2]; repeat apply snocTree_validityWith; assumption ||
          (cbn [validityWith]; tauto).
      * match goal with V : validityWith _ _ (Deep _ _ _ _) |- _ =>
          destruct V as [Vp2 [Vm2 [Vs2 Ec2]]] end.
        rewrite appendTree2_deep; apply deep_validityWith; try assumption.
        destruct sf; destruct pr2; cbn [addDigits2]; cbn [digitValidity] in *;
          first [apply I2|apply I3|apply I4]; valid_nodes.
    + destruct r as [|u|c2 pr2 m2 sf2].
      * cbn [appendTree3]; repeat apply snocTree_validityWith; assumption ||
          (cbn [validityWith]; tauto).
      * cbn [appendTree3]; repeat apply snocTree_validityWith; assumption ||
          (cbn [validityWith]; tauto).
      * match goal with V : validityWith _ _ (Deep _ _ _ _) |- _ =>
          destruct V as [Vp2 [Vm2 [Vs2 Ec2]]] end.
        rewrite appendTree3_deep; apply deep_validityWith; try assumption.
        destruct sf; destruct pr2; cbn [addDigits3]; cbn [digitValidity] in *;
          first [apply I2|apply I3|apply I4]; valid_nodes.
    + destruct r as [|u|c2 pr2 m2 sf2].
      * cbn [appendTree4]; repeat apply snocTree_validityWith; assumption ||
          (cbn [validityWith]; tauto).
      * cbn [appendTree4]; repeat apply snocTree_validityWith; assumption ||
          (cbn [validityWith]; tauto).
      * match goal with V : validityWith _ _ (Deep _ _ _ _) |- _ =>
          destruct V as [Vp2 [Vm2 [Vs2 Ec2]]] end.
        rewrite appendTree4_deep; apply deep_validityWith; try assumption.
        destruct sf; destruct pr2; cbn [addDigits4]; cbn [digitValidity] in *;
          first [apply I2|apply I3|apply I4]; valid_nodes.
Qed.

Lemma appendTree1_validityWith : forall a (t : FingerTree v a) (M : Measured v a) P,
  validityWith (@measure v a _ _ M) P t ->
  forall x r, P x -> validityWith (@measure v a _ _ M) P r ->
    validityWith (@measure v a _ _ M) P (appendTree1 t x r).
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) P,
    validityWith (@measure v a _ _ M) P t ->
    forall x r, P x -> validityWith (@measure v a _ _ M) P r ->
      validityWith (@measure v a _ _ M) P (appendTree1 t x r)) _ _ _).
  - intros; cbn [appendTree1]; apply consTree_validityWith; assumption.
  - intros a u M P Vu x r Vx Vr; destruct r;
      cbn [appendTree1];
      repeat first [apply consTree_validityWith | apply snocTree_validityWith];
      assumption || exact I.
  - intros a c pr m IH sf M P [Vp [Vm [Vs Ec]]] x r Vx Vr.
    pose proof (IH Measured__Node__5 (nodeValidity (@measure v a _ _ M) P) Vm) as I1.
    destruct (appendTree234_validityWith _ m Measured__Node__5
      (nodeValidity (@measure v a _ _ M) P) Vm) as [I2 [I3 I4]].
    destruct r as [|u|c2 pr2 m2 sf2].
    + cbn [appendTree1]; repeat apply snocTree_validityWith; assumption ||
        (cbn [validityWith]; tauto).
    + cbn [appendTree1]; repeat apply snocTree_validityWith; assumption ||
        (cbn [validityWith]; tauto).
    + destruct Vr as [Vp2 [Vm2 [Vs2 Ec2]]].
      rewrite appendTree1_deep; apply deep_validityWith; try assumption.
      destruct sf; destruct pr2; cbn [addDigits1]; cbn [digitValidity] in *;
        first [apply I1|apply I2|apply I3]; valid_nodes.
Qed.

Lemma append_validityWith {a} (M : Measured v a) P l r :
  validityWith (@measure v a _ _ M) P l -> validityWith (@measure v a _ _ M) P r ->
  validityWith (@measure v a _ _ M) P (op_zgzl__ l r).
Proof.
  intros Vl Vr; destruct l as [|x|c1 pr1 m1 sf1]; destruct r as [|y|c2 pr2 m2 sf2];
    cbn [op_zgzl__ appendTree0]; try assumption;
    try (apply consTree_validityWith; assumption);
    try (apply snocTree_validityWith; assumption).
  destruct Vl as [Vp1 [Vm1 [Vs1 Ec1]]], Vr as [Vp2 [Vm2 [Vs2 Ec2]]].
  pose proof (appendTree1_validityWith _ m1 Measured__Node__5
    (nodeValidity (@measure v a _ _ M) P) Vm1) as I1.
  destruct (appendTree234_validityWith _ m1 Measured__Node__5
    (nodeValidity (@measure v a _ _ M) P) Vm1) as [I2 [I3 I4]].
  apply deep_validityWith; try assumption.
  destruct sf1; destruct pr2; cbn [addDigits0]; cbn [digitValidity] in *;
    first [apply I1|apply I2|apply I3]; valid_nodes.
Qed.

Lemma digitToTree_validityWith {a} (M : Measured v a) P d :
  digitValidity P d -> validityWith (@measure v a _ _ M) P (digitToTree d).
Proof.
  intro V; destruct d; cbn [digitToTree]; [exact V|..];
    apply deep_validityWith; cbn [digitValidity validityWith] in *; tauto.
Qed.

Lemma digitToTree_cache {a} (M : Measured v a) d :
  treeCacheWith (@measure v a _ _ M) (digitToTree d) = digitMeasure measure d.
Proof.
  destruct d; cbn [digitToTree deep treeCacheWith digitMeasure];
    rewrite ?measure_digit_model; cbn [digitMeasure];
    change (@measure v (FingerTree v (Node v a)) _ _ _ Empty) with (@GHC.Base.mempty v _ _);
    rewrite ?right_id; repeat rewrite assoc; reflexivity.
Qed.

Lemma nodeToDigit_validity {a} (M : Measured v a) P n :
  nodeValidity (@measure v a _ _ M) P n ->
  digitValidity P (nodeToDigit n) /\ nodeCache n = digitMeasure measure (nodeToDigit n).
Proof.
  destruct n; cbn [nodeValidity nodeToDigit nodeCache digitValidity digitMeasure]; tauto.
Qed.

Lemma viewl_validityWith : forall a (t : FingerTree v a) (M : Measured v a) P,
  validityWith (@measure v a _ _ M) P t ->
  match @viewl v a _ _ M t with
  | EmptyL => treeCacheWith (@measure v a _ _ M) t = GHC.Base.mempty
  | op_ZCzl__ x r => P x /\ validityWith (@measure v a _ _ M) P r /\
      treeCacheWith (@measure v a _ _ M) t =
        GHC.Base.mappend (measure x) (treeCacheWith (@measure v a _ _ M) r)
  end.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) P,
    validityWith (@measure v a _ _ M) P t ->
    match @viewl v a _ _ M t with
    | EmptyL => treeCacheWith (@measure v a _ _ M) t = GHC.Base.mempty
    | op_ZCzl__ x r => P x /\ validityWith (@measure v a _ _ M) P r /\
        treeCacheWith (@measure v a _ _ M) t =
          GHC.Base.mappend (measure x) (treeCacheWith (@measure v a _ _ M) r)
    end) _ _ _).
  - intros; reflexivity.
  - intros a x M P V; cbn [viewl treeCacheWith validityWith];
      repeat split; auto; symmetry; apply right_id.
  - intros a c pr m IH sf M P [Vp [Vm [Vs Ec]]].
    specialize (IH Measured__Node__5 (nodeValidity (@measure v a _ _ M) P) Vm).
    destruct pr as [x|x y|x y z|x y z w]; cbn [digitValidity] in Vp;
      cbn [viewl lheadDigit ltailDigit] in *.
    + destruct (viewl m) as [|n r] eqn:E.
      * split; [exact Vp|]; split; [apply digitToTree_validityWith; exact Vs|].
        cbn [treeCacheWith]; rewrite digitToTree_cache, Ec; cbn [digitMeasure].
        change (treeCacheWith nodeCache m = GHC.Base.mempty) in IH.
        rewrite IH, right_id; reflexivity.
      * destruct IH as [Vn [Vr Em]].
        change (treeCacheWith nodeCache m =
          GHC.Base.mappend (nodeCache n) (treeCacheWith nodeCache r)) in Em.
        destruct (nodeToDigit_validity M P n Vn) as [Vd En].
        split; [exact Vp|]; split.
        -- cbn [validityWith]; repeat split; try assumption.
           rewrite measure_tree_model, measure_digit_model.
           change (GHC.Base.mappend (treeCacheWith nodeCache m) (digitMeasure measure sf) =
             GHC.Base.mappend
               (GHC.Base.mappend (digitMeasure measure (nodeToDigit n)) (treeCacheWith nodeCache r))
               (digitMeasure measure sf)).
           rewrite Em, En; reflexivity.
        -- cbn [treeCacheWith]; rewrite Ec, measure_tree_model, measure_digit_model.
           cbn [digitMeasure]; apply assoc.
    + split; [tauto|]; split; [apply deep_validityWith; cbn [digitValidity]; tauto|].
      cbn [deep treeCacheWith]; rewrite Ec, !measure_digit_model.
      cbn [digitMeasure]; repeat rewrite assoc; reflexivity.
    + split; [tauto|]; split; [apply deep_validityWith; cbn [digitValidity]; tauto|].
      cbn [deep treeCacheWith]; rewrite Ec, !measure_digit_model.
      cbn [digitMeasure]; repeat rewrite assoc; reflexivity.
    + split; [tauto|]; split; [apply deep_validityWith; cbn [digitValidity]; tauto|].
      cbn [deep treeCacheWith]; rewrite Ec, !measure_digit_model.
      cbn [digitMeasure]; repeat rewrite assoc; reflexivity.
Qed.

Lemma viewr_validityWith : forall a (t : FingerTree v a) (M : Measured v a) P,
  validityWith (@measure v a _ _ M) P t ->
  match @viewr v a _ _ M t with
  | EmptyR => treeCacheWith (@measure v a _ _ M) t = GHC.Base.mempty
  | op_ZCzg__ l x => P x /\ validityWith (@measure v a _ _ M) P l /\
      treeCacheWith (@measure v a _ _ M) t =
        GHC.Base.mappend (treeCacheWith (@measure v a _ _ M) l) (measure x)
  end.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) P,
    validityWith (@measure v a _ _ M) P t ->
    match @viewr v a _ _ M t with
    | EmptyR => treeCacheWith (@measure v a _ _ M) t = GHC.Base.mempty
    | op_ZCzg__ l x => P x /\ validityWith (@measure v a _ _ M) P l /\
        treeCacheWith (@measure v a _ _ M) t =
          GHC.Base.mappend (treeCacheWith (@measure v a _ _ M) l) (measure x)
    end) _ _ _).
  - intros; reflexivity.
  - intros a x M P V; cbn [viewr treeCacheWith validityWith];
      repeat split; auto; symmetry; apply left_id.
  - intros a c pr m IH sf M P [Vp [Vm [Vs Ec]]].
    specialize (IH Measured__Node__5 (nodeValidity (@measure v a _ _ M) P) Vm).
    destruct sf as [x|x y|x y z|x y z w]; cbn [digitValidity] in Vs;
      cbn [viewr rheadDigit rtailDigit] in *.
    + destruct (viewr m) as [|r n] eqn:E.
      * split; [exact Vs|]; split; [apply digitToTree_validityWith; exact Vp|].
        cbn [treeCacheWith]; rewrite digitToTree_cache, Ec; cbn [digitMeasure].
        change (treeCacheWith nodeCache m = GHC.Base.mempty) in IH.
        rewrite IH, right_id; reflexivity.
      * destruct IH as [Vn [Vr Em]].
        change (treeCacheWith nodeCache m =
          GHC.Base.mappend (treeCacheWith nodeCache r) (nodeCache n)) in Em.
        destruct (nodeToDigit_validity M P n Vn) as [Vd En].
        split; [exact Vs|]; split.
        -- cbn [validityWith]; repeat split; try assumption.
           rewrite measure_tree_model, measure_digit_model.
           change (GHC.Base.mappend (digitMeasure measure pr) (treeCacheWith nodeCache m) =
             GHC.Base.mappend
               (GHC.Base.mappend (digitMeasure measure pr) (treeCacheWith nodeCache r))
               (digitMeasure measure (nodeToDigit n))).
           rewrite Em, En; symmetry; apply assoc.
        -- cbn [treeCacheWith]; rewrite Ec, measure_tree_model, measure_digit_model.
           reflexivity.
    + split; [tauto|]; split; [apply deep_validityWith; cbn [digitValidity]; tauto|].
      cbn [deep treeCacheWith]; rewrite Ec, !measure_digit_model.
      cbn [digitMeasure]; repeat rewrite assoc; reflexivity.
    + split; [tauto|]; split; [apply deep_validityWith; cbn [digitValidity]; tauto|].
      cbn [deep treeCacheWith]; rewrite Ec, !measure_digit_model.
      cbn [digitMeasure]; repeat rewrite assoc; reflexivity.
    + split; [tauto|]; split; [apply deep_validityWith; cbn [digitValidity]; tauto|].
      cbn [deep treeCacheWith]; rewrite Ec, !measure_digit_model.
      cbn [digitMeasure]; repeat rewrite assoc; reflexivity.
Qed.

Lemma rotL_validityWith {a} (M : Measured v a) P m sf :
  validityWith nodeCache (nodeValidity (@measure v a _ _ M) P) m -> digitValidity P sf ->
  validityWith (@measure v a _ _ M) P (rotL m sf).
Proof.
  intros Vm Vs; pose proof (viewl_validityWith _ m Measured__Node__5
    (nodeValidity (@measure v a _ _ M) P) Vm) as V.
  unfold rotL; destruct (viewl m) as [|n r].
  - apply digitToTree_validityWith; exact Vs.
  - destruct V as [Vn [Vr Em]].
    change (treeCacheWith nodeCache m =
      GHC.Base.mappend (nodeCache n) (treeCacheWith nodeCache r)) in Em.
    destruct (nodeToDigit_validity M P n Vn) as [Vd En].
    cbn [validityWith]; repeat split; try assumption.
    rewrite measure_tree_model, measure_digit_model.
    change (GHC.Base.mappend (treeCacheWith nodeCache m) (digitMeasure measure sf) =
      GHC.Base.mappend (GHC.Base.mappend (digitMeasure measure (nodeToDigit n))
        (treeCacheWith nodeCache r)) (digitMeasure measure sf)).
    rewrite Em, En; reflexivity.
Qed.

Lemma rotR_validityWith {a} (M : Measured v a) P pr m :
  digitValidity P pr -> validityWith nodeCache (nodeValidity (@measure v a _ _ M) P) m ->
  validityWith (@measure v a _ _ M) P (rotR pr m).
Proof.
  intros Vp Vm; pose proof (viewr_validityWith _ m Measured__Node__5
    (nodeValidity (@measure v a _ _ M) P) Vm) as V.
  unfold rotR; destruct (viewr m) as [|r n].
  - apply digitToTree_validityWith; exact Vp.
  - destruct V as [Vn [Vr Em]].
    change (treeCacheWith nodeCache m =
      GHC.Base.mappend (treeCacheWith nodeCache r) (nodeCache n)) in Em.
    destruct (nodeToDigit_validity M P n Vn) as [Vd En].
    cbn [validityWith]; repeat split; try assumption.
    rewrite measure_tree_model, measure_digit_model.
    change (GHC.Base.mappend (digitMeasure measure pr) (treeCacheWith nodeCache m) =
      GHC.Base.mappend (GHC.Base.mappend (digitMeasure measure pr)
        (treeCacheWith nodeCache r)) (digitMeasure measure (nodeToDigit n))).
    rewrite Em, En; symmetry; apply assoc.
Qed.

Lemma deepL_validityWith {a} (M : Measured v a) P pr m sf :
  (match pr with None => True | Some d => digitValidity P d end) ->
  validityWith nodeCache (nodeValidity (@measure v a _ _ M) P) m -> digitValidity P sf ->
  validityWith (@measure v a _ _ M) P (deepL pr m sf).
Proof.
  destruct pr; cbn [deepL]; intros;
    [apply deep_validityWith|apply rotL_validityWith]; assumption.
Qed.

Lemma deepR_validityWith {a} (M : Measured v a) P pr m sf :
  digitValidity P pr -> validityWith nodeCache (nodeValidity (@measure v a _ _ M) P) m ->
  (match sf with None => True | Some d => digitValidity P d end) ->
  validityWith (@measure v a _ _ M) P (deepR pr m sf).
Proof.
  destruct sf; cbn [deepR]; intros;
    [apply deep_validityWith|apply rotR_validityWith]; assumption.
Qed.

Lemma splitDigit_validity {a} (M : Measured v a) P p i d :
  digitValidity P d ->
  let '(MkSplit l x r) := splitDigit p i d in
  (match l with None => True | Some dl => digitValidity P dl end) /\ P x /\
  (match r with None => True | Some dr => digitValidity P dr end).
Proof.
  intro V; destruct d; cbn [splitDigit GHC.Prim.seq];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [digitValidity] in *; tauto.
Qed.

Lemma splitNode_validity {a} (M : Measured v a) P p i n :
  nodeValidity (@measure v a _ _ M) P n ->
  let '(MkSplit l x r) := splitNode p i n in
  (match l with None => True | Some dl => digitValidity P dl end) /\ P x /\
  (match r with None => True | Some dr => digitValidity P dr end).
Proof.
  intro V; destruct n; cbn [splitNode];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [digitValidity nodeValidity] in *; tauto.
Qed.

Lemma splitTree_validityWith : forall a (t : FingerTree v a) (M : Measured v a)
  (D : HsToRocq.Err.Default a) P p i, t <> Empty ->
  validityWith (@measure v a _ _ M) P t ->
  let '(MkSplit l x r) := @splitTree v a _ _ M D p i t in
  validityWith (@measure v a _ _ M) P l /\ P x /\ validityWith (@measure v a _ _ M) P r.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    (D : HsToRocq.Err.Default a) P p i, t <> Empty ->
    validityWith (@measure v a _ _ M) P t ->
    let '(MkSplit l x r) := @splitTree v a _ _ M D p i t in
    validityWith (@measure v a _ _ M) P l /\ P x /\ validityWith (@measure v a _ _ M) P r) _ _ _).
  - intros; contradiction.
  - intros; cbn [splitTree validityWith] in *; tauto.
  - intros a c pr m IH sf M D P p i NE [Vp [Vm [Vs Ec]]].
    cbn [splitTree].
    destruct (p (GHC.Base.mappend i (measure pr))) eqn:Epr.
    + pose proof (splitDigit_validity M P p i pr Vp) as Ed.
      destruct (splitDigit p i pr) as [l x r].
      destruct Ed as [Vl [Vx Vr]].
      split; [destruct l; cbn [Data.Maybe.maybe];
        [apply digitToTree_validityWith; exact Vl|exact I]|].
      split; [exact Vx|apply deepL_validityWith; assumption].
    + destruct (p (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m))) eqn:Em.
      * assert (Nm : m <> Empty).
        { eapply split_middle_nonempty; eassumption. }
        specialize (IH Measured__Node__5 DefaultNode (nodeValidity (@measure v a _ _ M) P) p
          (GHC.Base.mappend i (measure pr)) Nm Vm).
        destruct (splitTree p (GHC.Base.mappend i (measure pr)) m) as [ml n mr].
        destruct IH as [Vl [Vn Vr]].
        pose proof (splitNode_validity M P p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure ml)) n Vn) as En.
        destruct (splitNode p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure ml)) n)
          as [l x r].
        destruct En as [Vdl [Vx Vdr]].
        split; [apply deepR_validityWith; assumption|].
        split; [exact Vx|apply deepL_validityWith; assumption].
      * pose proof (splitDigit_validity M P p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m)) sf Vs) as Ed.
        destruct (splitDigit p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m)) sf)
          as [l x r].
        destruct Ed as [Vl [Vx Vr]].
        split; [apply deepR_validityWith; assumption|].
        split; [exact Vx|destruct r; cbn [Data.Maybe.maybe];
          [apply digitToTree_validityWith; exact Vr|exact I]].
Qed.

Lemma split_validityWith {a} (M : Measured v a) P p t :
  validityWith (@measure v a _ _ M) P t ->
  let '(l, r) := split p t in
  validityWith (@measure v a _ _ M) P l /\ validityWith (@measure v a _ _ M) P r.
Proof.
  intro V; unfold split; destruct t as [|u|c pr m sf];
    cbn -[splitTree consTree validityWith]; try (split; exact I);
    match goal with
    | |- context [@splitTree v a _ _ M ?D ?p ?i ?t] =>
        pose proof (splitTree_validityWith a t M D P p i ltac:(discriminate) V) as E;
        destruct (@splitTree v a _ _ M D p i t) as [l x r]
    end;
    destruct (Bool.Sumbool.sumbool_of_bool _);
    destruct E as [Vl [Vx Vr]]; split; try assumption; try exact I;
    apply consTree_validityWith; assumption.
Qed.

Lemma mapTree_validityWith {v1} : forall a (t : FingerTree v1 a) b (M : Measured v b)
  (Q : b -> Prop) (f : a -> b),
  (forall x, Q (f x)) -> validityWith (@measure v b _ _ M) Q (mapTree f t).
Proof.
  refine (FingerTree_rect v1 (fun a t => forall b (M : Measured v b)
    (Q : b -> Prop) (f : a -> b),
    (forall x, Q (f x)) -> validityWith (@measure v b _ _ M) Q (mapTree f t)) _ _ _).
  - intros; exact I.
  - intros; apply H1.
  - intros a c pr m IH sf b M Q f E; cbn [mapTree].
    apply deep_validityWith.
    + destruct pr; cbn [mapDigit digitValidity]; auto.
    + apply (IH (Node v b) Measured__Node__5 (nodeValidity (@measure v b _ _ M) Q)).
      intro n; destruct n; cbn [mapNode]; [apply node2_validity|apply node3_validity]; auto.
    + destruct sf; cbn [mapDigit digitValidity]; auto.
Qed.

Lemma fmap'_validity {v1 a b} `{Measured v1 a} (M : Measured v b)
  (f : a -> b) (t : FingerTree v1 a) : validity M (fmap' f t).
Proof. apply mapTree_validityWith; auto. Qed.

Lemma reverseTree_validityWith {v1} : forall a (t : FingerTree v1 a) b (M : Measured v b)
  (Q : b -> Prop) (f : a -> b),
  (forall x, Q (f x)) -> validityWith (@measure v b _ _ M) Q (reverseTree f t).
Proof.
  refine (FingerTree_rect v1 (fun a t => forall b (M : Measured v b)
    (Q : b -> Prop) (f : a -> b),
    (forall x, Q (f x)) -> validityWith (@measure v b _ _ M) Q (reverseTree f t)) _ _ _).
  - intros; exact I.
  - intros; apply H1.
  - intros a c pr m IH sf b M Q f E; cbn [reverseTree].
    apply deep_validityWith.
    + destruct sf; cbn [reverseDigit digitValidity]; auto.
    + apply (IH (Node v b) Measured__Node__5 (nodeValidity (@measure v b _ _ M) Q)).
      intro n; destruct n; cbn [reverseNode]; [apply node2_validity|apply node3_validity]; auto.
    + destruct pr; cbn [reverseDigit digitValidity]; auto.
Qed.

Lemma reverse_validity {a} (M : Measured v a) (t : FingerTree v a) :
  validity M (Data.FingerTree.reverse t).
Proof. apply reverseTree_validityWith; auto. Qed.

Lemma unsafeFmapNode_validity {a b} (M : Measured v a) (N : Measured v b)
  P Q (f : a -> b) n :
  (forall x, P x -> Q (f x) /\ @measure v b _ _ N (f x) = @measure v a _ _ M x) ->
  nodeValidity (@measure v a _ _ M) P n ->
  nodeValidity (@measure v b _ _ N) Q (unsafeFmapNode f n) /\
    nodeCache (unsafeFmapNode f n) = nodeCache n.
Proof.
  intros E V; destruct n; cbn [nodeValidity unsafeFmapNode nodeCache] in *;
    decompose [and] V;
    repeat match goal with Hx : P ?x |- _ =>
      let Qx := fresh "Qx" in let Ex := fresh "Ex" in
      destruct (E x Hx) as [Qx Ex]; clear Hx
    end;
    repeat split; try assumption; congruence.
Qed.

Lemma unsafeFmap_validityWith : forall a (t : FingerTree v a) b
  (M : Measured v a) (N : Measured v b) P Q (f : a -> b),
  (forall x, P x -> Q (f x) /\ @measure v b _ _ N (f x) = @measure v a _ _ M x) ->
  validityWith (@measure v a _ _ M) P t ->
  validityWith (@measure v b _ _ N) Q (unsafeFmap f t).
Proof.
  refine (FingerTree_rect v (fun a t => forall b
    (M : Measured v a) (N : Measured v b) P Q (f : a -> b),
    (forall x, P x -> Q (f x) /\ @measure v b _ _ N (f x) = @measure v a _ _ M x) ->
    validityWith (@measure v a _ _ M) P t ->
    validityWith (@measure v b _ _ N) Q (unsafeFmap f t)) _ _ _).
  - intros; exact I.
  - intros a x b M N P Q f E V; exact (proj1 (E x V)).
  - intros a c pr m IH sf b M N P Q f E [Vp [Vm [Vs Ec]]].
    assert (D : forall d, digitValidity P d ->
      digitValidity Q (mapDigit f d) /\
      digitMeasure (@measure v b _ _ N) (mapDigit f d) = digitMeasure (@measure v a _ _ M) d).
    { intros d V; destruct d; cbn [digitValidity mapDigit digitMeasure] in *;
        decompose [and] V;
        repeat match goal with Hx : P ?x |- _ =>
          let Qx := fresh "Qx" in let Ex := fresh "Ex" in
          destruct (E x Hx) as [Qx Ex]; clear Hx
        end;
        repeat split; try assumption; congruence. }
    destruct (D pr Vp) as [Vp' Ep], (D sf Vs) as [Vs' Es].
    cbn [unsafeFmap validityWith]; repeat split; try assumption.
    + apply (IH (Node v b) Measured__Node__5 Measured__Node__5
        (nodeValidity (@measure v a _ _ M) P) (nodeValidity (@measure v b _ _ N) Q)).
      * intros n Vn; exact (unsafeFmapNode_validity M N P Q f n E Vn).
      * exact Vm.
    + rewrite Ep, Es, Ec; f_equal; f_equal.
      destruct m as [|n|cm pm mm sm]; [reflexivity|destruct n; reflexivity|reflexivity].
Qed.

Lemma unsafeFmap_validity {a b} (M : Measured v a) (N : Measured v b)
  (f : a -> b) (t : FingerTree v a) :
  (forall x, @measure v b _ _ N (f x) = @measure v a _ _ M x) ->
  validity M t -> validity N (unsafeFmap f t).
Proof. intros E V; eapply unsafeFmap_validityWith; [intros; split; [exact I|apply E]|exact V]. Qed.
End Validity.

Lemma contents_empty_iff {v a} (t : FingerTree v a) : contents t = [] <-> t = Empty.
Proof.
  destruct t as [|x|c pr m sf]; [tauto|cbn [contents contentsWith]; split; discriminate|].
  destruct pr; cbn [contents contentsWith digitContentsWith List.app]; split; discriminate.
Qed.

Lemma null_contents {v a} (t : FingerTree v a) : null t = true <-> contents t = [].
Proof. rewrite contents_empty_iff; destruct t; cbn; split; congruence. Qed.

Lemma eq_contents {v a} `{GHC.Base.Eq_ a} (l r : FingerTree v a) :
  (GHC.Base.op_zeze__ l r) = GHC.Base.op_zeze__ (contents l) (contents r).
Proof.
  change (GHC.Base.op_zeze__ (Data.Foldable.toList l) (Data.Foldable.toList r) =
    GHC.Base.op_zeze__ (contents l) (contents r)).
  rewrite !toList_contents; reflexivity.
Qed.

Lemma compare_contents {v a} `{GHC.Base.Ord a} (l r : FingerTree v a) :
  GHC.Base.compare l r = GHC.Base.compare (contents l) (contents r).
Proof.
  change (GHC.Base.compare (Data.Foldable.toList l) (Data.Foldable.toList r) =
    GHC.Base.compare (contents l) (contents r)).
  rewrite !toList_contents; reflexivity.
Qed.

Section PublicContracts.
Context {v a} `{GHC.Base.Monoid v} (M : Measured v a).
Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma empty_validity : validity M (@empty v a _ _ M).
Proof. exact I. Qed.
Lemma singleton_validity x : validity M (singleton x).
Proof. exact I. Qed.
Lemma consTree_validity x t : validity M t -> validity M (consTree x t).
Proof. intro V; eapply consTree_validityWith; [exact assoc|exact right_id|exact I|exact V]. Qed.
Lemma snocTree_validity t x : validity M t -> validity M (snocTree t x).
Proof. intro V; eapply snocTree_validityWith; [exact assoc|exact left_id|exact right_id|exact I|exact V]. Qed.
Lemma append_validity l r : validity M l -> validity M r -> validity M (op_zgzl__ l r).
Proof. apply append_validityWith; assumption. Qed.
Lemma fromList_validity xs : validity M (fromList xs).
Proof.
  apply fromList_validityWith; try assumption.
  induction xs; constructor; auto.
Qed.

Lemma viewl_contract t x r : validity M t -> viewl t = op_ZCzl__ x r ->
  validity M r /\ contents t = x :: contents r.
Proof.
  intros V E; pose proof (viewl_validityWith assoc right_id a t M (fun _ => True) V) as Vr.
  pose proof (viewl_contentsWith a t M a (fun x => [x])) as Ec.
  rewrite E in Vr, Ec; split; [exact (proj1 (proj2 Vr))|exact Ec].
Qed.

Lemma viewr_contract t l x : validity M t -> viewr t = op_ZCzg__ l x ->
  validity M l /\ contents t = contents l ++ [x].
Proof.
  intros V E; pose proof (viewr_validityWith assoc left_id right_id a t M (fun _ => True) V) as Vl.
  pose proof (viewr_contentsWith a t M a (fun x => [x])) as Ec.
  rewrite E in Vl, Ec; split; [exact (proj1 (proj2 Vl))|exact Ec].
Qed.

Lemma split_contract p t l r : validity M t -> split p t = (l, r) ->
  validity M l /\ validity M r /\ contents t = contents l ++ contents r.
Proof.
  intros V E; pose proof (split_validityWith assoc left_id right_id M (fun _ => True) p t V) as Vlr.
  pose proof (split_contentsWith right_id M (fun x => [x]) p t) as Ec.
  rewrite E in Vlr, Ec; tauto.
Qed.

Lemma takeUntil_validity p t : validity M t -> validity M (takeUntil p t).
Proof.
  intro V; unfold takeUntil, GHC.Base.op_z2218U__, Data.Tuple.fst.
  destruct (split p t) as [l r] eqn:E.
  exact (proj1 (split_contract p t l r V E)).
Qed.

Lemma dropUntil_validity p t : validity M t -> validity M (dropUntil p t).
Proof.
  intro V; unfold dropUntil, GHC.Base.op_z2218U__, Data.Tuple.snd.
  destruct (split p t) as [l r] eqn:E.
  exact (proj1 (proj2 (split_contract p t l r V E))).
Qed.

Lemma take_drop_contents p t : contents t = contents (takeUntil p t) ++ contents (dropUntil p t).
Proof.
  unfold takeUntil, dropUntil, GHC.Base.op_z2218U__, Data.Tuple.fst, Data.Tuple.snd.
  pose proof (split_contentsWith right_id M (fun x => [x]) p t) as E.
  destruct (split p t); exact E.
Qed.
End PublicContracts.

(* Every exported constant has both a full type check and a dependency audit. *)
Check @digitToTree_contentsWith. Print Assumptions digitToTree_contentsWith.
Check @nodeToDigit_contentsWith. Print Assumptions nodeToDigit_contentsWith.
Check @consTree_contentsWith. Print Assumptions consTree_contentsWith.
Check @mapTree_contentsWith. Print Assumptions mapTree_contentsWith.
Check @snocTree_contentsWith. Print Assumptions snocTree_contentsWith.
Check @appendTree234_contentsWith. Print Assumptions appendTree234_contentsWith.
Check @appendTree1_contentsWith. Print Assumptions appendTree1_contentsWith.
Check @append_contentsWith. Print Assumptions append_contentsWith.
Check @viewl_contentsWith. Print Assumptions viewl_contentsWith.
Check @viewr_contentsWith. Print Assumptions viewr_contentsWith.
Check @rotL_contentsWith. Print Assumptions rotL_contentsWith.
Check @rotR_contentsWith. Print Assumptions rotR_contentsWith.
Check @deepL_contentsWith. Print Assumptions deepL_contentsWith.
Check @deepR_contentsWith. Print Assumptions deepR_contentsWith.
Check @splitDigit_contentsWith. Print Assumptions splitDigit_contentsWith.
Check @splitNode_contentsWith. Print Assumptions splitNode_contentsWith.
Check @splitTree_contentsWith. Print Assumptions splitTree_contentsWith.
Check @split_contentsWith. Print Assumptions split_contentsWith.
Check @digitContentsWith_map. Print Assumptions digitContentsWith_map.
Check @contentsWith_ext. Print Assumptions contentsWith_ext.
Check @contentsWith_flat_map. Print Assumptions contentsWith_flat_map.
Check @contentsWith_singletons. Print Assumptions contentsWith_singletons.
Check @fmap'_contents. Print Assumptions fmap'_contents.
Check @unsafeFmap_contentsWith. Print Assumptions unsafeFmap_contentsWith.
Check @unsafeFmap_contents. Print Assumptions unsafeFmap_contents.
Check @reverseTree_contentsWith. Print Assumptions reverseTree_contentsWith.
Check @reverse_contents. Print Assumptions reverse_contents.
Check @empty_contents. Print Assumptions empty_contents.
Check @singleton_contents. Print Assumptions singleton_contents.
Check @consTree_contents. Print Assumptions consTree_contents.
Check @snocTree_contents. Print Assumptions snocTree_contents.
Check @append_contents. Print Assumptions append_contents.
Check @fromList_contents. Print Assumptions fromList_contents.
Check @measure_digit_model. Print Assumptions measure_digit_model.
Check @measure_tree_model. Print Assumptions measure_tree_model.
Check @node2_validity. Print Assumptions node2_validity.
Check @node3_validity. Print Assumptions node3_validity.
Check @deep_validityWith. Print Assumptions deep_validityWith.
Check @consTree_cache. Print Assumptions consTree_cache.
Check @snocTree_cache. Print Assumptions snocTree_cache.
Check @consTree_validityWith. Print Assumptions consTree_validityWith.
Check @snocTree_validityWith. Print Assumptions snocTree_validityWith.
Check @fromList_validityWith. Print Assumptions fromList_validityWith.
Check @appendTree234_validityWith. Print Assumptions appendTree234_validityWith.
Check @appendTree1_validityWith. Print Assumptions appendTree1_validityWith.
Check @append_validityWith. Print Assumptions append_validityWith.
Check @digitToTree_validityWith. Print Assumptions digitToTree_validityWith.
Check @digitToTree_cache. Print Assumptions digitToTree_cache.
Check @nodeToDigit_validity. Print Assumptions nodeToDigit_validity.
Check @viewl_validityWith. Print Assumptions viewl_validityWith.
Check @viewr_validityWith. Print Assumptions viewr_validityWith.
Check @rotL_validityWith. Print Assumptions rotL_validityWith.
Check @rotR_validityWith. Print Assumptions rotR_validityWith.
Check @deepL_validityWith. Print Assumptions deepL_validityWith.
Check @deepR_validityWith. Print Assumptions deepR_validityWith.
Check @splitDigit_validity. Print Assumptions splitDigit_validity.
Check @splitNode_validity. Print Assumptions splitNode_validity.
Check @splitTree_validityWith. Print Assumptions splitTree_validityWith.
Check @split_validityWith. Print Assumptions split_validityWith.
Check @mapTree_validityWith. Print Assumptions mapTree_validityWith.
Check @fmap'_validity. Print Assumptions fmap'_validity.
Check @reverseTree_validityWith. Print Assumptions reverseTree_validityWith.
Check @reverse_validity. Print Assumptions reverse_validity.
Check @unsafeFmapNode_validity. Print Assumptions unsafeFmapNode_validity.
Check @unsafeFmap_validityWith. Print Assumptions unsafeFmap_validityWith.
Check @unsafeFmap_validity. Print Assumptions unsafeFmap_validity.
Check @contents_empty_iff. Print Assumptions contents_empty_iff.
Check @null_contents. Print Assumptions null_contents.
Check @eq_contents. Print Assumptions eq_contents.
Check @compare_contents. Print Assumptions compare_contents.
Check @empty_validity. Print Assumptions empty_validity.
Check @singleton_validity. Print Assumptions singleton_validity.
Check @consTree_validity. Print Assumptions consTree_validity.
Check @snocTree_validity. Print Assumptions snocTree_validity.
Check @append_validity. Print Assumptions append_validity.
Check @fromList_validity. Print Assumptions fromList_validity.
Check @viewl_contract. Print Assumptions viewl_contract.
Check @viewr_contract. Print Assumptions viewr_contract.
Check @split_contract. Print Assumptions split_contract.
Check @takeUntil_validity. Print Assumptions takeUntil_validity.
Check @dropUntil_validity. Print Assumptions dropUntil_validity.
Check @take_drop_contents. Print Assumptions take_drop_contents.
