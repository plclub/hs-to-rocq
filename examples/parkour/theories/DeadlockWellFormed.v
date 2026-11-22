From Stdlib Require Import Lists.List.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Codec Parkour.Symbol.

(* This module uses only generated SOURCE syntax. In particular, it does not
   import an endpoint semantics, a local-effect model, or a progress predicate.

   S is the set of roles whose prefix arguments are currently available.
   A result relation describes PARTIAL families of actual results. It is not
   restricted to tuples with a result at every configured role. *)
Definition roles := Symbol -> Prop.
Definition values (A : Symbol -> Type) (S : roles) :=
  forall p, S p -> A p.
Definition includes (S T : roles) := forall p, S p -> T p.
Definition results (A : Symbol -> Type) :=
  forall S : roles, values A S -> Prop.
Definition programs (M : Type -> Type) (A : Symbol -> Type) (S : roles) :=
  forall p, S p -> Choreo M p (A p).

Definition pure_results {A S} (x : values A S) : results A :=
  fun D v => includes D S /\
    forall p (d : D p) (s : S p), v p d = x p s.

(* A non-owner's At contains no observable value. At the owner a local
   computation may return any actual value, including an opaque handle.
   Empty local result types still permit non-owner partial result families. *)
Definition located_results (X : Type) (l : Symbol) (S : roles)
    : results (fun p => At X l p) :=
  fun D _ => includes D S.

Definition comm_results {X l r S}
    (x : values (fun p => At X l p) S)
    : results (fun p => At X r p) :=
  fun D v => includes D S /\
    forall (s : S l) (d : D r),
      unAt (v r d) eq_refl = unAt (x l s) eq_refl.

Definition app_results {A B} (F : results (fun p => A p -> B p))
    (X : results A) : results B :=
  fun D v => exists (f : values (fun p => A p -> B p) D)
                   (x : values A D),
    F D f /\ X D x /\ forall p d, v p d = f p d (x p d).

Definition bind_results {A B} (P : results A)
    (K : forall D, values A D -> results B) : results B :=
  fun D v => exists S x, P S x /\ K S x D v.

Definition wire_law {X} (s : Show X) (r : Read X) :=
  forall x, @read X r (@show X s x) = Some x.

(* Codec dictionaries are those carried by the actual source constructors.
   Self communication never uses the wire. Role closure is checked even
   when the owner is not among the currently available roles. *)
#[universes(template)]
Inductive structural (R : list Symbol) (M : Type -> Type)
    : forall S A, programs M A S -> results A -> Prop :=
| WFPure : forall S A (x : values A S) c,
    (forall p s, c p s = Pure (x p s)) ->
    structural R M S A c (pure_results x)
| WFLocally : forall S X l
    (f : forall p, S p -> Unwrap l p -> M X) c,
    In l R ->
    (forall p s, c p s =
      Perf (@Locally M p X l (known l) MkSSymbol (f p s))) ->
    structural R M S (fun p => At X l p) c
      (located_results X l S)
| WFComm : forall S X l r
    (sh : forall p, S p -> Show X)
    (rd : forall p, S p -> Read X)
    (x : values (fun p => At X l p) S) c,
    In l R -> In r R ->
    (forall (s : S l) (t : S r),
      l <> r -> wire_law (sh l s) (rd r t)) ->
    (forall p s, c p s =
      Perf (@Comm M p X l r (sh p s) (rd p s)
        (known l) (known r) MkSSymbol (x p s) MkSSymbol)) ->
    structural R M S (fun p => At X r p) c (comm_results x)
| WFCond : forall S X l A
    (sh : forall p, S p -> Show X)
    (rd : forall p, S p -> Read X)
    (x : values (fun p => At X l p) S)
    (k : forall p, S p -> X -> Choreo M p (A p))
    (K : X -> results A) c,
    In l R ->
    (forall p (s : S l) (t : S p),
      p <> l -> wire_law (sh l s) (rd p t)) ->
    (forall a, structural R M S A (fun p s => k p s a) (K a)) ->
    (forall p s, c p s =
      Perf (@Cond M p X l (A p) (sh p s) (rd p s)
        (known l) MkSSymbol (x p s) (k p s))) ->
    structural R M S A c
      (fun D v => (forall p, ~ D p) \/
        exists a, K a D v /\
          forall s : S l, unAt (x l s) eq_refl = a)
| WFApp : forall S A B
    (f : programs M (fun p => A p -> B p) S)
    (x : programs M A S) F X c,
    structural R M S (fun p => A p -> B p) f F ->
    structural R M S A x X ->
    (forall p s, c p s = App (f p s) (x p s)) ->
    structural R M S B c (app_results F X)
| WFBind : forall S A B (t : programs M A S)
    (k : forall p, S p -> A p -> Choreo M p (B p)) P K c,
    structural R M S A t P ->
    (forall D (v : values A D) (inc : includes D S),
      P D v ->
      structural R M D B (fun p d => k p (inc p d) (v p d)) (K D v)) ->
    (forall p s, c p s = Bind (t p s) (k p s)) ->
    structural R M S B c (bind_results P K).

(* NoDup belongs to the public configured-network contract, not to each
   recursive structural judgement. Extra roles are deliberately allowed. *)
Definition well_formed (R : list Symbol) (M : Type -> Type)
    (A : Symbol -> Type) (c : forall p, Choreo M p (A p)) : Prop :=
  NoDup R /\ exists Q,
    structural R M (fun p => In p R) A (fun p _ => c p) Q.

(* Use the generated At eliminator with the correct owner evidence. *)
Definition owner_unwrap (l : Symbol) : Unwrap l l :=
  fun X x => @unAt X l l x eq_refl.

Definition off_role {X l p} (ne : l <> p) : At X l p :=
  Mk_At (fun e => False_rect X (ne e)).

Definition communication_head {M p A} (c : Choreo M p A)
    : option (Symbol * Symbol) :=
  match c with
  | Perf (@Comm _ _ _ l r _ _ _ _ _ _ _) => Some (l, r)
  | _ => None
  end.

Definition encodes {M p A} (c : Choreo M p A) (s : GHC.Base.String) :=
  match c with
  | Perf (@Comm _ _ X _ _ sh _ _ _ _ _ _) =>
      exists x : X, @show X sh x = s
  | _ => False
  end.

Definition decodes {M p A} (c : Choreo M p A) (s : GHC.Base.String) :=
  match c with
  | Perf (@Comm _ _ X _ _ _ rd _ _ _ _ _) =>
      exists x : X, @read X rd s = Some x
  | _ => False
  end.

Lemma structural_head R M S A c Q :
  structural R M S A c Q ->
  forall p q (s : S p) (t : S q),
    communication_head (c p s) = communication_head (c q t).
Proof.
  intros H; induction H; intros p q ps qt;
    repeat match goal with
    | E : forall p s, _ = _ |- _ => rewrite (E p ps), (E q qt)
    end; reflexivity.
Qed.

Lemma structural_head_roles R M S A c Q :
  structural R M S A c Q ->
  forall p (s : S p) l r,
    communication_head (c p s) = Some (l,r) -> In l R /\ In r R.
Proof.
  intros H; induction H; intros p s a b;
    match goal with E : forall p s, _ = _ |- _ => rewrite (E p s) end;
    cbn; intro E; try discriminate.
  inversion E; subst; auto.
Qed.

Lemma structural_wire R M S A c Q :
  structural R M S A c Q ->
  forall l r (s : S l) (t : S r) wire,
    communication_head (c l s) = Some (l,r) ->
    l <> r -> encodes (c l s) wire -> decodes (c r t) wire.
Proof.
  intros H; induction H; intros a b ps qt wire;
    match goal with E : forall p s, _ = _ |- _ =>
      rewrite (E a ps), (E b qt)
    end; cbn; intros E ne payload; try discriminate.
  inversion E; subst.
  destruct payload as [v <-].
  exists v. apply H1; assumption.
Qed.
