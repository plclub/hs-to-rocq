From Stdlib Require Import Lists.List.
From Stdlib Require NArith.BinNat.
Require Import Choreography.Network Control.Monad.Tree Parkour.Codec.
Import ListNotations.

(* Reliable FIFO channels. A decode failure cannot consume a message. *)
Definition loc := Choreography.Location.LocTm.
Definition wire := GHC.Base.String.
Definition channel := (loc * loc * SessionId)%type.
Definition loc_eq_dec := list_eq_dec BinNat.N.eq_dec.
Definition sid_eq_dec (x y : SessionId) : {x = y} + {x <> y}.
Proof. decide equality; decide equality; decide equality. Defined.
Definition channel_eq_dec (x y : channel) : {x = y} + {x <> y}.
Proof. decide equality; [apply sid_eq_dec | decide equality; apply loc_eq_dec]. Defined.
Definition queues := channel -> list wire.
Definition empty : queues := fun _ => [].
Definition put (q : queues) (c : channel) (xs : list wire) : queues :=
  fun d => if channel_eq_dec d c then xs else q d.
Definition enqueue q c x := put q c (q c ++ [x]).

Section Semantics.
Variable m : Type -> Type.
Variable roles : list loc.
(* The local-effect relation is supplied, not postulated. *)
Variable local : forall a, m a -> a -> Prop.
Definition net := Network m.
Fixpoint broadcast_to (sender : loc) (sid : SessionId) (w : wire)
    (rs : list loc) (q : queues) : queues :=
  match rs with
  | [] => q
  | r :: rest =>
      broadcast_to sender sid w rest
        (if loc_eq_dec sender r then q else enqueue q (sender,r,sid) w)
  end.

Inductive step (self : loc) : forall a, net a -> queues -> net a -> queues -> Prop :=
| S_exec : forall a (e : m a) v q,
    local a e v -> step self a (Perf (Exec e)) q (Pure v) q
| S_send : forall a (sh : Show a) sid (v : a) r q,
    step self unit (Perf (@Send m a sh sid v r)) q (Pure tt)
      (enqueue q (self,r,sid) (@show a sh v))
| S_recv : forall a (rd : Read a) sid sender q w ws v,
    q (sender,self,sid) = w :: ws ->
    @read a rd w = Some v ->
    step self a (Perf (@Recv m a rd sid sender)) q (Pure v)
      (put q (sender,self,sid) ws)
| S_bcast : forall a (sh : Show a) sid (v : a) q,
    step self unit (Perf (@BCast m a sh sid v)) q (Pure tt)
      (broadcast_to self sid (@show a sh v) roles q)
| S_bind : forall a b (t t' : net a) (k : a -> net b) q q',
    step self a t q t' q' ->
    step self b (Bind t k) q (Bind t' k) q'
| S_bind_done : forall a b (v : a) (k : a -> net b) q,
    step self b (Bind (Pure v) k) q (k v) q
| S_app_left : forall a b (f f' : net (a -> b)) (x : net a) q q',
    step self (a -> b) f q f' q' ->
    step self b (App f x) q (App f' x) q'
| S_app_right : forall a b (f : net (a -> b)) (x x' : net a) q q',
    step self a x q x' q' ->
    step self b (App f x) q (App f x') q'
| S_app_done : forall a b (f : a -> b) (x : a) q,
    step self b (App (Pure f) (Pure x)) q (Pure (f x)) q.

Definition final {a} (t : net a) : Prop := exists v, t = Pure v.
#[universes(template)]
Inductive run (self : loc) (a : Type) :
    net a -> queues -> net a -> queues -> Prop :=
| run_refl : forall t q, run self a t q t q
| run_cons : forall t q u r v s,
    step self a t q u r -> run self a u r v s ->
    run self a t q v s.
End Semantics.

Arguments step {m} roles local self {a}.
Arguments run {m} roles local self {a}.
Arguments final {m a}.

(* A necessary enabledness test avoids inversion on the indexed Tree syntax.
   Bind/Pure and App/Pure/Pure are the finite bookkeeping steps. *)
Definition is_pure {f a} (t : Tree f a) : Prop :=
  match t with Pure _ => True | _ => False end.
Fixpoint enabled {m a} (self : loc) (t : Network m a) (q : queues) : Prop :=
  match t with
  | Pure _ => False
  | Perf e =>
      match e with
      | Exec _ => True
      | Send _ _ _ => True
      | @Recv _ a rd sid sender =>
          exists w ws (v : a),
            q (sender,self,sid) = w :: ws /\ @read a rd w = Some v
      | BCast _ _ => True
      end
  | Bind t _ => enabled self t q \/ is_pure t
  | App f x => enabled self f q \/ enabled self x q \/
               (is_pure f /\ is_pure x)
  end.

Lemma step_enabled {m} roles local self a (t u : Network m a) q r :
  step roles local self t q u r -> enabled self t q.
Proof.
  intros H; induction H; simpl; eauto 8.
Qed.

Lemma put_same q c xs : put q c xs c = xs.
Proof. unfold put; destruct (channel_eq_dec c c); congruence. Qed.
Lemma put_other q c d xs : d <> c -> put q c xs d = q d.
Proof. intros H; unfold put; destruct (channel_eq_dec d c); congruence. Qed.
