From Stdlib Require Import Lists.List.
Require Import Choreography.Network.
Import ListNotations.

Definition role := Choreography.Location.LocTm.
Definition wire := GHC.Base.String.
Definition key := (role * role * SessionId)%type.
Definition word_eq_dec (x y : BinNums.N) : {x = y} + {x <> y}.
Proof. decide equality; decide equality. Defined.
Definition role_eq_dec := list_eq_dec word_eq_dec.
Definition session_eq_dec (x y : SessionId) : {x = y} + {x <> y}.
Proof. decide equality; decide equality; decide equality. Defined.
Definition key_eq_dec (x y : key) : {x = y} + {x <> y}.
Proof.
  decide equality; [apply session_eq_dec | decide equality; apply role_eq_dec].
Defined.

Definition queues := key -> list wire.
Definition empty_queues : queues := fun _ => [].
Definition replace_queue (q : queues) (k : key) (ws : list wire) : queues :=
  fun j => if key_eq_dec j k then ws else q j.
Definition enqueue (q : queues) (k : key) (w : wire) : queues :=
  replace_queue q k (q k ++ [w]).
Fixpoint announce (rs : list role) (p : role) (sid : SessionId)
    (w : wire) (q : queues) : queues :=
  match rs with
  | [] => q
  | r :: rs' => announce rs' p sid w
      (if role_eq_dec p r then q else enqueue q (p,r,sid) w)
  end.

Lemma replace_same q k ws : replace_queue q k ws k = ws.
Proof. unfold replace_queue. destruct (key_eq_dec k k); congruence. Qed.
Lemma replace_other q k j ws :
  j <> k -> replace_queue q k ws j = q j.
Proof. intros H. unfold replace_queue. destruct (key_eq_dec j k); congruence.
Qed.
Lemma enqueue_same q k w : enqueue q k w k = q k ++ [w].
Proof. apply replace_same. Qed.
