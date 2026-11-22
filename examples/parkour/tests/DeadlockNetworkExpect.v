From ITree Require Import ITree.
From Stdlib Require Import Lists.List.
Require Import DeadlockNetwork DeadlockLocal.
Require Import Control.Monad.Tree Choreography.Network Parkour.Codec.
Import ListNotations.

Inductive flag_event : Type -> Type :=
| Wait : flag_event unit
| SetFlag : flag_event unit.
Definition flag_reply (X : Type) (_ : role) (e : flag_event X)
    (s : bool) (x : X) (s' : bool) : Prop :=
  match e in flag_event Y return Y -> Prop with
  | Wait => fun _ => s = true /\ s' = s
  | SetFlag => fun _ => s' = true
  end x.
Definition flag_model : local_model (itree flag_event) flag_event role bool :=
  {| interpret_local := fun _ t => t; reply_local := flag_reply |}.
Definition alice : role := [].
Definition bob : role := [BinNums.Npos BinNums.xH].
Definition carol : role := [BinNums.N0].
Definition roles := [alice; bob; carol].
Definition wait : itree flag_event unit := Vis Wait (fun _ => Ret tt).
Definition set : itree flag_event unit := Vis SetFlag (fun _ => Ret tt).
Definition prog := @control (itree flag_event) flag_event.
Definition pure {A} (x : A) : prog A := CPure x.
Definition send (b : bool) : prog unit :=
  load (Perf (@Send (itree flag_event) bool show_bool Root b bob)).
Definition recv : prog bool :=
  load (Perf (@Recv (itree flag_event) bool read_bool Root alice)).
Definition wait_code : prog unit := load (Perf (Exec wait)).
Definition set_code : prog unit := load (Perf (Exec set)).
Definition act := @action flag_event bool.
Definition sent (b : bool) : act :=
  @Sent flag_event bool alice bob Root (@show bool show_bool b).
Definition received (b : bool) : act :=
  @Received flag_event bool alice bob Root (@show bool show_bool b).
Definition local_set (s : bool) : act :=
  @Local flag_event bool (LocalEvent alice SetFlag s tt true).
Definition local_wait : act :=
  @Local flag_event bool (LocalEvent alice Wait true tt true).
Definition can {A} p (t : prog A) q s a t' q' s' :=
  @step (itree flag_event) flag_event bool flag_model roles p A
    t q s a t' q' s'.
Definition done {A} (t : prog A) x :=
  @returns (itree flag_event) flag_event bool flag_model A t x.
Definition blocked {A} p (t : prog A) q s :=
  forall a t' q' s', ~ can p t q s a t' q' s'.

Definition send_first_contract : Prop :=
  can alice (send true) empty_queues false (sent true) (pure tt)
    (enqueue empty_queues (alice,bob,Root) (@show bool show_bool true)) false.
(* Queue functions are checked pointwise, not by functional extensionality:
   this residual is the actual update on the original nonempty queue. *)
Definition receive_exact_contract : Prop :=
  let q := enqueue empty_queues (alice,bob,Root) (@show bool show_bool true) in
  can bob recv q false (received true) (pure true)
    (replace_queue q (alice,bob,Root) []) false.

Definition left_send_contract : Prop :=
  can alice
    (CApp (CBind (send true) (fun _ => pure (fun b : bool => b))) recv)
    empty_queues false (sent true)
    (CApp (CBind (pure tt) (fun _ => pure (fun b : bool => b))) recv)
    (enqueue empty_queues (alice,bob,Root) (@show bool show_bool true)) false.
Definition right_send_contract : Prop :=
  can alice (CApp (CBind recv (fun _ => pure (fun _ : unit => tt))) (send true))
    empty_queues false (sent true)
    (CApp (CBind recv (fun _ => pure (fun _ : unit => tt))) (pure tt))
    (enqueue empty_queues (alice,bob,Root) (@show bool show_bool true)) false.
Definition two_receive_contract : Prop :=
  blocked bob (CApp (CBind recv (fun _ => pure (fun b : bool => b))) recv)
    empty_queues false.
Definition fifo_contract : Prop :=
  enqueue (enqueue empty_queues (alice,bob,Root) (@show bool show_bool true))
    (alice,bob,Root) (@show bool show_bool false) (alice,bob,Root) =
    [@show bool show_bool true; @show bool show_bool false].
Definition pure_join_contract : Prop :=
  done (CBind (CApp (pure (fun n : nat => S n)) (pure 4))
    (fun n => pure (S n))) 6.
Definition pure_no_action_contract : Prop :=
  blocked alice (pure tt) empty_queues false.
Definition shared_right_contract : Prop :=
  let t := load (Control.Monad.Tree.par (Perf (Exec wait)) (Perf (Exec set))) in
  exists u v,
    can alice t empty_queues false (local_set false) u empty_queues true /\
    can alice u empty_queues true local_wait v empty_queues true.
Definition shared_left_contract : Prop :=
  let t := load (Control.Monad.Tree.par (Perf (Exec set)) (Perf (Exec wait))) in
  exists u v,
    can alice t empty_queues false (local_set false) u empty_queues true /\
    can alice u empty_queues true local_wait v empty_queues true.
