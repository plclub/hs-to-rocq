From ParkourTheories.Network Require Import Endpoints Execution.

(* These converses are about genuine steps of the independent interpreter.
   A structural test that merely overapproximates actions is insufficient. *)
Definition role_enabled_contract : Prop :=
  forall M E S model roles p A (t : @control M E A) q (s : S),
    possible model p t q s <->
    exists a u q' s', Endpoints.step model roles p A t q s a u q' s'.

Definition network_enabled_contract : Prop :=
  forall M E S model roles (c : @configuration M E S),
    endpoints_possible model (mailboxes c) (shared_store c) (endpoints c)
    <-> exists a d, Network.Execution.step model roles c a d.

Definition returns_unique_contract : Prop :=
  forall M E S model A (t : @control M E A) x y,
    @returns M E S model A t x -> returns model A t y -> x = y.

Definition returns_no_action_contract : Prop :=
  forall M E S model A (t : @control M E A) x roles p q s a u q' s',
    @returns M E S model A t x -> ~ Endpoints.step model roles p A t q s a u q'
      s'.
