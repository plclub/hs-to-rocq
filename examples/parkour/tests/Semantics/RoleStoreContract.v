From ITree Require Import ITree.
From ParkourTheories.Semantics Require Import LocalEffects.

(* In the public contract each endpoint has private memory, and all roles
   consume the same input state. A reply can update both in one step. *)
Definition state_contract {M E : Type -> Type} {Role Store Input : Type}
    (base : local_model M E Role (Store * Input))
    (whole : local_model M E Role ((Role -> Store) * Input)) :=
  (forall X (op : M X),
    interpret_local _ _ _ _ whole X op = interpret_local _ _ _ _ base X op) /\
  (forall X p (event : E X) (before after : Role -> Store) i j result,
    reply_local _ _ _ _ whole X p event (before, i) result (after, j) <->
    reply_local _ _ _ _ base X p event (before p, i) result (after p, j) /\
    (forall other, other <> p -> after other = before other)).
