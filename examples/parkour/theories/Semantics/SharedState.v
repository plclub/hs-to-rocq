From ParkourTheories.Semantics Require Import LocalEffects.

(* Both machines thread this single state through a scheduled step. The
   reply sees the acting role's memory and the common input; other roles'
   memories are framed pointwise, without function extensionality. *)
Definition shared_model {M E : Type -> Type} {Role Store Input : Type}
    (m : local_model M E Role (Store * Input))
    : local_model M E Role ((Role -> Store) * Input) :=
  {| interpret_local := interpret_local _ _ _ _ m;
     reply_local := fun X p event before x after =>
       reply_local _ _ _ _ m X p event (fst before p, snd before) x
                                        (fst after p, snd after) /\
       forall r, r <> p -> fst after r = fst before r |}.
