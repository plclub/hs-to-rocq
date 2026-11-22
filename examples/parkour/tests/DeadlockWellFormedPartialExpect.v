From Stdlib Require Import Lists.List.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Codec Parkour.Symbol.
Require Import DeadlockWellFormedExpect.

Definition pure_case p : Choreo effect p (At bool alice p) :=
  Pure (truth alice p).
Definition app_case p : Choreo effect p (At bool alice p) :=
  App (Pure (fun x : At bool alice p => x)) (pure_case p).
Definition bind_case p : Choreo effect p (At bool alice p) :=
  Bind (pure_case p) (fun x => Pure x).
Definition cond_case p : Choreo effect p (At bool alice p) :=
  Perf (@Cond effect p bool alice (At bool alice p) show_bool read_bool
    (known alice) MkSSymbol (truth alice p)
    (fun b => Pure (Mk_At (fun _ => b)))).

Definition accepts_pure_app_bind_cond
    (wf : forall (R : list Symbol) (M : Type -> Type)
      (A : Symbol -> Type), (forall p, Choreo M p (A p)) -> Prop) : Prop :=
  wf participants effect (fun p => At bool alice p) pure_case /\
  wf participants effect (fun p => At bool alice p) app_case /\
  wf participants effect (fun p => At bool alice p) bind_case /\
  wf participants effect (fun p => At bool alice p) cond_case.

(* This is the literal continuation obligation, not a complete-result-tuple
   surrogate. The owner cannot supply an Empty_set value. Both other roles
   nevertheless have their actual At values and their continuations disagree.
   The public full-family rejection in the earlier frozen file is a separate,
   stronger acceptance statement. *)
Definition rejects_partial_empty_continuation
    (related : forall D : Symbol -> Prop,
      (forall p, D p -> At Empty_set alice p) -> Prop)
    (coherent : forall D : Symbol -> Prop,
      (forall p, D p -> Choreo effect p (At bool p p)) -> Prop) : Prop :=
  ~ (forall D (v : forall p, D p -> At Empty_set alice p),
    (forall p, D p -> In p participants) ->
    related D v -> coherent D (fun p _ => two_receivers p)).
