From Stdlib Require Import Lists.List.
Import ListNotations.

(* Literal contracts for abstract run glue, independent of its implementation.
   These do not specify or assume an EPP correspondence. *)
Section Contracts.
Context {S A : Type}.
Variable step : S -> A -> S -> Prop.
Variable final : S -> Prop.

Definition ready_equation (candidate : S -> Prop) : Prop :=
  forall s, candidate s <-> final s \/ exists a y, step s a y.
Definition stuck_equation (candidate : S -> Prop) : Prop :=
  forall s, candidate s <-> ~ final s /\ forall a y, ~ step s a y.
Definition DF_equation
    (run : S -> list A -> S -> Prop) (candidate : S -> Prop) : Prop :=
  forall s, candidate s <->
    forall tr y, run s tr y -> final y \/ exists a z, step y a z.
Definition run_empty (run : S -> list A -> S -> Prop) : Prop :=
  forall s y, run s [] y <-> s = y.
Definition run_extension (run : S -> list A -> S -> Prop) : Prop :=
  forall s tr a y, run s (tr ++ [a]) y <->
    exists x, run s tr x /\ step x a y.
Definition run_composition (run : S -> list A -> S -> Prop) : Prop :=
  forall s tr tr' y, run s (tr ++ tr') y <->
    exists x, run s tr x /\ run x tr' y.
End Contracts.
