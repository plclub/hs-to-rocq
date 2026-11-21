(* Load the generated upstream Tree and the Rocq 9 base on their usual -Q
   paths. This isolates the nested guard check from other Choreo2 features. *)
Require Import Control.Monad.Tree.

Inductive Op : Type -> Type :=
| Branch {A X : Type} : X -> (X -> Tree Op A) -> Op A.

Section Projection.
  Context {m : Type -> Type} `{GHC.Base.Applicative m} `{GHC.Base.Monad m}.

  Fixpoint handle {A} (e : Op A) {struct e} : m A :=
    match e with Branch x k => interp (@handle) (k x) end.

  Definition project {A} (t : Tree Op A) : m A := interp (@handle) t.

  Example branch_equation {A X} (x : X) (k : X -> Tree Op A) :
    project (Perf (Branch x k)) = project (k x).
  Proof. reflexivity. Qed.
End Projection.

Print Assumptions branch_equation.
