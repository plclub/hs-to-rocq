Require Import HsToRocq.Err.
Require Import FingerTreeProofs.CoreSize.

(* The source's partial branches use `error`; Coq needs an arbitrary result
   inhabitant.  The adjacent core midamble supplies the same kind of local
   default for `FingerTree`.  This is internal error infrastructure, not a
   public operation premise. *)
#[local] Instance DefaultPQueue {k v : Type} : Default (PQueue k v) :=
  {| default := MkPQueue Data.FingerTree.Empty |}.

(* Raw structural size of the queue's underlying finger tree.  Cached Prio
   measurements are ignored.  This helper is retained for the termination
   analysis and later correctness work; the measure obligation itself is not
   discharged. *)
Definition pqueue_size {k v : Type} (q : PQueue k v) : nat :=
  match q with MkPQueue t => size t end.