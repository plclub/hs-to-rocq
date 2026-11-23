Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree
  Choreography.Network Choreography.Choreo2.
Require Control.Monad.Trans.Reader Data.Either.

Definition runner {m p X} (c : Choreo m p X) (sid : SessionId) :=
  Control.Monad.Trans.Reader.runReaderT
    (unEpp (epp c (@MkSSymbol p))) sid.

(* Retain precisely the negative evidence selected by the production decision.
   Choosing an arbitrary proof of inequality would require equality of
   functions merely to compare the empty off-role At representations. *)
Definition off_role (l p : Symbol) (neq : l <> p) : Equal l p -> GHC.Base.Void
  :=
  match decide (@MkSSymbol l) (@MkSSymbol p) with
  | Proved pf => False_rect _ (neq pf)
  | Disproved dpf => dpf
  end.

Definition absent {X l p} (neq : l <> p) : At X l p :=
  Mk_At (fun pf => GHC.Base.absurd (off_role l p neq pf)).
