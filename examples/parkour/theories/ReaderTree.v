Require Choreography.Network Control.Monad.Tree Control.Monad.Trans.Reader.

(* The existential in Tree.Bind puts a tree above its result index in the
   universe hierarchy. Explicit instances distinguish a universe conflict
   from an instance-search failure when building the projection's reader. *)
Definition readerNetworkMonad (m : Type -> Type) :=
  @Control.Monad.Trans.Reader.Monad__ReaderT
    (Choreography.Network.Network m) Choreography.Network.SessionId
    (@Control.Monad.Tree.Functor__Tree (Choreography.Network.NetworkSig m))
    (@Control.Monad.Tree.Applicative__Tree (Choreography.Network.NetworkSig m))
    (@Control.Monad.Tree.Monad__Tree (Choreography.Network.NetworkSig m)).
