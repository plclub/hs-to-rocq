Require Main.
Require Choreography.Choreo2 Choreography.Network Control.Monad.Trans.Reader.

(* Use the four singleton declarations expanded by the upstream mkLoc splices.
   Each expected type forces projection all the way to a network at Root. *)
Check (Control.Monad.Trans.Reader.runReaderT
  (Choreography.Choreo2.unEpp
    (Choreography.Choreo2.epp Main.quorumVoting Main.candidate))
  Choreography.Network.Root : Choreography.Network.Network Parkour.Runtime.IO
    unit).
Check (Control.Monad.Trans.Reader.runReaderT
  (Choreography.Choreo2.unEpp
    (Choreography.Choreo2.epp Main.quorumVoting Main.voter1))
  Choreography.Network.Root : Choreography.Network.Network Parkour.Runtime.IO
    unit).
Check (Control.Monad.Trans.Reader.runReaderT
  (Choreography.Choreo2.unEpp
    (Choreography.Choreo2.epp Main.quorumVoting Main.voter2))
  Choreography.Network.Root : Choreography.Network.Network Parkour.Runtime.IO
    unit).
Check (Control.Monad.Trans.Reader.runReaderT
  (Choreography.Choreo2.unEpp
    (Choreography.Choreo2.epp Main.quorumVoting Main.voter3))
  Choreography.Network.Root : Choreography.Network.Network Parkour.Runtime.IO
    unit).
