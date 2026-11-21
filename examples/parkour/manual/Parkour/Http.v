Require Choreography.Location Choreography.Network Parkour.Runtime.

(* The transport implementation owns its configuration and executes the
   projected network. The public runner still chooses the location and
   computes that network using the generated projection. *)
Parameter HttpConfig : Type.
Parameter mkHttpConfig :
  list (Choreography.Location.LocTm * (GHC.Base.String * GHC.Num.Int)) -> HttpConfig.
Parameter runNetworkHttp : forall {a}, HttpConfig -> Choreography.Location.LocTm ->
  Choreography.Network.Network Parkour.Runtime.IO a -> Parkour.Runtime.IO a.

#[global] Instance backendHttp : Choreography.Network.Backend HttpConfig :=
  fun _ k => k {| Choreography.Network.runNetwork__ := @runNetworkHttp |}.
