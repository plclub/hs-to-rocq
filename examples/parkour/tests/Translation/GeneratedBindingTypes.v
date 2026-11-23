Require Control.Monad.Tree Choreography.Choreo2 Choreography.Network
  Choreography2 Main.
Require GHC.Base Parkour.Symbol Parkour.Runtime.

Check @Control.Monad.Tree.par :
  forall (f : Type -> Type) (a b : Type),
    Control.Monad.Tree.Tree f a -> Control.Monad.Tree.Tree f b ->
    Control.Monad.Tree.Tree f unit.

Check @Control.Monad.Tree.interp :
  forall (m f : Type -> Type) (a : Type)
    `{GHC.Base.Applicative m} `{GHC.Base.Monad m},
    (forall x : Type, f x -> m x) -> Control.Monad.Tree.Tree f a -> m a.

Check @Choreography.Choreo2.epp :
  forall (m : Type -> Type) (p : Parkour.Symbol.Symbol) (a : Type),
    Choreography.Choreo2.Choreo m p a -> Parkour.Symbol.SSymbol p ->
    Choreography.Choreo2.Epp m a.

Check @Choreography.Choreo2.unwrap :
  forall (l p : Parkour.Symbol.Symbol), l = p ->
    forall a : Type, Choreography.Choreo2.At a l p -> a.

Check @Choreography2.runChoreography :
  forall (config : Type) (p : Parkour.Symbol.Symbol) (a : Type),
    Choreography.Network.Backend config -> Parkour.Symbol.KnownSymbol p ->
    config -> Choreography.Choreo2.Choreo Parkour.Runtime.IO p a ->
    Parkour.Symbol.SSymbol p -> Parkour.Runtime.IO a.

Check @Main.quorumVoting :
  forall p : Parkour.Symbol.Symbol, Choreography.Choreo2.Choreo
    Parkour.Runtime.IO p unit.
