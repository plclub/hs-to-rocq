Require GHC.Base Control.Monad.Trans.Reader.
Generalizable All Variables.

(* mtl-2.3.1, Control.Monad.Reader.Class: the MonadReader API and its
   ReaderT instance. Every operation delegates to translated transformers.
   Epp's derived MonadReader instance belongs to generated Choreo2. *)
#[universes(template)] Record MonadReader__Dict (r : Type) (m : Type -> Type) := {
  ask__ : m r;
  local__ : forall {a}, (r -> r) -> m a -> m a;
  reader__ : forall {a}, (r -> a) -> m a
}.
Definition MonadReader (r : Type) (m : Type -> Type) `{GHC.Base.Monad m} :=
  forall result : Type, (MonadReader__Dict r m -> result) -> result.
Existing Class MonadReader.
Definition ask `{d : MonadReader r m} : m r := d _ (ask__ r m).
Definition local `{d : MonadReader r m} : forall {a}, (r -> r) -> m a -> m a :=
  d _ (local__ r m).
Definition reader `{d : MonadReader r m} : forall {a}, (r -> a) -> m a :=
  d _ (reader__ r m).

#[global] Instance readerT_instance {r m} `{GHC.Base.Monad m}
  : MonadReader r (Control.Monad.Trans.Reader.ReaderT r m) :=
  fun _ k => k {| ask__ := Control.Monad.Trans.Reader.ask;
                  local__ := fun a f x => Control.Monad.Trans.Reader.local f x;
                  reader__ := fun a f => Control.Monad.Trans.Reader.reader f |}.
