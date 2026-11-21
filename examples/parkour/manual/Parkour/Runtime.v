Require GHC.Base GHC.Err Control.Monad.Fail Parkour.Codec.
Import String.StringSyntax.

(* These effects are abstract. The base library's empty IO placeholder
   cannot support even getLine without introducing a contradiction. *)
Parameter IO STM : Type -> Type.
Parameter TVar : Type -> Type.

(* Only return and bind are primitive in each sequential monad. *)
Section Sequential.
  Context (m : Type -> Type)
          (ret : forall {a}, a -> m a)
          (bind : forall {a b}, m a -> (a -> m b) -> m b).
  Arguments ret {a}.
  Arguments bind {a b}.

  Definition functor : GHC.Base.Functor m :=
    fun _ k => k {| GHC.Base.fmap__ :=
                      fun _ _ f x => bind x (fun v => ret (f v));
                    GHC.Base.op_zlzd____ :=
                      fun _ _ v x => bind x (fun _ => ret v) |}.
  #[local] Existing Instance functor.
  Definition applicative : GHC.Base.Applicative m :=
    fun _ k => k {| GHC.Base.pure__ := @ret;
                    GHC.Base.op_zlztzg____ :=
                      fun _ _ f x => bind f (fun g => bind x (fun v => ret (g v)));
                    GHC.Base.op_ztzg____ := fun _ _ x y => bind x (fun _ => y);
                    GHC.Base.liftA2__ :=
                      fun _ _ _ f x y => bind x (fun v => bind y (fun w => ret (f v w))) |}.
  #[local] Existing Instance applicative.
  Definition monad : GHC.Base.Monad m :=
    fun _ k => k {| GHC.Base.return___ := @ret;
                    GHC.Base.op_zgzgze____ := @bind;
                    GHC.Base.op_zgzg____ := fun _ _ x y => bind x (fun _ => y) |}.
End Sequential.

Parameter returnIO : forall {a}, a -> IO a.
Parameter bindIO : forall {a b}, IO a -> (a -> IO b) -> IO b.
Parameter returnSTM : forall {a}, a -> STM a.
Parameter bindSTM : forall {a b}, STM a -> (a -> STM b) -> STM b.
#[global] Instance functorIO : GHC.Base.Functor IO := functor IO (@returnIO) (@bindIO).
#[global] Instance applicativeIO : GHC.Base.Applicative IO := applicative IO (@returnIO) (@bindIO).
#[global] Instance monadIO : GHC.Base.Monad IO := monad IO (@returnIO) (@bindIO).
#[global] Instance functorSTM : GHC.Base.Functor STM := functor STM (@returnSTM) (@bindSTM).
#[global] Instance applicativeSTM : GHC.Base.Applicative STM := applicative STM (@returnSTM) (@bindSTM).
#[global] Instance monadSTM : GHC.Base.Monad STM := monad STM (@returnSTM) (@bindSTM).

Parameter failIO : forall {a}, GHC.Base.String -> IO a.
#[global] Instance monadFailIO : Control.Monad.Fail.MonadFail IO :=
  fun _ k => k {| Control.Monad.Fail.fail__ := @failIO |}.
#[global] Instance defaultIO {a} : HsToRocq.Err.Default (IO a) :=
  {| HsToRocq.Err.default := failIO (GHC.Base.hs_string__ "pattern match failure") |}.

Parameter getLine : IO GHC.Base.String.
Parameter putStrLn : GHC.Base.String -> IO unit.
Parameter getArgs : IO (list GHC.Base.String).
Parameter newTVarIO : forall {a}, a -> IO (TVar a).
Parameter readTVar : forall {a}, TVar a -> STM a.
Parameter writeTVar : forall {a}, TVar a -> a -> STM unit.
Parameter retry : forall {a}, STM a.
Parameter atomically : forall {a}, STM a -> IO a.

Definition modifyTVar {a} (t : TVar a) (f : a -> a) : STM unit :=
  bindSTM (readTVar t) (fun v => writeTVar t (f v)).
Definition check (b : bool) : STM unit := if b then returnSTM tt else retry.

Definition read {a} `{Parkour.Codec.Read a} `{HsToRocq.Err.Default a}
    (s : GHC.Base.String) : a :=
  match Parkour.Codec.read s with
  | Some v => v
  | None => GHC.Err.error (GHC.Base.hs_string__ "Prelude.read: no parse")
  end.
