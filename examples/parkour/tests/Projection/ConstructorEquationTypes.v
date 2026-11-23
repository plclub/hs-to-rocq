(* Independent slice-7 constructor contracts. Freeze this file before proving
   them; all trees below are literal generated control, not an interpreter. *)
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree
  Choreography.Network Choreography.Choreo2.
Require Control.Monad.Trans.Reader Data.Either.

From ParkourTheories.Projection Require Import EndpointRunner.

Definition pure_equation : Prop :=
  forall (m : Type -> Type) p X (x : X) sid,
    runner (@Pure (ChoreoSig m p) X x) sid = Pure x.

Definition bind_equation : Prop :=
  forall (m : Type -> Type) p X Y (c : Choreo m p X)
    (k : X -> Choreo m p Y) sid,
    runner (Bind c k) sid =
      Bind (runner c sid) (fun x => runner (k x) sid).

Definition app_equation : Prop :=
  forall (m : Type -> Type) p X Y (f : Choreo m p (X -> Y))
    (x : Choreo m p X) sid,
    runner (App f x) sid =
      App (runner f (Nest (Data.Either.Left tt) sid))
          (runner x (Nest (Data.Either.Right tt) sid)).

Definition locally_owner_equation : Prop :=
  forall (m : Type -> Type) l X (known_l : KnownSymbol l)
    (body : Unwrap l l -> m X) sid,
    runner (@locally l l m X known_l MkSSymbol body) sid =
      Bind (Perf (Exec (body (@unwrap l l eq_refl))))
        (fun x => Pure (Mk_At (fun _ => x))).

Definition locally_other_equation : Prop :=
  forall (m : Type -> Type) l p X (known_l : KnownSymbol l)
    (body : Unwrap l p -> m X) (neq : l <> p) sid,
    runner (@locally l p m X known_l MkSSymbol body) sid =
      Pure (absent neq).

Definition comm_self_equation : Prop :=
  forall (m : Type -> Type) l p X (sh : Show X) (rd : Read X)
    (kl kr : KnownSymbol l) (x : At X l p) sid,
    runner (Perf (@Comm m p X l l sh rd kl kr MkSSymbol x MkSSymbol)) sid =
      Pure x.

Definition comm_sender_equation : Prop :=
  forall (m : Type -> Type) s r X (sh : Show X) (rd : Read X)
    (ks : KnownSymbol s) (kr : KnownSymbol r)
    (x : At X s s) (neq : r <> s) sid,
    runner (Perf (@Comm m s X s r sh rd ks kr MkSSymbol x MkSSymbol)) sid =
      Bind (Pure sid) (fun tag =>
        App (Bind (Perf (@Send m X sh tag (unAt x eq_refl) r))
                   (fun _ => Pure (fun v : At X r s => v)))
            (Pure (absent neq))).

Definition comm_receiver_equation : Prop :=
  forall (m : Type -> Type) s r X (sh : Show X) (rd : Read X)
    (ks : KnownSymbol s) (kr : KnownSymbol r)
    (x : At X s r) (neq : s <> r) sid,
    runner (Perf (@Comm m r X s r sh rd ks kr MkSSymbol x MkSSymbol)) sid =
      Bind (Pure sid) (fun tag =>
        Bind (Perf (@Recv m X rd tag s))
             (fun v => Pure (Mk_At (fun _ => v)))).

Definition comm_other_equation : Prop :=
  forall (m : Type -> Type) s r p X (sh : Show X) (rd : Read X)
    (ks : KnownSymbol s) (kr : KnownSymbol r)
    (x : At X s p) (distinct : s <> r)
    (ns : s <> p) (nr : r <> p) sid,
    runner (Perf (@Comm m p X s r sh rd ks kr MkSSymbol x MkSSymbol)) sid =
      Pure (absent nr).

Definition cond_owner_equation : Prop :=
  forall (m : Type -> Type) l X Y (sh : Show X) (rd : Read X)
    (kl : KnownSymbol l) (x : At X l l) (k : X -> Choreo m l Y) sid,
    runner (Perf (@Cond m l X l Y sh rd kl MkSSymbol x k)) sid =
      Bind (Bind (Pure sid)
                 (fun tag => Perf (@BCast m X sh tag (unAt x eq_refl))))
           (fun _ => runner (k (unAt x eq_refl)) sid).

Definition cond_peer_equation : Prop :=
  forall (m : Type -> Type) l p X Y (sh : Show X) (rd : Read X)
    (kl : KnownSymbol l) (x : At X l p) (k : X -> Choreo m p Y)
    (neq : l <> p) sid,
    runner (Perf (@Cond m p X l Y sh rd kl MkSSymbol x k)) sid =
      Bind (Bind (Pure sid) (fun tag => Perf (@Recv m X rd tag l)))
           (fun v => runner (k v) sid).

Definition par_equation : Prop :=
  forall (m : Type -> Type) p X Y (x : Choreo m p X) (y : Choreo m p Y) sid,
    runner (par x y) sid =
      App (App (Pure (fun (_ : X) (_ : Y) => tt))
               (runner x (Nest (Data.Either.Right tt)
                              (Nest (Data.Either.Left tt) sid))))
          (runner y (Nest (Data.Either.Right tt) sid)).

Definition root_equation : Prop :=
  forall (m : Type -> Type) p X (c : Choreo m p X),
    runner c Root =
      Control.Monad.Trans.Reader.runReaderT
        (unEpp (epp c (@MkSSymbol p))) Root.
