Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree
  Choreography.Network Choreography.Choreo2.
Require Control.Monad.Trans.Reader Data.Either.
From ParkourTheories.Projection Require Import EndpointRunner.
From ParkourTheories.Semantics Require Import Roles.

Theorem runner_pure :
  forall (m : Type -> Type) p X (x : X) sid,
    runner (@Pure (ChoreoSig m p) X x) sid = Pure x.
Proof. reflexivity. Qed.

Theorem runner_bind :
  forall (m : Type -> Type) p X Y (c : Choreo m p X)
    (k : X -> Choreo m p Y) sid,
    runner (Bind c k) sid =
      Bind (runner c sid) (fun x => runner (k x) sid).
Proof. reflexivity. Qed.

Theorem runner_app :
  forall (m : Type -> Type) p X Y (f : Choreo m p (X -> Y))
    (x : Choreo m p X) sid,
    runner (App f x) sid =
      App (runner f (Nest (Data.Either.Left tt) sid))
          (runner x (Nest (Data.Either.Right tt) sid)).
Proof. reflexivity. Qed.

Theorem runner_locally_owner :
  forall (m : Type -> Type) l X (known_l : KnownSymbol l)
    (body : Unwrap l l -> m X) sid,
    runner (@locally l l m X known_l MkSSymbol body) sid =
      Bind (Perf (Exec (body (@unwrap l l eq_refl))))
        (fun x => Pure (Mk_At (fun _ => x))).
Proof.
  intros m l X kl body sid.
  unfold runner, Choreography.Choreo2.locally.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol l)
                                (@Parkour.Symbol.MkSSymbol l)) as [pf | npf].
  - rewrite (symbol_uip l l pf eq_refl). reflexivity.
  - exact (GHC.Base.absurd (npf eq_refl)).
Qed.

Theorem runner_locally_other :
  forall (m : Type -> Type) l p X (known_l : KnownSymbol l)
    (body : Unwrap l p -> m X) (neq : l <> p) sid,
    runner (@locally l p m X known_l MkSSymbol body) sid =
      Pure (absent neq).
Proof.
  intros m l p X kl body neq sid.
  unfold runner, Choreography.Choreo2.locally, absent, off_role.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol l)
                                (@Parkour.Symbol.MkSSymbol p)) as [pf | npf].
  - exact (False_rect _ (neq pf)).
  - reflexivity.
Qed.

Theorem runner_comm_self :
  forall (m : Type -> Type) l p X (sh : Show X) (rd : Read X)
    (kl kr : KnownSymbol l) (x : At X l p) sid,
    runner (Perf (@Comm m p X l l sh rd kl kr MkSSymbol x MkSSymbol)) sid =
      Pure x.
Proof.
  intros m l p X sh rd kl kr x sid.
  unfold runner.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol l)
                                (@Parkour.Symbol.MkSSymbol l)) as [pf | npf].
  - rewrite (symbol_uip l l pf eq_refl). reflexivity.
  - exact (GHC.Base.absurd (npf eq_refl)).
Qed.

Theorem runner_comm_sender :
  forall (m : Type -> Type) s r X (sh : Show X) (rd : Read X)
    (ks : KnownSymbol s) (kr : KnownSymbol r)
    (x : At X s s) (neq : r <> s) sid,
    runner (Perf (@Comm m s X s r sh rd ks kr MkSSymbol x MkSSymbol)) sid =
      Bind (Pure sid) (fun tag =>
        App (Bind (Perf (@Send m X sh tag (unAt x eq_refl) r))
                   (fun _ => Pure (fun v : At X r s => v)))
            (Pure (absent neq))).
Proof.
  intros m s r X sh rd ks kr x neq sid.
  unfold runner, absent, off_role.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol s)
                                (@Parkour.Symbol.MkSSymbol r)) as [pf | npf].
  - exact (False_rect _ (neq (eq_sym pf))).
  - destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol s)
                                  (@Parkour.Symbol.MkSSymbol s)) as [pfs |
                                    npf'].
    + rewrite (symbol_uip s s pfs eq_refl).
      destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol r)
                                    (@Parkour.Symbol.MkSSymbol s)) as [pfr |
                                      npf''].
      * exact (False_rect _ (neq pfr)).
      * reflexivity.
    + exact (GHC.Base.absurd (npf' eq_refl)).
Qed.

Theorem runner_comm_receiver :
  forall (m : Type -> Type) s r X (sh : Show X) (rd : Read X)
    (ks : KnownSymbol s) (kr : KnownSymbol r)
    (x : At X s r) (neq : s <> r) sid,
    runner (Perf (@Comm m r X s r sh rd ks kr MkSSymbol x MkSSymbol)) sid =
      Bind (Pure sid) (fun tag =>
        Bind (Perf (@Recv m X rd tag s))
             (fun v => Pure (Mk_At (fun _ => v)))).
Proof.
  intros m s r X sh rd ks kr x neq sid.
  unfold runner.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol s)
                                (@Parkour.Symbol.MkSSymbol r)) as [pf | npf].
  - exact (False_rect _ (neq pf)).
  - destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol r)
                                  (@Parkour.Symbol.MkSSymbol r)) as [pfr |
                                    npf'].
    + reflexivity.
    + exact (GHC.Base.absurd (npf' eq_refl)).
Qed.

Theorem runner_comm_other :
  forall (m : Type -> Type) s r p X (sh : Show X) (rd : Read X)
    (ks : KnownSymbol s) (kr : KnownSymbol r)
    (x : At X s p) (distinct : s <> r)
    (ns : s <> p) (nr : r <> p) sid,
    runner (Perf (@Comm m p X s r sh rd ks kr MkSSymbol x MkSSymbol)) sid =
      Pure (absent nr).
Proof.
  intros m s r p X sh rd ks kr x distinct ns nr sid.
  unfold runner, absent, off_role.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol s)
                                (@Parkour.Symbol.MkSSymbol r)) as [pf | npf].
  - exact (False_rect _ (distinct pf)).
  - destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol s)
                                  (@Parkour.Symbol.MkSSymbol p)) as [pfs |
                                    npf'].
    + exact (False_rect _ (ns pfs)).
    + destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol r)
                                    (@Parkour.Symbol.MkSSymbol p)) as [pfr |
                                      npf''].
      * exact (False_rect _ (nr pfr)).
      * reflexivity.
Qed.

Theorem runner_cond_owner :
  forall (m : Type -> Type) l X Y (sh : Show X) (rd : Read X)
    (kl : KnownSymbol l) (x : At X l l) (k : X -> Choreo m l Y) sid,
    runner (Perf (@Cond m l X l Y sh rd kl MkSSymbol x k)) sid =
      Bind (Bind (Pure sid)
                 (fun tag => Perf (@BCast m X sh tag (unAt x eq_refl))))
           (fun _ => runner (k (unAt x eq_refl)) sid).
Proof.
  intros m l X Y sh rd kl x k sid.
  unfold runner.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol l)
                                (@Parkour.Symbol.MkSSymbol l)) as [pf | npf].
  - rewrite (symbol_uip l l pf eq_refl). reflexivity.
  - exact (GHC.Base.absurd (npf eq_refl)).
Qed.

Theorem runner_cond_peer :
  forall (m : Type -> Type) l p X Y (sh : Show X) (rd : Read X)
    (kl : KnownSymbol l) (x : At X l p) (k : X -> Choreo m p Y)
    (neq : l <> p) sid,
    runner (Perf (@Cond m p X l Y sh rd kl MkSSymbol x k)) sid =
      Bind (Bind (Pure sid) (fun tag => Perf (@Recv m X rd tag l)))
           (fun v => runner (k v) sid).
Proof.
  intros m l p X Y sh rd kl x k neq sid.
  unfold runner.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol l)
                                (@Parkour.Symbol.MkSSymbol p)) as [pf | npf].
  - exact (False_rect _ (neq pf)).
  - reflexivity.
Qed.

Theorem runner_par :
  forall (m : Type -> Type) p X Y (x : Choreo m p X) (y : Choreo m p Y) sid,
    runner (par x y) sid =
      App (App (Pure (fun (_ : X) (_ : Y) => tt))
               (runner x (Nest (Data.Either.Right tt)
                              (Nest (Data.Either.Left tt) sid))))
          (runner y (Nest (Data.Either.Right tt) sid)).
Proof. reflexivity. Qed.

Theorem runner_root :
  forall (m : Type -> Type) p X (c : Choreo m p X),
    runner c Root =
      Control.Monad.Trans.Reader.runReaderT
        (unEpp (epp c (@MkSSymbol p))) Root.
Proof. reflexivity. Qed.
