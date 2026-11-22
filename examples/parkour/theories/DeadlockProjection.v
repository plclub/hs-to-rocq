Require Import DeadlockProjectionExpect.
From Stdlib Require Import Logic.Eqdep_dec.

(* Only decidable equality UIP, never an equality/proof-irrelevance axiom. *)
Definition symbol_eq_dec (s t : Parkour.Symbol.Symbol) :=
  List.list_eq_dec BinNat.N.eq_dec s t.

Lemma symbol_uip (s t : Parkour.Symbol.Symbol) (p q : s = t) : p = q.
Proof. apply UIP_dec. exact symbol_eq_dec. Qed.

Theorem runner_pure : pure_equation.
Proof. unfold pure_equation. reflexivity. Qed.

Theorem runner_bind : bind_equation.
Proof. unfold bind_equation. reflexivity. Qed.

Theorem runner_app : app_equation.
Proof. unfold app_equation. reflexivity. Qed.

Theorem runner_locally_owner : locally_owner_equation.
Proof.
  unfold locally_owner_equation. intros m l X kl body sid.
  unfold runner, Choreography.Choreo2.locally.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol l)
                                (@Parkour.Symbol.MkSSymbol l)) as [pf | npf].
  - rewrite (symbol_uip l l pf eq_refl). reflexivity.
  - exact (GHC.Base.absurd (npf eq_refl)).
Qed.

Theorem runner_locally_other : locally_other_equation.
Proof.
  unfold locally_other_equation. intros m l p X kl body neq sid.
  unfold runner, Choreography.Choreo2.locally, absent, off_role.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol l)
                                (@Parkour.Symbol.MkSSymbol p)) as [pf | npf].
  - exact (False_rect _ (neq pf)).
  - reflexivity.
Qed.

Theorem runner_comm_self : comm_self_equation.
Proof.
  unfold comm_self_equation. intros m l p X sh rd kl kr x sid.
  unfold runner.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol l)
                                (@Parkour.Symbol.MkSSymbol l)) as [pf | npf].
  - rewrite (symbol_uip l l pf eq_refl). reflexivity.
  - exact (GHC.Base.absurd (npf eq_refl)).
Qed.

Theorem runner_comm_sender : comm_sender_equation.
Proof.
  unfold comm_sender_equation. intros m s r X sh rd ks kr x neq sid.
  unfold runner, absent, off_role.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol s)
                                (@Parkour.Symbol.MkSSymbol r)) as [pf | npf].
  - exact (False_rect _ (neq (eq_sym pf))).
  - destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol s)
                                  (@Parkour.Symbol.MkSSymbol s)) as [pfs | npf'].
    + rewrite (symbol_uip s s pfs eq_refl).
      destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol r)
                                    (@Parkour.Symbol.MkSSymbol s)) as [pfr | npf''].
      * exact (False_rect _ (neq pfr)).
      * reflexivity.
    + exact (GHC.Base.absurd (npf' eq_refl)).
Qed.

Theorem runner_comm_receiver : comm_receiver_equation.
Proof.
  unfold comm_receiver_equation. intros m s r X sh rd ks kr x neq sid.
  unfold runner.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol s)
                                (@Parkour.Symbol.MkSSymbol r)) as [pf | npf].
  - exact (False_rect _ (neq pf)).
  - destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol r)
                                  (@Parkour.Symbol.MkSSymbol r)) as [pfr | npf'].
    + reflexivity.
    + exact (GHC.Base.absurd (npf' eq_refl)).
Qed.

Theorem runner_comm_other : comm_other_equation.
Proof.
  unfold comm_other_equation. intros m s r p X sh rd ks kr x distinct ns nr sid.
  unfold runner, absent, off_role.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol s)
                                (@Parkour.Symbol.MkSSymbol r)) as [pf | npf].
  - exact (False_rect _ (distinct pf)).
  - destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol s)
                                  (@Parkour.Symbol.MkSSymbol p)) as [pfs | npf'].
    + exact (False_rect _ (ns pfs)).
    + destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol r)
                                    (@Parkour.Symbol.MkSSymbol p)) as [pfr | npf''].
      * exact (False_rect _ (nr pfr)).
      * reflexivity.
Qed.

Theorem runner_cond_owner : cond_owner_equation.
Proof.
  unfold cond_owner_equation. intros m l X Y sh rd kl x k sid.
  unfold runner.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol l)
                                (@Parkour.Symbol.MkSSymbol l)) as [pf | npf].
  - rewrite (symbol_uip l l pf eq_refl). reflexivity.
  - exact (GHC.Base.absurd (npf eq_refl)).
Qed.

Theorem runner_cond_peer : cond_peer_equation.
Proof.
  unfold cond_peer_equation. intros m l p X Y sh rd kl x k neq sid.
  unfold runner.
  cbn [Choreography.Choreo2.epp Control.Monad.Tree.interp].
  destruct (Parkour.Symbol.decide (@Parkour.Symbol.MkSSymbol l)
                                (@Parkour.Symbol.MkSSymbol p)) as [pf | npf].
  - exact (False_rect _ (neq pf)).
  - reflexivity.
Qed.

Theorem runner_par : par_equation.
Proof. unfold par_equation. reflexivity. Qed.

Theorem runner_root : root_equation.
Proof. unfold root_equation. reflexivity. Qed.
