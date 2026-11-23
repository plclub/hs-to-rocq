From Stdlib Require Import Lists.List NArith.BinNatDef.
From Stdlib Require NArith.BinNat.
Module N.
  Include BinNatDef.N.
  Definition eq_dec := BinNat.N.eq_dec.
End N.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Codec
  Parkour.Symbol.
Import ListNotations.

(* Frozen inputs and literal propositions, separate from implementation and
   proof bodies. The manifest pins this file before proofs are attempted. *)
Definition alice : Symbol := [].
Definition bob : Symbol := [1%N].
Definition carol : Symbol := [2%N].
Definition participants := [alice; bob; carol].
Definition effect (_ : Type) := unit.
Definition truth (l p : Symbol) : At bool l p := Mk_At (fun _ => true).

Definition communicating p : Choreo effect p (At bool bob p) :=
  Perf (@Comm effect p bool alice bob show_bool read_bool
    (known alice) (known bob) MkSSymbol (truth alice p) MkSSymbol).

Definition located p : Choreo effect p (At Empty_set alice p) :=
  Perf (@Locally effect p Empty_set alice (known alice) MkSSymbol
    (fun _ => tt)).

Definition two_receivers p : Choreo effect p (At bool p p) :=
  let sender := if List.list_eq_dec N.eq_dec p alice then bob else alice in
  Perf (@Comm effect p bool sender p show_bool read_bool
    (known sender) (known p) MkSSymbol (truth sender p) MkSSymbol).

Definition broken_read : Read bool := fun _ => None.
Definition wrong_codec p : Choreo effect p (At bool bob p) :=
  Perf (@Comm effect p bool alice bob show_bool broken_read
    (known alice) (known bob) MkSSymbol (truth alice p) MkSSymbol).

Definition self_communication p : Choreo effect p (At bool alice p) :=
  Perf (@Comm effect p bool alice alice show_bool broken_read
    (known alice) (known alice) MkSSymbol (truth alice p) MkSSymbol).

Definition off_owner (p : Symbol) := p = bob \/ p = carol.
Definition partial_empty (p : Symbol) (h : off_owner p)
    : At Empty_set alice p :=
  Mk_At (fun e =>
    False_rect Empty_set
      (match h with
       | or_introl b => fun z => @List.nil_cons N 1%N [] (eq_trans z b)
       | or_intror c => fun z => @List.nil_cons N 2%N [] (eq_trans z c)
       end e)).

(* These statements deliberately quantify over the implementation's public
   predicate, rather than defining expected results from its output. *)
Definition accepts_communicating
    (wf : forall (R : list Symbol) (M : Type -> Type)
      (A : Symbol -> Type), (forall p, Choreo M p (A p)) -> Prop) :=
  wf participants effect (fun p => At bool bob p) communicating.
Definition accepts_located
    (wf : forall (R : list Symbol) (M : Type -> Type)
      (A : Symbol -> Type), (forall p, Choreo M p (A p)) -> Prop) :=
  wf participants effect (fun p => At Empty_set alice p) located.
Definition rejects_receivers
    (wf : forall (R : list Symbol) (M : Type -> Type)
      (A : Symbol -> Type), (forall p, Choreo M p (A p)) -> Prop) :=
  ~ wf participants effect (fun p => At bool p p) two_receivers.
Definition rejects_absent
    (wf : forall (R : list Symbol) (M : Type -> Type)
      (A : Symbol -> Type), (forall p, Choreo M p (A p)) -> Prop) :=
  ~ wf [alice] effect (fun p => At bool bob p) communicating.
Definition rejects_codec
    (wf : forall (R : list Symbol) (M : Type -> Type)
      (A : Symbol -> Type), (forall p, Choreo M p (A p)) -> Prop) :=
  ~ wf participants effect (fun p => At bool bob p) wrong_codec.
Definition accepts_self
    (wf : forall (R : list Symbol) (M : Type -> Type)
      (A : Symbol -> Type), (forall p, Choreo M p (A p)) -> Prop) :=
  wf participants effect (fun p => At bool alice p) self_communication.

Definition empty_bind p : Choreo effect p (At bool p p) :=
  Bind (located p) (fun _ => two_receivers p).

Definition rejects_empty_bind
    (wf : forall (R : list Symbol) (M : Type -> Type)
      (A : Symbol -> Type), (forall p, Choreo M p (A p)) -> Prop) :=
  ~ wf participants effect (fun p => At bool p p) empty_bind.

Definition no_complete_empty_result : Prop :=
  (forall p, At Empty_set alice p) -> False.

Definition partial_empty_result_is_related
    (related : forall (S : Symbol -> Prop),
      (forall p, S p -> At Empty_set alice p) -> Prop) : Prop :=
  related off_owner partial_empty.
