From Stdlib Require Import Lists.List.
From Stdlib Require NArith.BinNat.
From ITree Require Import ITree.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree DeadlockLocal
  DeadlockSource.
Require Choreography.Choreo2.
Local Notation At := Choreography.Choreo2.At.
Local Notation Mk_At := Choreography.Choreo2.Mk_At.
Local Notation unAt := Choreography.Choreo2.unAt.
Local Notation Choreo := Choreography.Choreo2.Choreo.
Local Notation Locally := Choreography.Choreo2.Locally.
Local Notation Comm := Choreography.Choreo2.Comm.
Import ListNotations.

Definition A : Symbol := [].
Definition B : Symbol := [BinNat.N.of_nat 1].
Inductive request : Type -> Type := Wait : request bool | Act : request bool.
Definition wait : itree request bool := Vis Wait (fun x => Ret x).
Definition act : itree request bool := Vis Act (fun x => Ret x).
Definition reply X (_ : Symbol) (e : request X) (s : nat) (x : X) (s' : nat) :=
  match e in request T return T -> Prop with
  | Wait => fun _ => False
  | Act => fun b => b = true /\ s' = s
  end x.
Definition model : local_model (itree request) request Symbol nat :=
  {| interpret_local := fun _ t => t; reply_local := reply |}.
Definition roles := [A; B].
Definition show_bool : Show bool := fun b => if b then [BinNat.N.of_nat 1] else
  [].
Definition read_bool : Read bool := fun s =>
  match s with
  | [] => Some false
  | [BinNums.Npos BinNums.xH] => Some true
  | _ => None
  end.
Definition located {X l p} (x : X) : At X l p := Mk_At (fun _ => x).
Definition local_at p l (t : itree request bool) : Choreo (itree request) p (At
  bool l p) :=
  Perf (@Locally (itree request) p bool l (known l) MkSSymbol (fun _ => t)).
Definition comm p l d (v : At bool l p) : Choreo (itree request) p (At bool d p)
  :=
  Perf (@Comm (itree request) p bool l d show_bool read_bool
    (known l) (known d) MkSSymbol v MkSSymbol).

Definition independent p : Choreo (itree request) p (At bool B p) :=
  Bind (local_at p A wait) (fun _ => local_at p B act).
Definition receive_then_act : Choreo (itree request) B (At bool B B) :=
  Bind (comm B A B (located true)) (fun _ => local_at B B act).
Definition forward : Choreo (itree request) B (At bool A B) :=
  Bind (comm B A B (located true)) (fun x => comm B B A x).
Definition two_sends : Choreo (itree request) A (At bool B A) :=
  Bind (comm A A B (located true)) (fun _ => comm A A B (located false)).
Definition parallel : Choreo (itree request) B bool :=
  App (Bind (local_at B B wait) (fun _ => Pure (fun x : At bool B B => unAt x
    eq_refl)))
      (local_at B B act).
Definition first_path := child [] BindPrefix.
Definition second_path := child [] BindBody.
Definition two_pending :=
  [Pending bool DataDelivery first_path A B true;
   Pending bool DataDelivery second_path A B false].

Definition independent_contract : Prop :=
  exists t', role_step model roles (At bool B B) (Code [] (independent B)) 0 []
    (LocalAction (child [] BindBody) (LocalEvent B Act 0 true 0))
    t' 0 [].
Definition parallel_contract : Prop :=
  exists t', role_step model roles bool (Code [] parallel) 0 []
    (LocalAction (child [] AppArgument) (LocalEvent B Act 0 true 0))
    t' 0 [].
Definition receive_blocks_contract : Prop :=
  forall a t' s' q',
    ~ role_step model roles (At bool B B) (Code [] receive_then_act) 0 [] a t'
      s' q'.
Definition forward_blocks_contract : Prop :=
  forall a t' s' q',
    ~ role_step model roles (At bool A B) (Code [] forward) 0 [] a t' s' q'.
Definition sends_contract : Prop :=
  exists t1 t2,
    role_step model roles (At bool B A) (Code [] two_sends) 0 []
      (SendAction bool first_path A B true) t1 0
      [Pending bool DataDelivery first_path A B true] /\
    role_step model roles (At bool B A) t1 0
      [Pending bool DataDelivery first_path A B true]
      (SendAction bool second_path A B false) t2 0 two_pending.
Definition fifo_contract : Prop :=
  forall q', ~ take_pending DataDelivery second_path A B false two_pending q'.
