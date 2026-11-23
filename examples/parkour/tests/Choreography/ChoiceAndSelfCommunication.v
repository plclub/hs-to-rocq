From Stdlib Require Import Lists.List.
From Stdlib Require NArith.BinNat.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree.
From ParkourTheories Require Import Semantics.LocalEffects
  Choreography.Occurrences Choreography.PendingDeliveries Choreography.RoleSteps
  Tests.Choreography.CommunicationOrder.
Require Choreography.Choreo2.
Import ListNotations.

(* Additional frozen contracts: the non-owner's actual self-Comm value is
   retained, not replaced by a merely pointwise equivalent empty function. *)
Definition self_other_contract : Prop :=
  forall M E Store (model : local_model M E Symbol Store)
    (X : Type) (p l : Symbol) (o : occurrence)
    (sh : Show X) (rd : Read X) (kl kd : KnownSymbol l)
    (sl sd : SSymbol l) (v : Choreography.Choreo2.At X l p),
    silent model (Choreography.Choreo2.At X l p)
      (Code o (Perf (@Choreography.Choreo2.Comm M p X l l sh rd kl kd sl v sd)))
      (Returned v).

Definition C : Symbol := [BinNat.N.of_nat 2].
Definition announce_at p : Choreography.Choreo2.Choreo
    (ITreeDefinition.itree request) p bool :=
  Perf (@Choreography.Choreo2.Cond (ITreeDefinition.itree request) p bool A bool
    show_bool read_bool (known A) MkSSymbol (located true) (fun b => Pure b)).
Definition choice_pending :=
  [Pending bool ChoiceDelivery [] A B true;
   Pending bool ChoiceDelivery [] A C true].

Definition one_role_announcement_contract : Prop :=
  role_step model [A] bool (Code [] (announce_at A)) 0 []
    (AnnounceAction bool [] A true)
    (Code (child [] ChoiceBody) (Pure true)) 0 [].
Definition multi_role_announcement_contract : Prop :=
  role_step model [A; B; C] bool (Code [] (announce_at A)) 0 []
    (AnnounceAction bool [] A true)
    (Code (child [] ChoiceBody) (Pure true)) 0 choice_pending.
Definition separate_hear_contract : Prop :=
  role_step model [A; B; C] bool (Code [] (announce_at B)) 0 choice_pending
    (HearAction bool [] A B true)
    (Code (child [] ChoiceBody) (Pure true)) 0
    [Pending bool ChoiceDelivery [] A C true].
