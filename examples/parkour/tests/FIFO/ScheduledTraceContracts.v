From Stdlib Require Import Lists.List Strings.String.
From ITree Require Import ITree.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree.
From ParkourTheories Require Import Semantics.LocalEffects Semantics.SharedState
  Semantics.Runs Choreography.Occurrences Choreography.PendingDeliveries
  Choreography.RoleSteps Choreography.Execution Network.Mailboxes
  Network.Endpoints Network.Execution Projection.Matching.PrefixRelation.
Require Choreography.Choreo2 Control.Monad.Trans.Reader Choreography.Network.
Import ListNotations.

(* Independent slice-5 expectations, written before their inhabitants.
   A announces true to B and C, then sends false to C on Root; only B
   hears the announcement. C must still have its original source occurrence
   and its two outstanding Root FIFO entries, in announcement/data order.
   No existing fixture declarations or proof bodies supply these answers. *)
Definition wire_A : Symbol := GHC.Base.hs_string__ "wire-A".
Definition wire_B : Symbol := GHC.Base.hs_string__ "wire-B".
Definition wire_C : Symbol := GHC.Base.hs_string__ "wire-C".
Definition wire_roles : list Symbol := [wire_A; wire_B; wire_C].
Definition wire_effect (X : Type) := X.
Definition wire_event (_ : Type) := Empty_set.
Definition wire_model : local_model wire_effect wire_event Symbol (unit * unit)
  :=
  {| interpret_local := fun X (x : X) => Ret x;
     reply_local := fun _ _ _ _ _ _ => False |}.
Definition wire_stores : Symbol -> unit := fun _ => tt.

Definition wire_choice (p : Symbol) : Choreography.Choreo2.Choreo wire_effect p
  bool :=
  Perf (@Choreography.Choreo2.Cond wire_effect p bool wire_A bool
    show_bool read_bool (known wire_A) MkSSymbol
    (Choreography.Choreo2.Mk_At (fun _ => true))
    (fun b => Bind
      (Perf (@Choreography.Choreo2.Comm wire_effect p bool wire_A wire_C
        show_bool read_bool (known wire_A) (known wire_C) MkSSymbol
        (Choreography.Choreo2.Mk_At (fun _ => false)) MkSSymbol))
      (fun _ => Pure b))).

(* The projection outcome is the actual generated runner, not a hand projector.
  *)
Definition wire_projected (p : Symbol) : Choreography.Network.Network
  wire_effect bool :=
  Control.Monad.Trans.Reader.runReaderT
    (Choreography.Choreo2.unEpp
      (Choreography.Choreo2.epp (wire_choice p) (@MkSSymbol p)))
    Choreography.Network.Root.
Definition wire_source_initial :=
  @Choreography.Execution.initial wire_effect wire_event ((Symbol -> unit) *
    unit)
    (fun _ => bool) wire_choice (wire_stores, tt).
Definition wire_network_initial :=
  @Network.Execution.initialize wire_effect wire_event ((Symbol -> unit) * unit)
    wire_roles (fun _ => bool) wire_projected (wire_stores, tt).

(* Literal observations intentionally appear in each proposition. In particular,
   these are not obligations parameterized by a caller-selected predicate. *)
Definition wire_partial_delivery : Prop :=
  exists (s : @Choreography.Execution.configuration wire_effect wire_event
    ((Symbol -> unit) * unit) (fun _ => bool))
    (n : @Network.Execution.configuration wire_effect wire_event
      ((Symbol -> unit) * unit)),
    finite_run (Choreography.Execution.step (shared_model wire_model)
      wire_roles)
      wire_source_initial
      ([AnnounceAction bool [] wire_A true;
        SendAction bool [ChoiceBody; BindPrefix] wire_A wire_C false;
        HearAction bool [] wire_A wire_B true] :
          list (@RoleSteps.source_action wire_event ((Symbol -> unit) * unit)))
        s /\
    finite_run (Network.Execution.step (shared_model wire_model) wire_roles)
      wire_network_initial
      ([Announced wire_A Choreography.Network.Root (GHC.Base.hs_string__
        "True");
        Sent wire_A wire_C Choreography.Network.Root (GHC.Base.hs_string__
          "False");
        Received wire_A wire_B Choreography.Network.Root
          (GHC.Base.hs_string__ "True")] :
          list (@Endpoints.action wire_event ((Symbol -> unit) * unit))) n /\
    PrefixRelation.matches wire_model wire_stores tt wire_roles
      (fun _ => bool) wire_choice
      [AnnounceAction bool [] wire_A true;
       SendAction bool [ChoiceBody; BindPrefix] wire_A wire_C false;
       HearAction bool [] wire_A wire_B true] s
      [Announced wire_A Choreography.Network.Root (GHC.Base.hs_string__ "True");
       Sent wire_A wire_C Choreography.Network.Root (GHC.Base.hs_string__
         "False");
       Received wire_A wire_B Choreography.Network.Root (GHC.Base.hs_string__
         "True")] n /\
    Choreography.Execution.deliveries s =
      [Pending bool ChoiceDelivery [] wire_A wire_C true;
       Pending bool DataDelivery [ChoiceBody; BindPrefix] wire_A wire_C false]
         /\
    Choreography.Execution.positions s wire_C = Code [] (wire_choice wire_C) /\
    forall k, Network.Execution.mailboxes n k =
      if key_eq_dec k (wire_A, wire_C, Choreography.Network.Root)
      then [GHC.Base.hs_string__ "True"; GHC.Base.hs_string__ "False"] else [].

Definition wire_reject_invented_value : Prop :=
  forall (s : @Choreography.Execution.configuration wire_effect wire_event
    ((Symbol -> unit) * unit) (fun _ => bool))
    (n : @Network.Execution.configuration wire_effect wire_event
      ((Symbol -> unit) * unit)),
    ~ PrefixRelation.matches wire_model wire_stores tt wire_roles
      (fun _ => bool) wire_choice
      [AnnounceAction bool [] wire_A true;
       SendAction bool [ChoiceBody; BindPrefix] wire_A wire_C false;
       HearAction bool [] wire_A wire_B false] s
      [Announced wire_A Choreography.Network.Root (GHC.Base.hs_string__ "True");
       Sent wire_A wire_C Choreography.Network.Root (GHC.Base.hs_string__
         "False");
       Received wire_A wire_B Choreography.Network.Root (GHC.Base.hs_string__
         "True")] n.

Definition wire_reject_wrong_occurrence : Prop :=
  forall (s : @Choreography.Execution.configuration wire_effect wire_event
    ((Symbol -> unit) * unit) (fun _ => bool))
    (n : @Network.Execution.configuration wire_effect wire_event
      ((Symbol -> unit) * unit)),
    ~ PrefixRelation.matches wire_model wire_stores tt wire_roles
      (fun _ => bool) wire_choice
      [AnnounceAction bool [] wire_A true;
       SendAction bool [ChoiceBody; BindPrefix] wire_A wire_C false;
       HearAction bool [ChoiceBody] wire_A wire_B true] s
      [Announced wire_A Choreography.Network.Root (GHC.Base.hs_string__ "True");
       Sent wire_A wire_C Choreography.Network.Root (GHC.Base.hs_string__
         "False");
       Received wire_A wire_B Choreography.Network.Root (GHC.Base.hs_string__
         "True")] n.

Definition wire_reject_lost_pending : Prop :=
  forall (s : @Choreography.Execution.configuration wire_effect wire_event
    ((Symbol -> unit) * unit) (fun _ => bool))
    (n : @Network.Execution.configuration wire_effect wire_event
      ((Symbol -> unit) * unit)),
    Choreography.Execution.deliveries s = [] ->
    ~ PrefixRelation.matches wire_model wire_stores tt wire_roles
      (fun _ => bool) wire_choice
      [AnnounceAction bool [] wire_A true;
       SendAction bool [ChoiceBody; BindPrefix] wire_A wire_C false;
       HearAction bool [] wire_A wire_B true] s
      [Announced wire_A Choreography.Network.Root (GHC.Base.hs_string__ "True");
       Sent wire_A wire_C Choreography.Network.Root (GHC.Base.hs_string__
         "False");
       Received wire_A wire_B Choreography.Network.Root (GHC.Base.hs_string__
         "True")] n.

Definition wire_reject_swapped_fifo : Prop :=
  forall (s : @Choreography.Execution.configuration wire_effect wire_event
    ((Symbol -> unit) * unit) (fun _ => bool))
    (n : @Network.Execution.configuration wire_effect wire_event
      ((Symbol -> unit) * unit)),
    Network.Execution.mailboxes n (wire_A, wire_C, Choreography.Network.Root) =
      [GHC.Base.hs_string__ "False"; GHC.Base.hs_string__ "True"] ->
    ~ PrefixRelation.matches wire_model wire_stores tt wire_roles
      (fun _ => bool) wire_choice
      [AnnounceAction bool [] wire_A true;
       SendAction bool [ChoiceBody; BindPrefix] wire_A wire_C false;
       HearAction bool [] wire_A wire_B true] s
      [Announced wire_A Choreography.Network.Root (GHC.Base.hs_string__ "True");
       Sent wire_A wire_C Choreography.Network.Root (GHC.Base.hs_string__
         "False");
       Received wire_A wire_B Choreography.Network.Root (GHC.Base.hs_string__
         "True")] n.

(* A second, small input puts a self-communication in the function branch
   and a genuine communication in the argument branch. Completing both
   branches must emit exactly the argument branch's send and receive. *)
Definition wire_app_self (p : Symbol) :
    Choreography.Choreo2.Choreo wire_effect p (Choreography.Choreo2.At bool
      wire_B p) :=
  App
    (Bind
      (Perf (@Choreography.Choreo2.Comm wire_effect p bool wire_A wire_A
        show_bool read_bool (known wire_A) (known wire_A) MkSSymbol
        (Choreography.Choreo2.Mk_At (fun _ => true)) MkSSymbol))
      (fun _ => Pure (fun x => x)))
    (Perf (@Choreography.Choreo2.Comm wire_effect p bool wire_A wire_B
      show_bool read_bool (known wire_A) (known wire_B) MkSSymbol
      (Choreography.Choreo2.Mk_At (fun _ => false)) MkSSymbol)).

Definition wire_app_self_completed : Prop :=
  exists (s : @Choreography.Execution.configuration wire_effect wire_event
    ((Symbol -> unit) * unit) (fun p => Choreography.Choreo2.At bool wire_B p))
    (n : @Network.Execution.configuration wire_effect wire_event
      ((Symbol -> unit) * unit)),
    PrefixRelation.matches wire_model wire_stores tt [wire_A; wire_B]
      (fun p => Choreography.Choreo2.At bool wire_B p) wire_app_self
      [SendAction bool [AppArgument] wire_A wire_B false;
       ReceiveAction bool [AppArgument] wire_A wire_B false] s
      [Sent wire_A wire_B
         (Choreography.Network.Nest (Data.Either.Right tt)
           Choreography.Network.Root)
         (GHC.Base.hs_string__ "False");
       Received wire_A wire_B
         (Choreography.Network.Nest (Data.Either.Right tt)
           Choreography.Network.Root)
         (GHC.Base.hs_string__ "False")] n /\
    Choreography.Execution.final (shared_model wire_model) [wire_A; wire_B] s /\
    Network.Execution.final (shared_model wire_model) n /\
    Choreography.Execution.deliveries s = [] /\
    forall k, Network.Execution.mailboxes n k = [].

Definition wire_app_reject_root_tag : Prop :=
  forall (s : @Choreography.Execution.configuration wire_effect wire_event
    ((Symbol -> unit) * unit) (fun p => Choreography.Choreo2.At bool wire_B p))
    (n : @Network.Execution.configuration wire_effect wire_event
      ((Symbol -> unit) * unit)),
    ~ PrefixRelation.matches wire_model wire_stores tt [wire_A; wire_B]
      (fun p => Choreography.Choreo2.At bool wire_B p) wire_app_self
      [SendAction bool [AppArgument] wire_A wire_B false;
       ReceiveAction bool [AppArgument] wire_A wire_B false] s
      [Sent wire_A wire_B Choreography.Network.Root (GHC.Base.hs_string__
        "False");
       Received wire_A wire_B Choreography.Network.Root (GHC.Base.hs_string__
         "False")] n.
