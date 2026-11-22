(* Independent concrete slice-6 expectations. This file imports no case proofs.
   The source, roles, payload, trace and mutations are fixed here. *)
From Stdlib Require Import Lists.List Strings.String.
From Stdlib Require NArith.BinNat.
From ITree Require ITree.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree
  Choreography.Choreo2 Choreography.Network
  DeadlockLocal DeadlockRuns DeadlockSource DeadlockNetwork
  DeadlockWellFormed DeadlockProjectionExpect.
Import ListNotations.

Module MutationExpect.
Definition A : Symbol := [BinNat.N.of_nat 0].
Definition B : Symbol := [BinNat.N.of_nat 1].
Definition Id (X : Type) := X.
Inductive no_event : Type -> Type := .
Definition model : local_model Id no_event Symbol unit :=
  {| interpret_local := fun X x => ITreeDefinition.Ret x;
     reply_local := fun X _ (_ : no_event X) _ _ _ => False |}.
Definition payload p : At unit A p := Mk_At (fun _ => tt).
Definition family p : Choreo Id p (At unit B p) :=
  Perf (@Comm Id p unit A B show_unit read_unit
    (known A) (known B) MkSSymbol (payload p) MkSSymbol).
Definition source_initial := DeadlockSource.initial
  (E := no_event) family tt.
Definition bytes := GHC.Base.hs_string__ "()".
Definition endpoint p := runner (family p) Root.
Definition initial := initialize (E := no_event) [A;B] endpoint tt.
Definition wrong_sid := Nest (Data.Either.Left tt) Root.
Definition wrong_initial : @DeadlockNetwork.configuration Id no_event unit :=
  {| endpoints :=
       [Endpoint _ A (load (runner (family A) Root));
        Endpoint _ B (load (runner (family B) wrong_sid))];
     mailboxes := empty_queues; DeadlockNetwork.shared_store := tt |}.
Definition omitted_sender : @DeadlockNetwork.configuration Id no_event unit :=
  {| endpoints := [Endpoint _ B (load (runner (family B) Root))];
     mailboxes := empty_queues; DeadlockNetwork.shared_store := tt |}.

Definition wf_contract : Prop := well_formed [A;B] Id _ family.
Definition source_df_contract : Prop :=
  DF (cstep model [A;B]) (cfinal model [A;B]) source_initial.
Definition correct_contract : Prop :=
  exists final, run model [A;B] initial
    [Sent A B Root bytes; Received A B Root bytes] final /\
    nfinal model final.
Definition wrong_contract : Prop :=
  exists residual,
    run model [A;B] wrong_initial [Sent A B Root bytes] residual /\
    mailboxes residual (A,B,Root) = [bytes] /\
    mailboxes residual (A,B,wrong_sid) = [] /\
    stuck (nstep model [A;B]) (nfinal model) residual.
Definition omitted_contract : Prop :=
  run model [B] omitted_sender [] omitted_sender /\
  stuck (nstep model [B]) (nfinal model) omitted_sender.
Definition no_explanation_contract : Prop :=
  forall trace residual,
    crun model [A;B] source_initial trace residual ->
    ~ stuck (cstep model [A;B]) (cfinal model [A;B]) residual.
Definition wrong_progress_contract : Prop :=
  forall target,
    run model [A;B] wrong_initial [Sent A B Root bytes] target ->
    stuck (nstep model [A;B]) (nfinal model) target ->
    forall trace source,
      crun model [A;B] source_initial trace source ->
      ~ (ready (cstep model [A;B]) (cfinal model [A;B]) source ->
         ready (nstep model [A;B]) (nfinal model) target).
Definition omitted_progress_contract : Prop :=
  forall trace source,
    crun model [A;B] source_initial trace source ->
    ~ (ready (cstep model [A;B]) (cfinal model [A;B]) source ->
       ready (nstep model [B]) (nfinal model) omitted_sender).
End MutationExpect.
