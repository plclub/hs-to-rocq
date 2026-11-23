From ITree Require ITree.
From Stdlib Require Import Lists.List Strings.String.
From ParkourTheories Require Import Semantics.LocalEffects Network.Mailboxes
  Network.Endpoints Network.Execution.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree
  Choreography.Network Choreography.Choreo2.
Require Control.Monad.Trans.Reader.
Import ListNotations.

(* Exactly counterexample/Family.v's family, instantiated against the repaired
   generated library. The frozen counterexample remains a separate build. *)
Module Repair.
Definition A : Symbol := GHC.Base.hs_string__ "A".
Definition B : Symbol := GHC.Base.hs_string__ "B".
Definition Id (X : Type) := X.
Definition choice (p : Symbol) : At bool A p := Mk_At (fun _ => true).
Definition payload (p : Symbol) : At unit A p := Mk_At (fun _ => tt).
Definition branch (p : Symbol) (_ : bool) : Choreo Id p (At unit B p) :=
  op_z7eUzg__ (payload p) (@MkSSymbol B).
Definition program (p : Symbol) : Choreo Id p (At unit B p) :=
  cond (choice p) (branch p).

Inductive no_event : Type -> Type := .
Definition pure_model : local_model Id no_event role unit :=
  {| interpret_local := fun X x => ITreeDefinition.Ret x;
     reply_local := fun X _ (_ : no_event X) _ _ _ => False |}.
Definition endpoint_tree p :=
  Control.Monad.Trans.Reader.runReaderT
    (unEpp (epp (program p) (@MkSSymbol p))) Root.
Definition owner : @control Id no_event (At unit B A) :=
  load (endpoint_tree A).
Definition peer : @control Id no_event (At unit B B) :=
  load (endpoint_tree B).
Definition config (o : @control Id no_event (At unit B A))
    (b : @control Id no_event (At unit B B)) (q : queues)
    : @configuration Id no_event unit :=
  {| endpoints := [Endpoint _ A o; Endpoint _ B b];
     mailboxes := q; shared_store := tt |}.
Definition initial := config owner peer empty_queues.
Definition truth := GHC.Base.hs_string__ "True".
Definition unit_wire := GHC.Base.hs_string__ "()".

(* Both sends run before either receive. The intermediate FIFO therefore
   witnesses the actual order, not just a successful interleaving. *)
Lemma repaired_exact_family :
  exists n1 n2 n3 n4,
    Network.Execution.step pure_model [A; B] initial (Announced A Root truth) n1
      /\
    Network.Execution.step pure_model [A; B] n1 (Sent A B Root unit_wire) n2 /\
    mailboxes n2 (A,B,Root) = [truth; unit_wire] /\
    Network.Execution.step pure_model [A; B] n2 (Received A B Root truth) n3 /\
    Network.Execution.step pure_model [A; B] n3 (Received A B Root unit_wire) n4
      /\
    Network.Execution.final pure_model n4.
Proof.
  unfold initial, config, owner, peer, endpoint_tree, program, branch,
    choice, payload.
  cbn.
  do 4 eexists. split.
  - eapply Schedule with (pre := []) (post := [_]).
    apply StepBind. eapply StepContinue.
    + apply ReturnPure.
    + apply StepBCast.
  - split.
    + eapply Schedule with (pre := []) (post := [_]).
      eapply StepContinue.
      * apply ReturnPure.
      * eapply StepContinue.
        -- apply ReturnPure.
        -- apply StepLeft. apply StepBind. apply StepSend.
    + split.
      * reflexivity.
      * split.
        -- eapply Schedule with (pre := [_]) (post := []).
           apply StepBind. eapply StepContinue.
           ++ apply ReturnPure.
           ++ eapply StepRecv with (x := true); reflexivity.
        -- split.
           ++ eapply Schedule with (pre := [_]) (post := []).
              eapply StepContinue.
              ** apply ReturnPure.
              ** eapply StepContinue.
                 --- apply ReturnPure.
                 --- apply StepBind.
                     eapply StepRecv with (x := tt); reflexivity.
           ++ split.
              ** constructor.
                 --- eexists. eapply ReturnApp.
                     +++ eapply ReturnBind; apply ReturnPure.
                     +++ apply ReturnPure.
                 --- constructor.
                     +++ eexists. eapply ReturnBind; apply ReturnPure.
                     +++ constructor.
              ** intro k. cbn.
                 unfold enqueue, replace_queue, empty_queues.
                 repeat destruct (key_eq_dec _ _); reflexivity.
Qed.

Corollary repaired_exact_run :
  exists final,
    Network.Execution.run pure_model [A; B] initial
      [Announced A Root truth; Sent A B Root unit_wire;
       Received A B Root truth; Received A B Root unit_wire] final /\
    Network.Execution.final pure_model final.
Proof.
  destruct repaired_exact_family as
    [n1 [n2 [n3 [n4 [H1 [H2 [Hfifo [H3 [H4 Hfinal]]]]]]]]].
  exists n4. split; [| exact Hfinal].
  eapply RunCons; [exact H1 |].
  eapply RunCons; [exact H2 |].
  eapply RunCons; [exact H3 |].
  eapply RunCons; [exact H4 |].
  apply RunNil.
Qed.

Example decode_truth : @read bool read_bool truth = Some true.
Proof. reflexivity. Qed.
Example decode_unit : @read unit read_unit unit_wire = Some tt.
Proof. reflexivity. Qed.
End Repair.
