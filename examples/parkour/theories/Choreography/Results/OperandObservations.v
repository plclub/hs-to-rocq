From Stdlib Require Import Lists.List Logic.Eqdep_dec.
From ITree Require ITree.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Codec
  Parkour.Symbol.
From ParkourTheories.Choreography Require Import Occurrences PendingDeliveries
  RoleSteps WellFormedness Results.FiniteSelection.
Import ListNotations.

(* A produced operand retains its original type and Show dictionary. Neither
   receiving nor the proofs below compare equality proofs between Types. *)
Inductive operand : Type :=
| Operand : forall X, Show X -> X -> operand.

Definition operand_wire (a : operand) : GHC.Base.String :=
  match a with Operand X sh x => @show X sh x end.

Inductive payload_event : Type :=
| Produced : delivery_kind -> occurrence -> Symbol -> Symbol -> operand ->
  payload_event
| Consumed : delivery_kind -> occurrence -> Symbol -> Symbol ->
    GHC.Base.String -> payload_event.

(* A receive names an earlier production at exactly the same source occurrence,
   delivery kind, sender, and recipient. Bytes alone at a different occurrence
   cannot witness this predicate. This is a condition on a PAST history only. *)
Definition past_receive (past : list payload_event) kind o sender recipient wire
  :=
  exists a before between after,
    past = before ++ Produced kind o sender recipient a ::
      between ++ Consumed kind o sender recipient wire :: after /\
    wire = operand_wire a.

(* An original sender operand, not an equality of received typed values.
   This predicate must be obtained from the actual sender's syntax history.
   Its use below is explicit; it is NOT asserted for arbitrary cursor histories.
   *)
Definition original_operand (past : list payload_event) kind o sender recipient
    (a : operand) :=
  forall b, In (Produced kind o sender recipient b) past -> b = a.

Lemma past_receive_wire past kind o sender recipient wire a :
  past_receive past kind o sender recipient wire ->
  original_operand past kind o sender recipient a ->
  wire = operand_wire a.
Proof.
  intros (b & before & between & after & History & Bytes) Origin.
  rewrite History in Origin.
  assert (Recorded : In (Produced kind o sender recipient b)
    (before ++ Produced kind o sender recipient b ::
      between ++ Consumed kind o sender recipient wire :: after)).
  { apply in_or_app. right. now left. }
  specialize (Origin b Recorded).
  (* Observe the WHOLE package. No injection on its hidden Type is needed. *)
  exact (eq_trans Bytes (f_equal operand_wire Origin)).
Qed.

(* The event observer used at an actual sender focus. The original operand
   includes the dictionary carried by that constructor, not a replacement
   codec chosen by a proof. *)
Definition sender_operand {M p A} (c : Choreo M p A) : option operand :=
  match c with
  | Perf (@Comm _ _ X l _ sh _ _ _ _ input _) =>
    match List.list_eq_dec BinNat.N.eq_dec l p with
    | left e => Some (Operand X sh (unAt input e))
    | right _ => None
    end
  | Perf (@Cond _ _ X l _ sh _ _ _ input _) =>
    match List.list_eq_dec BinNat.N.eq_dec l p with
    | left e => Some (Operand X sh (unAt input e))
    | right _ => None
    end
  | _ => None
  end.

Definition recorded_sender {M p A} (past : list payload_event)
    kind o recipient (c : Choreo M p A) :=
  forall a, In (Produced kind o p recipient a) past ->
    sender_operand c = Some a.

Lemma comm_sender_operand M X l r sh rd kl kr sl input sr :
  sender_operand
    (Perf (@Comm M l X l r sh rd kl kr sl input sr)) =
    Some (Operand X sh (unAt input eq_refl)).
Proof.
  cbn [sender_operand].
  destruct (List.list_eq_dec BinNat.N.eq_dec l l) as [same|Different].
  - assert (same = eq_refl).
    { apply Eqdep_dec.UIP_dec. apply List.list_eq_dec. exact BinNat.N.eq_dec. }
    now subst same.
  - contradiction.
Qed.

Lemma comm_recorded_original M X l r sh rd kl kr sl input sr past o :
  recorded_sender past DataDelivery o r
    (Perf (@Comm M l X l r sh rd kl kr sl input sr)) ->
  original_operand past DataDelivery o l r
    (Operand X sh (unAt input eq_refl)).
Proof.
  intros Recorded a Member. specialize (Recorded a Member).
  rewrite comm_sender_operand in Recorded.
  now injection Recorded.
Qed.

Theorem received_original_value X (sh : Show X) (rd : Read X)
    past kind o sender recipient wire (sent got : X) :
  wire_law sh rd ->
  original_operand past kind o sender recipient (Operand X sh sent) ->
  past_receive past kind o sender recipient wire ->
  @read X rd wire = Some got ->
  got = sent.
Proof.
  intros Codec Origin Past Read.
  pose proof (past_receive_wire _ _ _ _ _ _ _ Past Origin) as Bytes.
  cbn in Bytes. rewrite Bytes, Codec in Read. now injection Read.
Qed.

(* Bind selects actual completed prefix values ONLY on the roles that entered
   the body. Entered can strictly contain the final completed-role set. *)
Lemma bind_entered_values A entered
    (PrefixTree : forall p, A p -> Prop) :
  (forall p, In p entered -> exists x, PrefixTree p x) ->
  exists x : values A (fun p => In p entered),
    forall p d, PrefixTree p (x p d).
Proof. apply select_returned. Qed.

Lemma partial_bind_results A B entered completed
    (v : values B (fun p => In p completed))
    (P : results A) (K : forall D, values A D -> results B)
    (PrefixTree : forall p, A p -> Prop) :
  (forall p, In p entered -> exists x, PrefixTree p x) ->
  (forall x, (forall p d, PrefixTree p (x p d)) ->
    P (fun p => In p entered) x) ->
  (forall x, (forall p d, PrefixTree p (x p d)) ->
    P (fun p => In p entered) x ->
    K (fun p => In p entered) x (fun p => In p completed) v) ->
  bind_results P K (fun p => In p completed) v.
Proof.
  intros Prefix PrefixSound BodySound.
  destruct (bind_entered_values A entered PrefixTree Prefix) as [x Tree].
  exists (fun p => In p entered), x.
  split; [now apply PrefixSound |].
  apply BodySound; [exact Tree | now apply PrefixSound].
Qed.

(* Scope of this module: these are the wire/value and finite extraction lemmas.
   A theorem extracting original_operand and the recursive tree premises above
   from every matched_prefix has NOT been proved here. In particular, arbitrary
   cursor histories are not claimed to establish structural's result relation.
   *)

(* These primitive certificates describe actual result observations. In the
   remote case the receive certificate contains decoding of the real past
   wire, not an assumed equation with the sender's typed value. *)
(* The explicit self certificate uses a role equality so that the input and
   output are compared at their common owner. *)
Definition comm_observed {X l r}
    (past : list payload_event) (o : occurrence)
    (rd : Read X) p (input : At X l p) (output : At X r p) : Prop :=
  (exists same : l = r,
    forall e : r = p, unAt output e = unAt input (eq_trans same e)) \/
  (l <> r /\
    forall e : r = p, exists wire,
      past_receive past DataDelivery o l r wire /\
      @read X rd wire = Some (unAt output e)).

Lemma comm_observed_value X l r S D
    (input : values (fun p => At X l p) S)
    (output : values (fun p => At X r p) D)
    (inc : includes D S)
    (sh : forall p, S p -> Show X)
    (rd : forall p, S p -> Read X) past o :
  (forall p (s t : S p), s = t) ->
  (forall (s : S l) (t : S r), l <> r -> wire_law (sh l s) (rd r t)) ->
  (forall (s : S l),
    original_operand past DataDelivery o l r
      (Operand X (sh l s) (unAt (input l s) eq_refl))) ->
  (forall p d,
    comm_observed past o (rd p (inc p d)) p
      (input p (inc p d)) (output p d)) ->
  comm_results input D output.
Proof.
  intros PI Codec Origin Played. split; [exact inc|].
  intros s d.
  destruct (Played r d) as [(same & Self) | (Different & Remote)].
  - destruct same. specialize (Self eq_refl).
    rewrite (PI l (inc l d) s) in Self. exact Self.
  - destruct (Remote eq_refl) as (wire & Past & Read).
    eapply received_original_value.
    + apply Codec; exact Different.
    + apply Origin.
    + exact Past.
    + exact Read.
Qed.

(* A choice receiver observes the same original owner operand by the same
   argument. In particular the choice equality is a conclusion, not a premise.
   *)
Lemma choice_observed_value X l p S
    (input : values (fun p => At X l p) S)
    (sh : forall p, S p -> Show X)
    (rd : forall p, S p -> Read X) (s : S l) (t : S p)
    past o wire (a : X) :
  p <> l ->
  wire_law (sh l s) (rd p t) ->
  original_operand past ChoiceDelivery o l p
    (Operand X (sh l s) (unAt (input l s) eq_refl)) ->
  past_receive past ChoiceDelivery o l p wire ->
  @read X (rd p t) wire = Some a ->
  a = unAt (input l s) eq_refl.
Proof.
  intros _ Codec Origin Past Read.
  eapply received_original_value; eassumption.
Qed.

(* Finite extraction from the actual per-role subtrees. In App and Bind these
   predicates can retain arbitrarily many local actions and past receives. *)
Lemma app_completed_values A B D
    (v : values B (fun p => In p D))
    (F : forall p, (A p -> B p) -> Prop)
    (X : forall p, A p -> Prop) :
  (forall p (d e : In p D), d = e) ->
  (forall p d, exists f x,
    F p f /\ X p x /\ v p d = f x) ->
  exists (f : values (fun p => A p -> B p) (fun p => In p D))
         (x : values A (fun p => In p D)),
    (forall p d, F p (f p d) /\ X p (x p d) /\
      v p d = f p d (x p d)).
Proof.
  intros PI Trees.
  destruct (@select_returned (fun p => ((A p -> B p) * A p)%type)
    (fun p pair => F p (fst pair) /\ X p (snd pair) /\
      forall d : In p D, v p d = fst pair (snd pair)) D)
    as [pairs Valid].
  - intros p d.
    destruct (Trees p d) as (f & x & Tf & Tx & Eq).
    exists (f,x). cbn. repeat split; try assumption.
    intro e.
    (* Membership evidence is not silently identified: the actual result family
       must be proof-index independent if duplicate witnesses can occur. *)
    now rewrite <- (PI p d e).
  - exists (fun p d => fst (pairs p d)), (fun p d => snd (pairs p d)).
    intros p d. destruct (Valid p d) as [Tf [Tx Eq]].
    repeat split; auto.
Qed.

Lemma partial_app_results A B D
    (v : values B (fun p => In p D))
    (F : results (fun p => A p -> B p)) (X : results A)
    (FunctionTree : forall p, (A p -> B p) -> Prop)
    (ArgumentTree : forall p, A p -> Prop) :
  (forall p (d e : In p D), d = e) ->
  (forall p d, exists f x,
    FunctionTree p f /\ ArgumentTree p x /\ v p d = f x) ->
  (forall f, (forall p d, FunctionTree p (f p d)) ->
    F (fun p => In p D) f) ->
  (forall x, (forall p d, ArgumentTree p (x p d)) ->
    X (fun p => In p D) x) ->
  app_results F X (fun p => In p D) v.
Proof.
  intros PI Trees FunctionSound ArgumentSound.
  destruct (app_completed_values A B D v FunctionTree ArgumentTree PI Trees)
    as (f & x & Valid).
  exists f,x. repeat split.
  - apply FunctionSound. intros p d. exact (proj1 (Valid p d)).
  - apply ArgumentSound. intros p d. exact (proj1 (proj2 (Valid p d))).
  - intros p d. exact (proj2 (proj2 (Valid p d))).
Qed.

Section ActualLocalResults.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Symbol Store.
Variable configured : list Symbol.

(* Finite actual paths include silent bookkeeping as well as visible events.
   Stores and queues are threaded through every visible edge. *)
#[universes(template)]
Inductive played_path {p A} :
    @cursor M E p A -> Store -> list pending ->
    list (@source_action E Store) ->
    cursor p A -> Store -> list pending -> Prop :=
| PlayedDone t s q : played_path t s q [] t s q
| PlayedSilent t u v s q tr s' q' :
    silent model A t u ->
    played_path u s q tr v s' q' ->
    played_path t s q tr v s' q'
| PlayedAction t u v s q a s1 q1 tr s' q' :
    role_step model configured A t s q a u s1 q1 ->
    played_path u s1 q1 tr v s' q' ->
    played_path t s q (a :: tr) v s' q'.

#[universes(template)]
Inductive local_play {p X} :
    ITreeDefinition.itree E X -> Store ->
    list (LocalEffects.local_event E Symbol Store) ->
    ITreeDefinition.itree E X -> Store -> Prop :=
| LocalPlayedDone t s : local_play t s [] t s
| LocalPlayedStep t s a u s1 tr v s' :
    LocalEffects.local_step (LocalEffects.reply_local _ _ _ _ model)
      p t s a u s1 ->
    local_play u s1 tr v s' ->
    local_play t s (a :: tr) v s'.

Lemma local_play_cursor p X o t s tr u s' q (x : X) :
  @local_play p X t s tr u s' ->
  LocalEffects.local_return u x ->
  played_path (Local (p := p) o t) s q
    (map (fun a => LocalAction o a) tr)
    (Returned (here_at x)) s' q.
Proof.
  intros Run Return. induction Run; cbn.
  - eapply PlayedSilent.
    + apply SLocalReturn. exact Return.
    + constructor.
  - eapply PlayedAction.
    + apply RLocal. exact H.
    + apply IHRun. exact Return.
Qed.

Theorem owner_locally_actual_result p X o ks ss
    (f : Unwrap p p -> M X) s tr u s' q x :
  @local_play p X
    (LocalEffects.interpret_local _ _ _ _ model X
      (f (RoleSteps.owner_unwrap p))) s tr u s' ->
  LocalEffects.local_return u x ->
  played_path (Code o (Perf (@Locally M p X p ks ss f))) s q
    (map (fun a => LocalAction o a) tr)
    (Returned (here_at x)) s' q.
Proof.
  intros Run Return. eapply PlayedSilent.
  - apply SLocalStart.
  - eapply local_play_cursor; eassumption.
Qed.

Lemma receive_actual_result p X l o sh rd kl kd sl input sd
    (different : l <> p) (s : Store) q q' x :
  take_at_occurrence DataDelivery o l p x q q' ->
  played_path
    (Code o (Perf (@Comm M p X l p sh rd kl kd sl input sd))) s q
    [ReceiveAction X o l p x] (Returned (here_at x)) s q'.
Proof.
  intro Take. eapply PlayedAction.
  - eapply RReceive; eassumption.
  - constructor.
Qed.

End ActualLocalResults.
