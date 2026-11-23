From Stdlib Require Import Lists.List.
Require Import DeadlockSource DeadlockNetwork DeadlockMatch DeadlockMessages
  DeadlockCutSafety DeadlockStaticOrigin DeadlockEnteredOrigin DeadlockRootOrigin
  DeadlockWellFormed DeadlockLocal DeadlockState DeadlockPlayedValues DeadlockPast
  DeadlockCoherence DeadlockOrder DeadlockChoiceOrigin DeadlockStaticPaths DeadlockPartialValues
  Choreography.Choreo2 Control.Monad.Tree Parkour.Codec Parkour.Symbol.
Import ListNotations.
Local Arguments positions {M E Store A} _ _.

Section Selected.
Context {M E Store Input} (model : local_model M E role (Store * Input))
  (stores : role -> Store) (input : Input) (R : list role) (A : role -> Type)
  (c : forall p, Choreo M p (A p)).
Local Notation sm := (shared_model model).
Local Notation prefix := (matched_prefix model stores input R A c).
Variable X : Type.
Variable l : role.
Variables (sh : forall p : role, Show X) (rd : forall p : role, Read X)
  (arg : forall p, At X l p) (k : forall p, X -> Choreo M p (A p)).
Let chosen := unAt (arg l) eq_refl.
Let body p := k p chosen.
Hypothesis Shape : forall p, In p R ->
  c p = Perf (@Cond M p X l (A p) (sh p) (rd p) (known l) MkSSymbol (arg p) (k p)).

(* A role can enter while another is still at the condition. The history
   starts at that role's selected body; no simultaneous entry is required. *)
Definition entered_body_or_waiting (s : @DeadlockSource.configuration M E ((role -> Store) * Input) A) p :=
  positions s p = Code [] (c p) \/
  exists tr, cursor_history sm R (Code [ChoiceBody] (body p)) tr (positions s p).

Hypothesis Entry : forall tc s tn n gs, prefix tc s tn n gs ->
  forall p, In p R -> entered_body_or_waiting s p.

Lemma select_inner_code tc s tn n gs p Y (C : @cursor_context M E p Y (A p))
    (code : Choreo M p Y) path :
  prefix tc s tn n gs -> In p R -> static_path path ->
  silent_prefix sm (positions s p)
    (plug C (Code (ChoiceBody :: path) code)) ->
  descend path (body p) = Some (existT _ Y code).
Proof.
  intros P InP Static Sil.
  destruct (Entry _ _ _ _ _ P p InP) as [Waiting|[tr Hist]].
  - assert (Wait : silent_prefix sm (Code [] (c p)) (plug C (Code (ChoiceBody :: path) code))).
    { rewrite <- Waiting. exact Sil. }
    rewrite (Shape p InP) in Wait.
    pose proof (before_choice_no_child sm p X l (A p) (sh p) (rd p) (known l)
      MkSSymbol (arg p) (k p) [] Y C (ChoiceBody :: path) code Wait). discriminate.
  - eapply entered_focus_original; [exact Hist|exact Sil|exact Static].
Qed.

Lemma selected_inner_packet tc s tn n gs past Y jk path sender recipient (v : Y) dict :
  payload_history model stores input R A c tc s tn n gs past ->
  In (Message Y jk (ChoiceBody :: path) sender recipient v dict) gs ->
  static_path path ->
  output (descend path (body sender)) (ChoiceBody :: path) recipient =
    Some (Message Y jk (ChoiceBody :: path) sender recipient v dict).
Proof.
  intros H InG Static.
  destruct (actual_production_focus model stores input R A c _ _ _ _ _
    (history_production model stores input R A c _ _ _ _ _ _ H jk (ChoiceBody :: path)
      sender recipient (Operand Y dict v)
      (proj1 (history_past_ok model stores input R A c _ _ _ _ _ _ H) _ InG)))
    as (tc0 & s0 & tn0 & n0 & gs0 & a & s1 & na & n1 & gs1 & ev & who & P & Pair & Hin & Focus).
  destruct (production_focus_sender _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Focus) as [Eq _].
  subst who. destruct Focus as (B & C & before & after & Sil & Prim & End & Site).
  pose proof (focus_packet _ _ _ _ _ Site) as Packet.
  destruct (sender_site_operand _ _ _ _ _ _ _ _ _ Site) as [_ [code [-> _]]].
  rewrite (select_inner_code _ _ _ _ _ _ _ C code path P Hin Static Sil).
  exact Packet.
Qed.

Theorem selected_body_originals tc s tn n gs p :
  well_formed R M A body -> prefix tc s tn n gs -> In p R ->
  forall Y kind path sender reader, static_path path ->
  receive_site sm p (A p) (positions s p) Y kind (ChoiceBody :: path) sender reader ->
  exists (v : Y) (dict : Show Y),
    (forall g, In g gs ->
      message_key g = (sender,p,session_at (ChoiceBody :: path) Choreography.Network.Root) ->
      message_path g = ChoiceBody :: path -> g = Message Y kind (ChoiceBody :: path) sender p v dict) /\
    wire_law dict reader.
Proof.
  intros [_ [Q WF]] P InP Y kind path sender reader Static (B & C & focus & Sil & Site).
  destruct (focus_reader _ _ _ _ _ _ Site) as (code & -> & Reads).
  pose proof (select_inner_code _ _ _ _ _ _ _ C code path P InP Static Sil) as Receiver.
  pose proof (family_static_reader WF path (ChoiceBody :: path) p InP (fun r h => h)
    (fun r _ => output (descend path (body r)) (ChoiceBody :: path) p) (fun _ _ => eq_refl)) as Reader.
  cbn beta in Reader. rewrite Receiver in Reader.
  destruct (Reads _ Reader) as (v & dict & InS & Orig & Law).
  exists v, dict. split; [|exact Law].
  intros [T jk b from dest x sw] InG Key Path.
  cbn [message_key message_path] in Key, Path. subst b; injection Key as -> ->.
  destruct (matched_payload_history model stores input R A c _ _ _ _ _ P) as [past Hist].
  pose proof (selected_inner_packet _ _ _ _ _ _ T jk path sender p x sw Hist InG Static).
  congruence.
Qed.
End Selected.

Definition root_condition {M p B} (code : Choreo M p B) : Prop :=
  match code with Perf (Cond _ _ _) => True | _ => False end.

Lemma invert_root_condition R M S A family Q :
  structural R M S A family Q ->
  forall p mem, root_condition (family p mem) ->
  exists X l (sh : forall r, S r -> Show X) (rd : forall r, S r -> Read X)
    (arg : forall r, S r -> At X l r)
    (k : forall r, S r -> X -> Choreo M r (A r)) K,
    In l R /\
    (forall r (ss : S l) (sr : S r), r <> l -> wire_law (sh l ss) (rd r sr)) /\
    (forall r s, family r s = Perf (@Cond M r X l (A r)
      (sh r s) (rd r s) (known l) MkSSymbol (arg r s) (k r s))) /\
    (forall x, structural R M S A (fun r s => k r s x) (K x)).
Proof.
  destruct 1; intros peer mem Root;
    match goal with Shape : forall p s, ?prog p s = _ |- _ => rewrite (Shape peer mem) in Root end;
    cbn [root_condition] in Root; try contradiction.
  exists X,l,sh,rd,x,k,K. auto.
Qed.

Lemma structural_pointwise R M S A c Q :
  structural R M S A c Q ->
  forall d, (forall p s, d p s = c p s) -> structural R M S A d Q.
Proof.
  destruct 1; intros d Eq;
    econstructor; try eassumption; intros; rewrite Eq; auto.
Qed.

(* Discharge the asynchronous entry premise from actual matched histories.
   The body certificate and the cross-role codec law are exactly the two
   child premises of WFCond, specialized at its owner's concrete argument. *)
Theorem choice_body_originals {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c
    X l (sh : forall p : role, Show X) (rd : forall p : role, Read X)
    (arg : forall p, At X l p) (k : forall p, X -> Choreo M p (A p))
    tc s tn n gs p :
  In l R ->
  (forall r, In r R -> c r = Perf (@Cond M r X l (A r) (sh r) (rd r)
    (known l) MkSSymbol (arg r) (k r))) ->
  (forall r, In r R -> l <> r -> wire_law (sh l) (rd r)) ->
  well_formed R M A (fun r => k r (unAt (arg l) eq_refl)) ->
  matched_prefix model stores input R A c tc s tn n gs -> In p R ->
  forall Y kind path sender reader, static_path path ->
  receive_site (shared_model model) p (A p) (positions s p) Y kind (ChoiceBody :: path) sender reader ->
  exists (v : Y) (dict : Show Y),
    (forall g, In g gs ->
      message_key g = (sender,p,session_at (ChoiceBody :: path) Choreography.Network.Root) ->
      message_path g = ChoiceBody :: path -> g = Message Y kind (ChoiceBody :: path) sender p v dict) /\
    wire_law dict reader.
Proof.
  intros Owner Shape Law Body Run Member.
  refine (selected_body_originals model stores input R A c X l sh rd arg k Shape
    _ tc s tn n gs p Body Run Member).
  intros tc0 s0 tn0 n0 gs0 P who InR.
  destruct (matched_payload_history model stores input R A c _ _ _ _ _ P) as [past Hist].
  destruct (root_choice_actor_invariant model stores input R A c X l sh rd arg k
    _ _ _ _ _ _ Owner Shape Law Hist who InR) as [[_ Waiting]|Started].
  - left; exact Waiting.
  - right. destruct Started as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
      suffix & _ & _ & _ & _ & _ & _ & H). now exists suffix.
Qed.

Definition on_roster {F : role -> Type} R (f : forall r, In r R -> F r)
    (outside : forall r, F r) r :=
  match in_dec role_eq_dec r R with left s => f r s | right _ => outside r end.

Lemma on_roster_member {F} R f outside r member :
  NoDup R -> @on_roster F R f outside r = f r member.
Proof.
  intro ND. unfold on_roster. destruct (in_dec role_eq_dec r R) as [s|Ne]; [|contradiction].
  now rewrite (roster_member_unique R ND r s member).
Qed.

Theorem source_originals_choice_static {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c tc s tn n gs :
  well_formed R M A c -> matched_prefix model stores input R A c tc s tn n gs ->
  forall p, In p R -> forall Y kind path sender reader, static_path path ->
  receive_site (shared_model model) p (A p) (positions s p) Y kind (ChoiceBody :: path) sender reader ->
  exists (v : Y) (dict : Show Y),
    (forall g, In g gs ->
      message_key g = (sender,p,session_at (ChoiceBody :: path) Choreography.Network.Root) ->
      message_path g = ChoiceBody :: path -> g = Message Y kind (ChoiceBody :: path) sender p v dict) /\
    wire_law dict reader.
Proof.
  intros [ND [Q WF]] Run p Member Y kind path sender reader Static Site.
  assert (Root : root_condition (c p)).
  { destruct Site as (B & C & focus & Sil & F).
    assert (Hit : exists code, focus = Code (ChoiceBody :: path) code /\ possible_path [] code)
      by (destruct F; eexists; split; [reflexivity|exact I|reflexivity|exact I]).
    destruct Hit as (code & -> & Hit).
    assert (Possible : possible_path (ChoiceBody :: path) (c p)).
    { eapply reached_action_path; [|exact Sil|exact Hit].
      eapply run_follows; [exact (prefix_source_run model stores input R A c _ _ _ _ _ Run)|].
      intros tail T; exact T. }
    destruct (c p); cbn [root_condition possible_path] in *; try contradiction.
    match goal with e : ChoreoSig _ _ _ |- _ => destruct e; exact Possible end. }
  destruct (invert_root_condition _ _ _ _ _ _ WF p Member Root)
    as (X & l & sh & rd & arg & k & K & Owner & Law & Shape & Branch).
  pose (v0 := unAt (arg l Owner) eq_refl).
  pose (shows := on_roster R sh (fun _ => sh l Owner)).
  pose (reads := on_roster R rd (fun _ => rd l Owner)).
  pose (args := on_roster R arg (fun r => @Mk_At X l r (fun _ => v0))).
  pose (cont := on_roster R k (fun r _ => c r)).
  pose proof (on_roster_member R arg (fun r => @Mk_At X l r (fun _ => v0)) l Owner ND) as Base.
  change (args l = arg l Owner) in Base.
  eapply (choice_body_originals model stores input R A c X l shows reads args cont
    _ _ _ _ _ p); try eassumption.
  - intros r h. unfold shows,reads,args,cont. rewrite !(on_roster_member _ _ _ _ h ND).
    exact (Shape r h).
  - intros r h Ne. unfold shows,reads. rewrite (on_roster_member _ _ _ _ Owner ND),
      (on_roster_member _ _ _ _ h ND). apply Law. congruence.
  - split; [exact ND|]. exists (K v0). eapply structural_pointwise; [exact (Branch v0)|].
    intros r h. rewrite Base. unfold cont. rewrite (on_roster_member _ _ _ _ h ND). reflexivity.
Qed.
