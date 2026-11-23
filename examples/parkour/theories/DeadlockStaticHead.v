From Stdlib Require Import Lists.List.
Require Import DeadlockSource DeadlockNetwork DeadlockMessages DeadlockFrontiers
  DeadlockFirstSend DeadlockRootHead DeadlockRootOrigin DeadlockStaticOrigin DeadlockStaticPaths
  DeadlockWellFormed DeadlockMatch DeadlockPast DeadlockOrder DeadlockLocal
  DeadlockState DeadlockHead DeadlockCutSafety DeadlockStaticBarrier Choreography.Choreo2 Control.Monad.Tree Parkour.Symbol.
Import ListNotations.

Lemma output_is_sender {M sender} R p pack X kind o (v : X) sh :
  In p R -> sender <> p ->
  @output M sender pack o p = Some (Message X kind o sender p v sh) ->
  match pack with Some (existT _ _ code) => sender_ready R code p | None => False end.
Proof.
  intros Member Ne. destruct pack as [[A code]|]; [|discriminate].
  destruct code as [A sig| | |]; cbn [output outgoing sender_ready]; try discriminate.
  destruct sig; cbn [output outgoing sender_ready]; try discriminate;
    destruct (role_eq_dec _ _) as [Eq|N]; [|discriminate| |discriminate];
    intro Whole; inversion Whole; subst; auto.
Qed.

Lemma sent_site_possible {M p A} (code : Choreo M p A) path o d msg :
  output (descend path code) o d = Some msg -> possible_path path code.
Proof.
  revert A code. induction path as [|e path IH]; intros A code; destruct code;
    cbn [descend output outgoing possible_path]; try discriminate; try tauto;
    destruct e; cbn [descend output possible_path]; try discriminate; auto.
Qed.

Section First.
Context {M E Store Input} (model : local_model M E role (Store * Input))
  (stores : role -> Store) (input : Input) (R : list role) (A : role -> Type)
  (c : forall p, Choreo M p (A p)).
Local Notation prefix := (matched_prefix model stores input R A c).
Local Notation sm := (shared_model model).

(* Compare a waiting receiver with the FIRST send on its wire key. If that
   send was at another occurrence then it must lie strictly AFTER the site.
   The returned predecessor trace has made no sends at this key. *)
Theorem first_send_at_or_after tc s tn n gs p X kind site sender rd first rest :
  well_formed R M A c -> prefix tc s tn n gs ->
  In p R -> static_path site ->
  receive_site sm p (A p) (positions s p) X kind site sender rd ->
  let k := (sender,p,session_at site Choreography.Network.Root) in
  sent R k tc = first :: rest ->
  first = site \/
    exists tc0 s0 tn0 n0 gs0 a s1 b n1 gs1 batch,
      prefix tc0 s0 tn0 n0 gs0 /\ paired_step model R A s0 n0 gs0 a s1 b n1 gs1 /\
      sent R k tc0 = [] /\ emits R k a = first :: batch /\ source_before site first.
Proof.
  cbn zeta. intros WF Run InP Static Site Sent.
  destruct (receiver_selects_sender model stores input R A c _ _ _ _ _
    WF Run p InP X kind site sender rd Static Site) as (v & sh & Output & Law).
  destruct (first_send_prefix model stores input R A c _ _ _ _ _ _ _ _
    Run Sent) as (tc0 & s0 & tn0 & n0 & gs0 & a & s1 & b & n1 & gs1 & tcTail &
      tnTail & batch & g & TC & TN & Pre & Act & Next & Nil & Emits & InG & Key & Path).
  destruct g as [Y jk path from dest x sw]. cbn [message_path message_key] in Path, Key.
  subst path. injection Key as -> -> Sid.
  destruct (matched_payload_history model stores input R A c _ _ _ _ _ Next) as [past Hist].
  destruct (sampled_send_site model stores input R A c _ _ _ _ _ _ Y jk first sender p
    x sw Hist InG) as [_ First].
  pose proof (static_compatible site first (c sender) Static
    (sent_site_possible _ _ _ _ _ Output) First) as Comp.
  destruct (equal_lane_order _ _ Comp
    (proj1 (same_session_iff _ _ Choreography.Network.Root) (eq_sym Sid)))
    as [Eq|[Before|After]].
  - left; now symmetry.
  - right. exists tc0,s0,tn0,n0,gs0,a,s1,b,n1,gs1,batch. tauto.
  - exfalso. exact (DeadlockFirstSend.static_no_predecessor _ _ Static After).
Qed.

Theorem source_head_paths_static tc s tn n gs p :
  well_formed R M A c -> prefix tc s tn n gs -> In p R ->
  forall X kind site sender rd, static_path site ->
  receive_site sm p (A p) (positions s p) X kind site sender rd ->
  forall g, first_for (sender,p,session_at site Choreography.Network.Root) gs g ->
    message_path g = site.
Proof.
  intros WF Run InP X kind site sender rd Static Site g Head.
  set (key := (sender,p,session_at site Choreography.Network.Root)).
  destruct (sent R key tc) as [|first rest] eqn:Sent.
  - pose proof (prefix_ledger model stores input R A c _ _ _ _ _ key Run) as Ledger.
    rewrite Sent in Ledger. symmetry in Ledger. apply app_eq_nil in Ledger as [_ Empty].
    destruct (head_key_path _ _ _ Head) as [tail Nonempty].
    fold key in Nonempty. congruence.
  - eapply head_from_first_send; [exact Run|exact Site|exact Sent| |exact Head].
    destruct (first_send_at_or_after tc s tn n gs p X kind site sender rd first rest
      WF Run InP Static Site Sent) as [Eq|Later]; [exact Eq|exfalso].
    destruct Later as (tc0 & s0 & tn0 & n0 & gs0 & a & s1 & b & n1 & gs1 & batch &
      Early & Act & Empty & Emits & Before).
    destruct (receiver_selects_sender model stores input R A c _ _ _ _ _
      WF Run p InP X kind site sender rd Static Site) as (v & sh & Origin & Codec).
    assert (Ne : sender <> p).
    { destruct Site as (B & C & focus & Sil & Site). destruct Site; assumption. }
    assert (Emitted : In first (emits R (sender,p,session_at site Choreography.Network.Root) a)).
    { rewrite Emits; now left. }
    pose proof (static_sender_barrier sm R A c (stores,input) tc0 s0 a s1 sender p site first
      (prefix_source_run model stores input R A c _ _ _ _ _ Early)
      ltac:(exists site; split; [reflexivity|exact (output_is_sender _ _ _ _ _ _ _ _ InP Ne Origin)])
      (paired_source model R A _ _ _ _ _ _ _ _ Act)
      Emitted Before) as Issued.
    change (In site (sent R (sender,p,session_at site Choreography.Network.Root) tc0)) in Issued.
    rewrite Empty in Issued. exact Issued.
Qed.
End First.
