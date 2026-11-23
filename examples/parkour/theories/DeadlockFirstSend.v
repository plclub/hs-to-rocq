From Stdlib Require Import Lists.List.
Require Import DeadlockSource DeadlockNetwork DeadlockFrontiers DeadlockMessages
  DeadlockMatch DeadlockLocal DeadlockOrder DeadlockStaticOrigin DeadlockStaticPaths
  DeadlockState DeadlockWellFormed DeadlockCutSafety DeadlockFrontierCoverage
  DeadlockCoherence DeadlockChronology DeadlockHead Parkour.Symbol.
Import ListNotations.

Lemma static_no_predecessor prior site :
  static_path site -> ~ source_before prior site.
Proof.
  intros [Choice Body] Before. induction Before; cbn in *; tauto.
Qed.

Lemma head_key_path k gs g :
  first_for k gs g ->
  exists tail, key_paths k gs = message_path g :: tail.
Proof.
  intros (pre & post & -> & Earlier & <-).
  rewrite key_paths_app, key_paths_absent by exact Earlier.
  rewrite key_paths_same. eexists; reflexivity.
Qed.

Lemma path_member k gs path :
  In path (key_paths k gs) ->
  exists g, In g gs /\ message_key g = k /\ message_path g = path.
Proof.
  unfold key_paths. intro H. apply in_map_iff in H.
  destruct H as (g & Eq & Eligible). apply filter_In in Eligible.
  destruct Eligible as [Member Test]. exists g.
  destruct (key_eq_dec (message_key g) k); intuition discriminate.
Qed.

Lemma emits_without_receive {E S} R k (a : @source_action E S) :
  emits R k a <> [] -> receives k a = [].
Proof. destruct a; cbn [emits receives]; tauto. Qed.

Section First.
Context {M E Store Input} (model : local_model M E role (Store * Input))
  (stores : role -> Store) (input : Input) (R : list role) (A : role -> Type)
  (c : forall p, Choreography.Choreo2.Choreo M p (A p)).
Local Notation prefix := (matched_prefix model stores input R A c).

(* Locate the actual step that first emitted on this key. Both traces carry
   their suffixes to the queried destination, rather than just asserting the
   existence of some other execution that can send the same occurrence. *)
Theorem first_send_prefix tc s tn n gs k first rest :
  prefix tc s tn n gs -> sent R k tc = first :: rest ->
  exists tc0 s0 tn0 n0 gs0 a s1 b n1 gs1 tailC tailN batchTail g,
    tc = tc0 ++ a :: tailC /\ tn = tn0 ++ b :: tailN /\
    prefix tc0 s0 tn0 n0 gs0 /\
    paired_step model R A s0 n0 gs0 a s1 b n1 gs1 /\
    prefix (tc0 ++ [a]) s1 (tn0 ++ [b]) n1 gs1 /\
    sent R k tc0 = [] /\ emits R k a = first :: batchTail /\
    In g gs1 /\ message_key g = k /\ message_path g = first.
Proof.
  intro Hist. revert first rest. induction Hist as
    [|tc s tn n gs a s' b n' gs' P IH Pair State]; intros first rest Sent; [discriminate|].
  unfold sent in Sent.
  rewrite flat_map_app in Sent. cbn [flat_map] in Sent. rewrite app_nil_r in Sent.
  fold (sent R k tc) in Sent. destruct (sent R k tc) as [|head old] eqn:Sends.
  - cbn in Sent.
    assert (New : prefix (tc ++ [a]) s' (tn ++ [b]) n' gs') by (econstructor; eassumption).
    pose proof (prefix_ledger _ _ _ _ _ _ _ _ _ _ _ k P) as Old.
    rewrite Sends in Old. symmetry in Old. apply app_eq_nil in Old as [Rec _].
    pose proof (prefix_ledger _ _ _ _ _ _ _ _ _ _ _ k New) as Ledger.
    unfold sent,received in Ledger. rewrite !flat_map_app in Ledger. cbn [flat_map] in Ledger.
    rewrite !app_nil_r in Ledger. fold (sent R k tc) (received k tc) in Ledger.
    rewrite Sends, Rec, (emits_without_receive R k a ltac:(rewrite Sent; discriminate)) in Ledger.
    cbn in Ledger. rewrite Sent in Ledger.
    destruct (path_member k gs' first ltac:(rewrite <- Ledger; now left)) as (g & InG & Key & Path).
    exists tc,s,tn,n,gs,a,s',b,n',gs',[],[],rest,g. repeat split; assumption || reflexivity.
  - injection Sent as <- Eq.
    destruct (IH head old eq_refl)
      as (tc0 & s0 & tn0 & n0 & gs0 & a0 & s1 & b0 & n1 & gs1 & tailC & tailN & bt & g &
        -> & -> & Prefix & Act & Next & Before & Batch & InG & Key & Path).
    exists tc0,s0,tn0,n0,gs0,a0,s1,b0,n1,gs1,(tailC ++ [a]),(tailN ++ [b]),bt,g.
    rewrite <- !app_assoc. repeat split; assumption || reflexivity.
Qed.
End First.

Lemma plugged_future {M E p B A} (C : @cursor_context M E p B A) focus o :
  future focus o -> future (plug C focus) o.
Proof. induction C; cbn; intros F; first [exact F|left; now apply IHC|right; now apply IHC]. Qed.

Lemma receive_site_future {M E S} (m : local_model M E role S) p A t X kind o sender rd :
  receive_site m p A t X kind o sender rd -> future t o.
Proof.
  intros (B & C & focus & Sil & Site).
  assert (Seen : future (plug C focus) o).
  { apply plugged_future. destruct Site; cbn; apply extends_refl. }
  induction Sil; [exact Seen|]. eapply silent_future; [exact H|now apply IHSil].
Qed.

Section StaticFrontier.
Context {M E Store Input} (model : local_model M E role (Store * Input))
  (stores : role -> Store) (input : Input) (R : list role) (A : role -> Type)
  (c : forall p, Choreography.Choreo2.Choreo M p (A p)).
Local Notation prefix := (matched_prefix model stores input R A c).
Local Notation sm := (shared_model model).

Theorem head_from_first_send tc s tn n gs p X kind site sender rd first rest head :
  prefix tc s tn n gs ->
  receive_site sm p (A p) (positions s p) X kind site sender rd ->
  sent R (sender,p,session_at site Choreography.Network.Root) tc = first :: rest ->
  first = site ->
  first_for (sender,p,session_at site Choreography.Network.Root) gs head ->
  message_path head = site.
Proof.
  intros P Site Sent -> First.
  pose proof (matched_future_unreceived model stores input R A c _ _ _ _ _ sender p
    (session_at site Choreography.Network.Root) site P
    (receive_site_future sm p (A p) _ X kind _ _ _ Site)) as Fresh.
  pose proof (prefix_ledger model stores input R A c _ _ _ _ _
    (sender,p,session_at site Choreography.Network.Root) P) as Eq.
  destruct (head_key_path _ _ _ First) as [tail Pending].
  rewrite Sent, Pending in Eq.
  destruct (received _ _) as [|earlier consumed]; cbn in Eq; injection Eq as E1 E2.
  - symmetry; exact E1.
  - exfalso; apply Fresh; now left.
Qed.
End StaticFrontier.
