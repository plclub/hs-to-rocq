Require Import DeadlockNetwork DeadlockLocal Choreography.Network Parkour.Codec.

(* A computational view for inverting steps at a known control. It keeps the
   real residual, wire action and post-state. No injectivity of dependent
   constructor packages or proof-irrelevance axiom is needed. *)
Section Views.
Context {M E : Type -> Type} {S : Type} (m : local_model M E role S)
        (roles : list role) (p : role).

Definition primitive_view {A} (op : NetworkSig M A) q s obs
    : @control M E A -> queues -> S -> Prop :=
  match op in NetworkSig _ X return control X -> queues -> S -> Prop with
  | Exec e => fun u r s' =>
      exists a t', local_step (reply_local _ _ _ _ m) p
        (interpret_local _ _ _ _ m _ e) s a t' s' /\
        obs = Local a /\ u = CLocal t' /\ r = q
  | @Send _ X sh sid v dst => fun u r s' =>
      obs = Sent p dst sid (@show X sh v) /\ u = CPure tt /\
      r = enqueue q (p,dst,sid) (@show X sh v) /\ s' = s
  | @Recv _ X rd sid src => fun u r s' =>
      exists w ws x, q (src,p,sid) = cons w ws /\ @read X rd w = Some x /\
        obs = Received src p sid w /\ u = CPure x /\
        r = replace_queue q (src,p,sid) ws /\ s' = s
  | @BCast _ X sh sid v => fun u r s' =>
      obs = Announced p sid (@show X sh v) /\ u = CPure tt /\
      r = announce roles p sid (@show X sh v) q /\ s' = s
  end.

Fixpoint step_view {A} (t : @control M E A) q s obs : control A -> queues -> S
  -> Prop :=
  match t in control X return control X -> queues -> S -> Prop with
  | CPure _ => fun _ _ _ => False
  | CPerf op => primitive_view op q s obs
  | CLocal t => fun u r s' =>
      exists a t', local_step (reply_local _ _ _ _ m) p t s a t' s' /\
        obs = Local a /\ u = CLocal t' /\ r = q
  | CBind t k => fun u r s' =>
      (exists v, step_view t q s obs v r s' /\ u = CBind v k) \/
      (exists x, returns m _ t x /\ step_view (k x) q s obs u r s')
  | CApp f x => fun u r s' =>
      (exists g, step_view f q s obs g r s' /\ u = CApp g x) \/
      (exists y, step_view x q s obs y r s' /\ u = CApp f y)
  end.

Lemma view_of_step A (t u : control A) q s obs r s' :
  step m roles p A t q s obs u r s' -> step_view t q s obs u r s'.
Proof.
  induction 1; cbn; eauto 10.
Qed.

Lemma step_of_view A (t u : control A) q s obs r s' :
  step_view t q s obs u r s' -> step m roles p A t q s obs u r s'.
Proof.
  revert u. induction t as [A v|A op|A B t IH k KH|A B f FH x XH|A t]; cbn;
    intros u H.
  - contradiction.
  - destruct op; cbn in H.
    + destruct H as (event & next & Hlocal & -> & -> & ->). now apply StepExec.
    + destruct H as (-> & -> & -> & ->). apply StepSend.
    + destruct H as (w & ws & x & Hhead & Hread & -> & -> & -> & ->).
      eapply StepRecv; eassumption.
    + destruct H as (-> & -> & -> & ->). apply StepBCast.
  - destruct H as [(v & H & ->) | (x & Hr & H)].
    + apply StepBind, IH, H.
    + eapply StepContinue; [exact Hr | apply KH, H].
  - destruct H as [(g & H & ->) | (y & H & ->)].
    + apply StepLeft, FH, H.
    + apply StepRight, XH, H.
  - destruct H as (event & next & Hlocal & -> & -> & ->). now apply StepLocal.
Qed.
End Views.
