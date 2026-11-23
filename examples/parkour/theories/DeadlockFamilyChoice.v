From Stdlib Require Import Lists.List.
Require Import DeadlockFamilyLog DeadlockLogChoice DeadlockLogScope
  DeadlockPlayedFamily DeadlockPlayedActual DeadlockLocalLog DeadlockObservedCut
  DeadlockSource DeadlockLocal DeadlockChronology DeadlockCoherence
  DeadlockPlayedValues DeadlockPartialValues DeadlockMatch DeadlockWellFormed
  DeadlockState DeadlockPast DeadlockMessages DeadlockNetwork
  Parkour.Symbol Parkour.Codec Choreography.Choreo2
  Control.Monad.Tree.
Import ListNotations.
Local Arguments tokens {M E Store Input} model stores input R A c {p B} _.
Local Arguments cursor_at {M E Store Input} model stores input R A c {p B} _.
Local Arguments LoggedCut {M E Store Input} model stores input R A c {p B} _ _.

Polymorphic Lemma choice_forall_member {U : Type} (P : U -> Prop) xs x :
  Forall P xs -> In x xs -> P x.
Proof.
  intros All. induction All; cbn; intros Member; [contradiction|].
  destruct Member as [<-|Member]; [assumption|now apply IHAll].
Qed.

Section ChoiceFamily.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input0 : Input) (R : list Symbol)
  (A0 : Symbol -> Type) (c : forall p, Choreo M p (A0 p)).
Variable past : list payload_event.
Variable ar : actor_archive model stores input0 R A0 c.
Local Notation entry := (observed_entry model stores input0 R A0 c).
Local Notation site := (entry_site model stores input0 R A0 c).
Local Notation stamp := (stamped model stores input0 R A0 c).
Local Notation log := (actor_log model stores input0 R A0 c).
Local Notation cut := (logged_cut model stores input0 R A0 c).
Local Notation node := (at_node model stores input0 R A0 c past).
Local Notation good := (owns_region model stores input0 R A0 c ar).
Local Notation region := (in_region model stores input0 R A0 c ar).

Definition choice_action_site p B (t : @cursor M E p B)
    (a : @source_action E ((Symbol -> Store) * Input)) : Prop :=
  match t with
  | Code o (Perf (Cond _ _ _)) => action_path a = o
  | _ => True
  end.

Lemma primitive_choice_site p B t s q a u s' q' :
  primitive_action (shared_model model) R B t s q a u s' q' ->
  choice_action_site p B t a.
Proof. destruct 1; cbn [choice_action_site]; exact I || reflexivity. Qed.

Lemma stamped_choice_site p X B l o sh rd kl sl v k (e : entry p) u :
  stamp p B (Code o (Perf (@Cond M p X l B sh rd kl sl v k))) e u ->
  site p e = o.
Proof.
  intro First. rewrite <- (primitive_entry_site model stores input0 R A0 c
    p B _ e u First).
  exact (primitive_choice_site p B _ _ _ _ _ _ _ (proj1 First)).
Qed.

Definition choice_header_action p B (t : @cursor M E p B)
    (a : @source_action E ((Symbol -> Store) * Input)) : Prop :=
  match t with
  | Code o (Perf (@Cond _ _ X l _ _ _ _ _ _ _)) =>
      (exists x : X, a = AnnounceAction X o p x /\ l = p) \/
      (exists x : X, a = HearAction X o l p x /\ l <> p)
  | _ => True
  end.

Lemma primitive_choice_header p B t s q a u s' q' :
  primitive_action (shared_model model) R B t s q a u s' q' ->
  choice_header_action p B t a.
Proof.
  destruct 1; cbn [choice_header_action]; try exact I; eauto.
Qed.

(* These are the actual typed action constructors. Layout coverage can
   forget their payloads, but need not invent an announcement or hearing. *)
Lemma stamped_choice_header p X B l o sh rd kl sl v k (e : entry p) u :
  stamp p B (Code o (Perf (@Cond M p X l B sh rd kl sl v k))) e u ->
  (exists x : X, entry_action model stores input0 R A0 c p e =
      AnnounceAction X o p x /\ l = p) \/
  (exists x : X, entry_action model stores input0 R A0 c p e =
      HearAction X o l p x /\ l <> p).
Proof.
  intro First. exact (primitive_choice_header p B _ _ _ _ _ _ _ (proj1 First)).
Qed.

Definition choice_header_batch p B (t : @cursor M E p B)
    (events : list payload_event) : Prop :=
  match t with
  | Code o (Perf (@Cond _ _ _ l _ _ _ _ _ _ _)) =>
      forall ev, In ev events ->
      match ev with
      | Produced kind path sender recipient _ | Consumed kind path sender recipient _ =>
          kind = ChoiceDelivery /\ path = o /\ sender = l /\ l <> recipient
      end
  | _ => True
  end.

Lemma observed_choice_header_batch p B t s q a u s' q' na gs gs' events :
  observed (shared_model model) R B t s q a u s' q' na gs gs' events ->
  choice_header_batch p B t events.
Proof.
  destruct 1; cbn [choice_header_batch]; try exact I.
  - intros ev Member. apply in_map_iff in Member.
    destruct Member as [m [<- Member]].
    unfold announcement_messages in Member. apply in_map_iff in Member.
    destruct Member as [peer [<- Member]].
    cbn [produced_message]. repeat split; try reflexivity.
    apply filter_In in Member as [_ Member].
    destruct (role_eq_dec peer p); [discriminate|congruence].
  - intros ev [<-|[]]. repeat split; try reflexivity; assumption.
  - pose proof (silent_not_cond (shared_model model) p _ _ _ H) as Not.
    destruct t; cbn [choice_header_batch not_cond_cursor] in *; try exact I.
    match goal with code : Choreo _ _ _ |- _ => destruct code end;
      cbn [choice_header_batch not_cond_cursor] in *; try exact I.
    match goal with sig : ChoreoSig _ _ _ |- _ => destruct sig end;
      cbn [choice_header_batch not_cond_cursor] in *; try exact I.
    contradiction.
Qed.

Lemma stamped_choice_header_batch p X B l o sh rd kl sl v k (e : entry p) u :
  stamp p B (Code o (Perf (@Cond M p X l B sh rd kl sl v k))) e u ->
  forall ev, In ev (entry_batch model stores input0 R A0 c p e) ->
  match ev with
  | Produced kind path sender recipient _ | Consumed kind path sender recipient _ =>
      kind = ChoiceDelivery /\ path = o /\ sender = l /\ l <> recipient
  end.
Proof.
  intros [_ Obs].
  exact (observed_choice_header_batch p B _ _ _ _ _ _ _ _ _ _ _ Obs).
Qed.

(* A conditional has one event at its root. Every later token belongs to
   ChoiceBody, at any reached occurrence, not just the initial occurrence. *)
Lemma choice_suffix_owned p B o (original : cut p B) head suffix :
  (forall e, In e (tokens model stores input0 R A0 c original) <->
    region p o e) ->
  tokens model stores input0 R A0 c original = head :: suffix ->
  site p head = o ->
  Forall (fun e => extends (child o ChoiceBody) (site p e)) suffix ->
  forall e, In e suffix <-> region p (child o ChoiceBody) e.
Proof.
  intros Own Trace Head Scoped e. split.
  - intro Member. split.
    + exact (proj1 (proj1 (Own e) ltac:(rewrite Trace; now right))).
    + exact (choice_forall_member _ suffix e Scoped Member).
  - intros [Seen Below].
    assert (Old : region p o e).
    { split; [exact Seen|]. now apply extends_child in Below. }
    apply (proj2 (Own e)) in Old. rewrite Trace in Old.
    destruct Old as [Eq|Member]; [|exact Member].
    subst e. rewrite Head in Below.
    destruct (choice_fresh o o Below) as [Ne _]. contradiction.
Qed.

Theorem replay_cond_logged_partition tc s tn n gs S X l A
    (sh : forall p, S p -> Show X) (rd : forall p, S p -> Read X)
    (input : values (fun p => At X l p) S)
    (k : forall p, S p -> X -> Choreo M p (A p))
    active completed inc o (cuts : family cut A active)
    (done : includes (fun p => In p completed) (fun p => In p active))
    (v : values A (fun p => In p completed)) :
  payload_history model stores input0 R A0 c tc s tn n gs past ->
  NoDup active -> NoDup completed ->
  good A active o cuts ->
  family_at cut node S A (fun p s => Perf (@Cond M p X l (A p)
    (sh p s) (rd p s) (known l) MkSSymbol (input p s) (k p s)))
    active inc o cuts ->
  family_returned cut (finished model stores input0 R A0 c)
    A active completed done cuts v ->
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (finished_in : includes (fun p => In p completed) (fun p => In p entered))
    (choices : values (fun _ => X) (fun p => In p entered))
    (body : family cut A entered),
    NoDup entered /\
    good A entered (child o ChoiceBody) body /\
    (forall p d, choice_observation past X l p (rd p (inc p (inside p d)))
      (input p (inc p (inside p d))) o (choices p d)) /\
    (forall p d, node p _ (child o ChoiceBody)
      (k p (inc p (inside p d)) (choices p d)) (body p d)) /\
    family_returned cut (finished model stores input0 R A0 c)
      A entered completed finished_in body v /\
    (forall p d, cursor_at model stores input0 R A0 c (cuts p (inside p d)) =
      cursor_at model stores input0 R A0 c (body p d)) /\
    (forall p d, ~ In p entered ->
      cursor_at model stores input0 R A0 c (cuts p d) =
      Code o (Perf (@Cond M p X l (A p) (sh p (inc p d)) (rd p (inc p d))
        (known l) MkSSymbol (input p (inc p d)) (k p (inc p d))))) /\
    (forall p d, exists header : entry p,
      tokens model stores input0 R A0 c (cuts p (inside p d)) =
        header :: tokens model stores input0 R A0 c (body p d) /\
      site p header = o /\
      stamp p (A p)
        (Code o (Perf (@Cond M p X l (A p)
          (sh p (inc p (inside p d))) (rd p (inc p (inside p d)))
          (known l) MkSSymbol (input p (inc p (inside p d)))
          (k p (inc p (inside p d)))))) header
        (Code (child o ChoiceBody) (k p (inc p (inside p d)) (choices p d)))) /\
    (forall p d, ~ In p entered ->
      tokens model stores input0 R A0 c (cuts p d) = []).
Proof.
  intros Hist NA NC Good At Ret.
  set (head := fun p s => Perf (@Cond M p X l (A p)
    (sh p s) (rd p s) (known l) MkSSymbol (input p s) (k p s))).
  destruct (@select_returned
    (fun p => option (X * entry p * list (entry p))%type)
    (fun p part => forall d : In p active,
      match part with
      | None => tokens model stores input0 R A0 c (cuts p d) = [] /\
          cursor_at model stores input0 R A0 c (cuts p d) = Code o (head p (inc p d))
      | Some (x,e,suffix) =>
          tokens model stores input0 R A0 c (cuts p d) = e :: suffix /\
          site p e = o /\
          choice_observation past X l p (rd p (inc p d)) (input p (inc p d)) o x /\
          stamp p (A p) (Code o (head p (inc p d))) e
            (Code (child o ChoiceBody) (k p (inc p d) x)) /\
          node p _ (child o ChoiceBody) (k p (inc p d) x)
            (LoggedCut model stores input0 R A0 c
              (cursor_at model stores input0 R A0 c (cuts p d)) suffix)
      end) active) as (parts & Valid).
  - intros p d. destruct (At p d) as [Run Stamps].
    destruct (actor_log_cond_replay model stores input0 R A0 c tc s tn n gs past
      p X (A p) l o _ _ _ _ _ _ _ _ Hist Stamps Run)
      as [Empty|(e & suffix & x & Trace & First & Choice & Rest)].
    + exists None. intro d'. rewrite <- (roster_member_unique active NA p d d').
      exact Empty.
    + exists (Some (x,e,suffix)). intro d'.
      rewrite <- (roster_member_unique active NA p d d').
      split; [exact Trace|]. split.
      * exact (stamped_choice_site p X (A p) l o
          (sh p (inc p d)) (rd p (inc p d)) (known l) MkSSymbol
          (input p (inc p d)) (k p (inc p d)) e _ First).
      * split; [exact Choice|]. split; [exact First|]. split; [exact Rest|].
        intros token Member. apply Stamps. rewrite Trace; now right.
  - set (obs := fun p =>
      match in_dec (List.list_eq_dec BinNat.N.eq_dec) p active with
      | left d => parts p d
      | right _ => None
      end).
    assert (Observed : forall p d, obs p = parts p d).
    { intros p d. unfold obs.
      destruct (in_dec (List.list_eq_dec BinNat.N.eq_dec) p active) as [e|Ne].
      - now rewrite (roster_member_unique active NA p e d).
      - contradiction. }
    set (entered := entered_domain _ active obs).
    set (inside := entered_inside _ active obs).
    set (triple := entered_value _ active obs).
    assert (Entry : forall p d, parts p (inside p d) = Some (triple p d)).
    { intros p d. rewrite <- Observed.
      exact (entered_value_spec _ active obs p d). }
    assert (Finished : includes (fun p => In p completed) (fun p => In p entered)).
    { intros p d.
      pose proof (Valid p (done p d) (done p d)) as H.
      pose proof (Ret p d) as Return.
      pose proof (Observed p (done p d)) as O.
      destruct (parts p (done p d)) as [[[x e] suffix]|]; cbn in H,O.
      - eapply entered_domain_complete; [apply done; exact d|exact O].
      - unfold DeadlockFamilyLog.finished in Return.
        rewrite (proj2 H) in Return. contradiction. }
    assert (Body : forall p d,
      let '(x,e,suffix) := triple p d in
      tokens model stores input0 R A0 c (cuts p (inside p d)) = e :: suffix /\
      site p e = o /\
      choice_observation past X l p (rd p (inc p (inside p d)))
        (input p (inc p (inside p d))) o x /\
      stamp p (A p) (Code o (head p (inc p (inside p d)))) e
        (Code (child o ChoiceBody) (k p (inc p (inside p d)) x)) /\
      node p _ (child o ChoiceBody) (k p (inc p (inside p d)) x)
        (LoggedCut model stores input0 R A0 c
          (cursor_at model stores input0 R A0 c (cuts p (inside p d))) suffix)).
    { intros p d. pose proof (Valid p (inside p d) (inside p d)) as H.
      rewrite Entry in H. destruct (triple p d) as [[x e] suffix]. exact H. }
    set (body := fun p d =>
      let '(x,e,suffix) := triple p d in
      LoggedCut model stores input0 R A0 c
        (cursor_at model stores input0 R A0 c (cuts p (inside p d))) suffix).
    assert (SuffixOwn : forall p d token,
      In token (tokens model stores input0 R A0 c (body p d)) <->
      region p (child o ChoiceBody) token).
    { intros p d token. unfold body.
      pose proof (Body p d) as H.
      destruct (triple p d) as [[x e] suffix].
      destruct H as [Trace [Site [Choice [First [Run Stamps]]]]].
      eapply choice_suffix_owned; [exact (proj2 (proj2 Good) p (inside p d))|
        exact Trace|exact Site|].
      exact (proj1 (actor_log_scope model stores input0 R A0 c p _ _ _ _ _ Run)). }
    exists entered,inside,Finished,
      (fun p d => let '(x,e,suffix) := triple p d in x),body.
    split; [apply entered_domain_nodup; exact NA|]. split.
    + split; [apply entered_domain_nodup; exact NA|]. split.
      * intros p token InBody.
        assert (Old : region p o token).
        { split; [exact (proj1 InBody)|].
          apply extends_child with ChoiceBody. exact (proj2 InBody). }
        pose proof (proj1 (proj2 Good) p token Old) as Present.
        pose proof (Valid p Present Present) as H.
        pose proof (Observed p Present) as O.
        destruct (parts p Present) as [[[x e] suffix]|].
        -- eapply entered_domain_complete; [exact Present|exact O].
        -- apply (proj2 (proj2 Good) p Present) in Old.
           rewrite (proj1 H) in Old. contradiction.
      * exact SuffixOwn.
    + split.
      * intros p d. pose proof (Body p d) as H.
        destruct (triple p d) as [[x e] suffix]. exact (proj1 (proj2 (proj2 H))).
      * split.
        -- intros p d. pose proof (Body p d) as H.
           unfold body. destruct (triple p d) as [[x e] suffix].
           exact (proj2 (proj2 (proj2 (proj2 H)))).
        -- split.
           ++ intros p d. unfold body.
              destruct (triple p (Finished p d)) as [[x e] suffix].
              unfold DeadlockFamilyLog.finished; cbn.
              rewrite (roster_member_unique active NA p
                (inside p (Finished p d)) (done p d)). apply Ret.
           ++ split.
              ** intros p d. unfold body.
                 destruct (triple p d) as [[x e] suffix]. reflexivity.
               ** split.
                  --- intros p d NotEntered. pose proof (Valid p d d) as H.
                      pose proof (Observed p d) as O.
                      destruct (parts p d) as [[[x e] suffix]|].
                      +++ exfalso. apply NotEntered.
                          eapply entered_domain_complete; [exact d|exact O].
                      +++ exact (proj2 H).
                  --- split.
                      +++ intros p d. pose proof (Body p d) as H.
                          unfold body. destruct (triple p d) as [[x e] suffix].
                          exists e. split; [exact (proj1 H)|].
                          split; [exact (proj1 (proj2 H))|].
                          exact (proj1 (proj2 (proj2 (proj2 H)))).
                      +++ intros p d NotEntered. pose proof (Valid p d d) as H.
                          pose proof (Observed p d) as O.
                          destruct (parts p d) as [[[x e] suffix]|].
                          *** exfalso. apply NotEntered.
                              eapply entered_domain_complete; [exact d|exact O].
                          *** exact (proj1 H).
Qed.

Theorem replay_cond_logged_strong tc s tn n gs S X l A
    (sh : forall p, S p -> Show X) (rd : forall p, S p -> Read X)
    (input : values (fun p => At X l p) S)
    (k : forall p, S p -> X -> Choreo M p (A p))
    active completed inc o (cuts : family cut A active)
    (done : includes (fun p => In p completed) (fun p => In p active))
    (v : values A (fun p => In p completed)) :
  payload_history model stores input0 R A0 c tc s tn n gs past ->
  NoDup active -> NoDup completed ->
  good A active o cuts ->
  family_at cut node S A (fun p s => Perf (@Cond M p X l (A p)
    (sh p s) (rd p s) (known l) MkSSymbol (input p s) (k p s)))
    active inc o cuts ->
  family_returned cut (finished model stores input0 R A0 c)
    A active completed done cuts v ->
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (finished_in : includes (fun p => In p completed) (fun p => In p entered))
    (choices : values (fun _ => X) (fun p => In p entered))
    (body : family cut A entered),
    NoDup entered /\
    good A entered (child o ChoiceBody) body /\
    (forall p d, choice_observation past X l p (rd p (inc p (inside p d)))
      (input p (inc p (inside p d))) o (choices p d)) /\
    (forall p d, node p _ (child o ChoiceBody)
      (k p (inc p (inside p d)) (choices p d)) (body p d)) /\
    family_returned cut (finished model stores input0 R A0 c)
      A entered completed finished_in body v /\
    (forall p d, cursor_at model stores input0 R A0 c (cuts p (inside p d)) =
      cursor_at model stores input0 R A0 c (body p d)) /\
    (forall p d, ~ In p entered ->
      cursor_at model stores input0 R A0 c (cuts p d) =
      Code o (Perf (@Cond M p X l (A p) (sh p (inc p d)) (rd p (inc p d))
        (known l) MkSSymbol (input p (inc p d)) (k p (inc p d))))).
Proof.
  intros Hist NA NC Good At Ret.
  destruct (replay_cond_logged_partition tc s tn n gs S X l A sh rd input k
    active completed inc o cuts done v Hist NA NC Good At Ret)
    as (entered & inside & finished_in & choices & body &
      NE & Owned & Choice & BodyAt & BodyRet & EnteredShape &
      OutsideShape & Headers & Absent).
  exists entered,inside,finished_in,choices,body.
  split; [exact NE|]. split; [exact Owned|]. split; [exact Choice|].
  split; [exact BodyAt|]. split; [exact BodyRet|].
  split; [exact EnteredShape|exact OutsideShape].
Qed.

Theorem replay_cond_logged tc s tn n gs S X l A
    (sh : forall p, S p -> Show X) (rd : forall p, S p -> Read X)
    (input : values (fun p => At X l p) S)
    (k : forall p, S p -> X -> Choreo M p (A p))
    active completed inc o (cuts : family cut A active)
    (done : includes (fun p => In p completed) (fun p => In p active))
    (v : values A (fun p => In p completed)) :
  observed_archives model stores input0 R A0 c tc s tn n gs past ar ->
  NoDup active -> NoDup completed ->
  good A active o cuts ->
  family_at cut node S A (fun p s => Perf (@Cond M p X l (A p)
    (sh p s) (rd p s) (known l) MkSSymbol (input p s) (k p s)))
    active inc o cuts ->
  family_returned cut (finished model stores input0 R A0 c)
    A active completed done cuts v ->
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (finished_in : includes (fun p => In p completed) (fun p => In p entered))
    (choices : values (fun _ => X) (fun p => In p entered))
    (body : family cut A entered),
    NoDup entered /\
    good A entered (child o ChoiceBody) body /\
    (forall p d, choice_observation past X l p (rd p (inc p (inside p d)))
      (input p (inc p (inside p d))) o (choices p d)) /\
    (forall p d, node p _ (child o ChoiceBody)
      (k p (inc p (inside p d)) (choices p d)) (body p d)) /\
    family_returned cut (finished model stores input0 R A0 c)
      A entered completed finished_in body v.
Proof.
  intros Observed NA NC Good At Ret.
  pose proof (observed_archives_history model stores input0 R A0 c
    tc s tn n gs past ar Observed) as Hist.
  destruct (replay_cond_logged_strong tc s tn n gs S X l A sh rd input k
    active completed inc o cuts done v Hist NA NC Good At Ret)
    as (entered & inside & finished_in & choices & body &
      NE & Owned & Choice & BodyAt & BodyRet & EnteredShape & OutsideShape).
  exists entered,inside,finished_in,choices,body.
  split; [exact NE|]. split; [exact Owned|]. split; [exact Choice|].
  split; [exact BodyAt|exact BodyRet].
Qed.
End ChoiceFamily.

Print Assumptions replay_cond_logged_strong.
Print Assumptions replay_cond_logged.
Print Assumptions replay_cond_logged_partition.
