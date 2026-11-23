From Stdlib Require Import Lists.List.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Symbol.
Require Import DeadlockSource DeadlockCoherence DeadlockReplay
  DeadlockWellFormed DeadlockPartialValues.
Import ListNotations.

(* These are inversions of the cut obtained from the actual history. They
   retain the stored Bind prefix and the actual conditional transition. *)
Section ActualCuts.
Context {M E : Type -> Type} {Store : Type}.
Variable model : DeadlockLocal.local_model M E Symbol Store.
Variable configured : list Symbol.
Variable p : Symbol.

Definition cut_returned {A} (t : @cursor M E p A) (v : A) : Prop :=
  match t in cursor _ B return B -> Prop with
  | Returned x => fun v => v = x
  | _ => fun _ => False
  end v.

Definition decomposition {A} o (c : Choreo M p A)
    (t : @cursor M E p A) : Prop :=
  match c in Tree _ B return cursor p B -> Prop with
  | App f x => fun t =>
      t = Code o (App f x) \/
      exists cf cx,
        syntax_cut model configured p _ (child o AppFunction) f cf /\
        syntax_cut model configured p _ (child o AppArgument) x cx /\
        (t = Fork cf cx \/
         exists fv xv, cf = Returned fv /\ cx = Returned xv /\
           t = Returned (fv xv))
  | Bind prefix k => fun t =>
      t = Code o (Bind prefix k) \/
      (exists ct,
        syntax_cut model configured p _ (child o BindPrefix) prefix ct /\
        t = Seq o ct k) \/
      exists x body,
        syntax_cut model configured p _ (child o BindPrefix) prefix (Returned x)
          /\
        syntax_cut model configured p _ (child o BindBody) (k x) body /\
        t = body
  | Perf e =>
      match e in ChoreoSig _ _ B return cursor p B -> Prop with
      | @Cond _ _ X l Y sh rd kl sl input k => fun t =>
          t = Code o (Perf (@Cond M p X l Y sh rd kl sl input k)) \/
          exists x body s q a s' q',
            ((exists same : l = p,
                x = unAt input same /\ a = AnnounceAction X o p x) \/
             (l <> p /\ a = HearAction X o l p x)) /\
            primitive_action model configured Y
              (Code o (Perf (@Cond M p X l Y sh rd kl sl input k)))
              s q a (Code (child o ChoiceBody) (k x)) s' q' /\
            syntax_cut model configured p Y (child o ChoiceBody) (k x) body /\
            t = body
      | _ => fun _ => True
      end
  | _ => fun _ => True
  end t.

Lemma syntax_cut_decomposition A o c t :
  syntax_cut model configured p A o c t -> decomposition o c t.
Proof.
  destruct 1; cbn [decomposition].
  - destruct c as [A e|A x|X Y f x|X Y prefix k]; cbn; try exact I;
      try (left; reflexivity).
    destruct e; cbn; try exact I. left; reflexivity.
  - exact I.
  - destruct H; exact I.
  - right. do 2 eexists. repeat split; try eassumption.
    left; reflexivity.
  - right. do 2 eexists. repeat split; try eassumption.
    right. do 2 eexists. repeat split; reflexivity.
  - right; left. eexists. split; [eassumption|reflexivity].
  - right; right. do 2 eexists. repeat split; try eassumption; reflexivity.
  - right. do 7 eexists. repeat split; try eassumption; reflexivity.
Qed.

Theorem actual_history_decomposition A o (c : Choreo M p A) tr t :
  cursor_history model configured (Code o c) tr t ->
  decomposition o c t.
Proof.
  intro History. apply syntax_cut_decomposition.
  eapply code_history_has_syntax_cut. exact History.
Qed.

Lemma app_cut_children X Y o (f : Choreo M p (X -> Y)) x t :
  syntax_cut model configured p Y o (App f x) t ->
  exists cf cx,
    syntax_cut model configured p _ (child o AppFunction) f cf /\
    syntax_cut model configured p _ (child o AppArgument) x cx /\
    (forall v, cut_returned t v ->
      exists fv xv, cut_returned cf fv /\ cut_returned cx xv /\ v = fv xv).
Proof.
  intro Cut. destruct (syntax_cut_decomposition _ _ _ _ Cut)
    as [Initial|(cf & cx & F & Xcut & Shape)].
  - subst t.
    exists (Code (child o AppFunction) f), (Code (child o AppArgument) x).
    split; [apply SyntaxCode|]. split; [apply SyntaxCode|].
    intros v Return. contradiction.
  - exists cf, cx. split; [exact F|]. split; [exact Xcut|].
    intros v Return. destruct Shape as [Forked|(fv & xv & Ef & Ex & Et)].
    + subst t. contradiction.
    + subst cf cx t. exists fv, xv. cbn [cut_returned] in *.
      repeat split; try reflexivity; exact Return.
Qed.

Lemma bind_cut_completed_prefix X Y o
    (prefix : Choreo M p X) (k : X -> Choreo M p Y) t v :
  syntax_cut model configured p Y o (Bind prefix k) t ->
  cut_returned t v ->
  exists x body,
    syntax_cut model configured p X (child o BindPrefix) prefix (Returned x) /\
    syntax_cut model configured p Y (child o BindBody) (k x) body /\
    cut_returned body v.
Proof.
  intros Cut Return.
  destruct (syntax_cut_decomposition _ _ _ _ Cut)
    as [Initial|[(ct & Prefix & Seq)|(x & body & Prefix & Body & Eq)]].
  - subst t. contradiction.
  - subst t. contradiction.
  - subst t. exists x, body. repeat split; assumption.
Qed.

Lemma choice_cut_completed_body X Y l o sh rd kl sl input
    (k : X -> Choreo M p Y) t v :
  syntax_cut model configured p Y o
    (Perf (@Cond M p X l Y sh rd kl sl input k)) t ->
  cut_returned t v ->
  exists x body s q a s' q',
    ((exists same : l = p,
        x = unAt input same /\ a = AnnounceAction X o p x) \/
     (l <> p /\ a = HearAction X o l p x)) /\
    primitive_action model configured Y
      (Code o (Perf (@Cond M p X l Y sh rd kl sl input k)))
      s q a (Code (child o ChoiceBody) (k x)) s' q' /\
    syntax_cut model configured p Y (child o ChoiceBody) (k x) body /\
    cut_returned body v.
Proof.
  intros Cut Return.
  destruct (syntax_cut_decomposition _ _ _ _ Cut)
    as [Initial|(x & body & s & q & a & s' & q' & Selected & Step & Body & Eq)].
  - subst t. contradiction.
  - subst t. exists x, body, s, q, a, s', q'.
    repeat split; assumption.
Qed.

Corollary actual_app_children X Y o (f : Choreo M p (X -> Y)) x tr t :
  cursor_history model configured (Code o (App f x)) tr t ->
  exists cf cx,
    syntax_cut model configured p _ (child o AppFunction) f cf /\
    syntax_cut model configured p _ (child o AppArgument) x cx /\
    (forall v, cut_returned t v ->
      exists fv xv, cut_returned cf fv /\ cut_returned cx xv /\ v = fv xv).
Proof.
  intro History. apply app_cut_children.
  eapply code_history_has_syntax_cut. exact History.
Qed.

Corollary actual_bind_completed_prefix X Y o
    (prefix : Choreo M p X) (k : X -> Choreo M p Y) tr t v :
  cursor_history model configured (Code o (Bind prefix k)) tr t ->
  cut_returned t v ->
  exists x body,
    syntax_cut model configured p X (child o BindPrefix) prefix (Returned x) /\
    syntax_cut model configured p Y (child o BindBody) (k x) body /\
    cut_returned body v.
Proof.
  intros History Return. eapply bind_cut_completed_prefix; [|exact Return].
  eapply code_history_has_syntax_cut. exact History.
Qed.

(* The prefix cut also exists when the role has not yet entered its body.
   In the entered case it is the retained, returned prefix, not a new witness
   chosen from a source result predicate. *)
Lemma bind_cut_prefix X Y o
    (prefix : Choreo M p X) (k : X -> Choreo M p Y) t :
  syntax_cut model configured p Y o (Bind prefix k) t ->
  exists ct,
    syntax_cut model configured p X (child o BindPrefix) prefix ct /\
    ((t = Code o (Bind prefix k) \/ t = Seq o ct k) \/
     exists x body,
       ct = Returned x /\
       syntax_cut model configured p Y (child o BindBody) (k x) body /\
       t = body).
Proof.
  intro Cut.
  destruct (syntax_cut_decomposition _ _ _ _ Cut)
    as [Initial|[(ct & Prefix & Seq)|(x & body & Prefix & Body & Eq)]].
  - exists (Code (child o BindPrefix) prefix).
    split; [apply SyntaxCode|]. left; left; exact Initial.
  - exists ct. split; [exact Prefix|]. left; right; exact Seq.
  - exists (Returned x). split; [exact Prefix|].
    right. exists x, body. repeat split; try assumption; reflexivity.
Qed.

Corollary initial_role_actual_decomposition A
    (c : forall r, Choreo M r (A r)) s tr finish :
  crun model configured (initial c s) tr finish ->
  decomposition [] (c p) (@positions M E Store A finish p).
Proof.
  intro Run. apply actual_history_decomposition with (tr := actor_actions p tr).
  exact (initial_actor_history model configured A c s tr finish Run p).
Qed.

End ActualCuts.

Print Assumptions actual_history_decomposition.
Print Assumptions app_cut_children.
Print Assumptions bind_cut_completed_prefix.
Print Assumptions choice_cut_completed_body.
Print Assumptions actual_app_children.
Print Assumptions actual_bind_completed_prefix.
Print Assumptions bind_cut_prefix.
Print Assumptions initial_role_actual_decomposition.

(* Bridge for DeadlockSameHistory.at_sender_cut: this conclusion concerns
   exactly the supplied archived cut, not another history with the same
   endpoint. Its archive is neither replaced nor existentially reselected. *)
Theorem archived_cut_actual_syntax
    {M E : Type -> Type} {Store : Type}
    (model : DeadlockLocal.local_model M E Symbol Store) configured p A o
    (c : Choreo M p A) tr
    (cut : annotated_cut model configured p A) :
  cut_history model configured p (Code o c) tr cut ->
  syntax_cut model configured p A o c (erased_cursor model configured p A cut).
Proof.
  intro History. apply code_history_has_syntax_cut with (tr := tr).
  exact (cut_is_actual_history model configured p A (Code o c) tr cut History).
Qed.

(* A finite domain of actual optional observations. The domain is computed
   from the observations, rather than assumed to contain all completed roles. *)
Definition has_value {T} (v : option T) : bool :=
  match v with Some _ => true | None => false end.

Definition option_value {T} (v : option T) :
    has_value v = true -> T :=
  match v as u return has_value u = true -> T with
  | Some x => fun _ => x
  | None => fun impossible => False_rect T (Bool.diff_false_true impossible)
  end.

Lemma option_value_spec T (v : option T) H :
  v = Some (option_value v H).
Proof. destruct v; [reflexivity|discriminate]. Qed.

Section FiniteDomains.
Variable T : Symbol -> Type.
Variable active : list Symbol.
Variable observed : forall p, option (T p).
Definition entered_domain := filter (fun p => has_value (observed p)) active.
Definition entered_inside : includes (fun p => In p entered_domain)
    (fun p => In p active) :=
  fun p d => proj1 (proj1 (filter_In _ _ _) d).
Definition entered_value : values T (fun p => In p entered_domain) :=
  fun p d => option_value (observed p) (proj2 (proj1 (filter_In _ _ _) d)).

Lemma entered_domain_nodup : NoDup active -> NoDup entered_domain.
Proof. apply NoDup_filter. Qed.

Lemma entered_value_spec p d : observed p = Some (entered_value p d).
Proof. apply option_value_spec. Qed.

Lemma entered_domain_complete p x :
  In p active -> observed p = Some x -> In p entered_domain.
Proof.
  intros Member Obs. apply filter_In. split; [exact Member|].
  now rewrite Obs.
Qed.
End FiniteDomains.

Section ConcreteFamilies.
Context {M E : Type -> Type} {Store : Type}.
Variable model : DeadlockLocal.local_model M E Symbol Store.
Variable configured : list Symbol.

Definition actual_family (A : Symbol -> Type) rs :=
  forall p, In p rs -> @cursor M E p (A p).
Definition actual_at S A (c : programs M A S) rs
    (inc : includes (fun p => In p rs) S) o (cuts : actual_family A rs) :=
  forall p d, syntax_cut model configured p (A p) o (c p (inc p d)) (cuts p d).
Definition actual_returned A active completed
    (done : includes (fun p => In p completed) (fun p => In p active))
    (cuts : actual_family A active) (v : values A (fun p => In p completed)) :=
  forall p d, cut_returned p (cuts p (done p d)) (v p d).

Theorem replay_app_actual S A B
    (f : programs M (fun p => A p -> B p) S) (x : programs M A S)
    active inc o (cuts : actual_family B active) :
  NoDup active ->
  actual_at S B (fun p s => App (f p s) (x p s)) active inc o cuts ->
  exists (fs : actual_family (fun p => A p -> B p) active)
      (xs : actual_family A active),
    actual_at S _ f active inc (child o AppFunction) fs /\
    actual_at S _ x active inc (child o AppArgument) xs /\
    forall p d v, cut_returned p (cuts p d) v ->
      exists g a, cut_returned p (fs p d) g /\
        cut_returned p (xs p d) a /\ v = g a.
Proof.
  intros ND At.
  destruct (@select_returned
    (fun p => (@cursor M E p (A p -> B p) * @cursor M E p (A p))%type)
    (fun p pair => forall d : In p active,
      syntax_cut model configured p _ (child o AppFunction)
        (f p (inc p d)) (let '(cf,cx) := pair in cf) /\
      syntax_cut model configured p _ (child o AppArgument)
        (x p (inc p d)) (let '(cf,cx) := pair in cx) /\
      forall v, cut_returned p (cuts p d) v ->
        exists g a, cut_returned p (let '(cf,cx) := pair in cf) g /\
          cut_returned p (let '(cf,cx) := pair in cx) a /\ v = g a) active)
    as (parts & Valid).
  - intros p d.
    destruct (app_cut_children model configured p _ _ _ _ _ _ (At p d))
      as (cf & cx & F & X & Return).
    exists (cf,cx). intro e.
    rewrite <- (roster_member_unique active ND p d e).
    exact (conj F (conj X Return)).
  - exists (fun p d => let '(cf,cx) := parts p d in cf),
      (fun p d => let '(cf,cx) := parts p d in cx).
    split; [intros p d; exact (proj1 (Valid p d d))|].
    split; [intros p d; exact (proj1 (proj2 (Valid p d d)))|].
    intros p d. exact (proj2 (proj2 (Valid p d d))).
Qed.

Theorem replay_bind_actual S A B (t : programs M A S)
    (k : forall p, S p -> A p -> Choreo M p (B p))
    active completed inc o (cuts : actual_family B active)
    (done : includes (fun p => In p completed) (fun p => In p active))
    (v : values B (fun p => In p completed)) :
  NoDup active -> NoDup completed ->
  actual_at S B (fun p s => Bind (t p s) (k p s)) active inc o cuts ->
  actual_returned B active completed done cuts v ->
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (finished : includes (fun p => In p completed) (fun p => In p entered))
    (prefix : actual_family A active)
    (x : values A (fun p => In p entered))
    (body : actual_family B entered),
    NoDup entered /\
    actual_at S A t active inc (child o BindPrefix) prefix /\
    actual_returned A active entered inside prefix x /\
    (forall p d, syntax_cut model configured p _ (child o BindBody)
      (k p (inc p (inside p d)) (x p d)) (body p d)) /\
    actual_returned B entered completed finished body v.
Proof.
  intros NA NC At Ret.
  destruct (@select_returned
    (fun p => (@cursor M E p (A p) *
      option (A p * @cursor M E p (B p)))%type)
    (fun p pair => forall d : In p active,
      let '(pre,entry) := pair in
      syntax_cut model configured p _ (child o BindPrefix)
        (t p (inc p d)) pre /\
      match entry with
      | None => cuts p d = Code o (Bind (t p (inc p d)) (k p (inc p d))) \/
          cuts p d = Seq o pre (k p (inc p d))
      | Some (a,b) => pre = Returned a /\
          syntax_cut model configured p _ (child o BindBody)
            (k p (inc p d) a) b /\ cuts p d = b
      end) active) as (parts & Valid).
  - intros p d.
    destruct (bind_cut_prefix model configured p _ _ _ _ _ _ (At p d))
      as (pre & Prefix & [Outside|(a & b & Eq & Body & End)]).
    + exists (pre,None). intro e.
      rewrite <- (roster_member_unique active NA p d e).
      exact (conj Prefix Outside).
    + exists (pre,Some (a,b)). intro e.
      rewrite <- (roster_member_unique active NA p d e).
      exact (conj Prefix (conj Eq (conj Body End))).
  - set (obs := fun p =>
      match in_dec (List.list_eq_dec BinNat.N.eq_dec) p active with
      | left d => let '(pre,entry) := parts p d in entry
      | right _ => None
      end).
    assert (Observed : forall p d, obs p =
      (let '(pre,entry) := parts p d in entry)).
    { intros p d. unfold obs.
      destruct (in_dec (List.list_eq_dec BinNat.N.eq_dec) p active) as [e|Ne].
      - now rewrite (roster_member_unique active NA p e d).
      - contradiction. }
    set (entered := entered_domain _ active obs).
    set (inside := entered_inside _ active obs).
    set (pair := entered_value _ active obs).
    assert (Entry : forall p d, (let '(pre,entry) := parts p (inside p d) in
      entry)
      = Some (pair p d)).
    { intros p d. rewrite <- Observed.
      exact (entered_value_spec _ active obs p d). }
    assert (Finished : includes (fun p => In p completed) (fun p => In p
      entered)).
    { intros p d.
      pose proof (Valid p (done p d) (done p d)) as H.
      pose proof (Ret p d) as Return.
      pose proof (Observed p (done p d)) as O.
      destruct (parts p (done p d)) as [pre [[a b]|]]; cbn in H,O.
      - eapply entered_domain_complete; [apply done; exact d|exact O].
      - destruct H as [_ [Eq|Eq]]; rewrite Eq in Return; contradiction. }
    exists entered, inside, Finished,
      (fun p d => let '(pre,entry) := parts p d in pre),
      (fun p d => let '(a,b) := pair p d in a),
      (fun p d => let '(a,b) := pair p d in b).
    split; [apply entered_domain_nodup; exact NA|].
    split.
    + intros p d. pose proof (Valid p d d) as H.
      destruct (parts p d) as [pre entry]. exact (proj1 H).
    + assert (Body : forall p d,
        let '(a,b) := pair p d in
        (let '(pre,entry) := parts p (inside p d) in pre) = Returned a /\
        syntax_cut model configured p _ (child o BindBody)
          (k p (inc p (inside p d)) a) b /\ cuts p (inside p d) = b).
      { intros p d. pose proof (Entry p d) as Eq.
        pose proof (Valid p (inside p d) (inside p d)) as H.
        destruct (parts p (inside p d)) as [pre entry].
        cbn in Eq,H. rewrite Eq in H.
        destruct (pair p d) as [a b]. exact (proj2 H). }
      split.
      * intros p d. pose proof (Body p d) as H.
        destruct (pair p d) as [a b].
        destruct (parts p (inside p d)) as [pre entry].
        cbn in H |- *. rewrite (proj1 H). reflexivity.
      * split.
        -- intros p d. pose proof (Body p d) as H.
           destruct (pair p d) as [a b]. exact (proj1 (proj2 H)).
        -- intros p d. pose proof (Body p (Finished p d)) as H.
           destruct (pair p (Finished p d)) as [a b].
           cbn in H |- *.
           rewrite <- (proj2 (proj2 H)).
           rewrite (roster_member_unique active NA p
             (inside p (Finished p d)) (done p d)).
           apply Ret.
Qed.

Theorem replay_cond_actual S X l A
    (sh : forall p, S p -> Parkour.Codec.Show X)
    (rd : forall p, S p -> Parkour.Codec.Read X)
    (input : values (fun p => At X l p) S)
    (k : forall p, S p -> X -> Choreo M p (A p))
    active completed inc o (cuts : actual_family A active)
    (done : includes (fun p => In p completed) (fun p => In p active))
    (v : values A (fun p => In p completed)) :
  NoDup active -> NoDup completed ->
  actual_at S A (fun p s => Perf (@Cond M p X l (A p)
    (sh p s) (rd p s) (known l) MkSSymbol (input p s) (k p s)))
    active inc o cuts ->
  actual_returned A active completed done cuts v ->
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (finished : includes (fun p => In p completed) (fun p => In p entered))
    (choices : values (fun _ => X) (fun p => In p entered))
    (body : actual_family A entered),
    NoDup entered /\
    (forall p d, exists s q a s' q',
      ((exists same : l = p, choices p d = unAt (input p (inc p (inside p d)))
        same /\
          a = AnnounceAction X o p (choices p d)) \/
       (l <> p /\ a = HearAction X o l p (choices p d))) /\
      primitive_action model configured (A p)
        (Code o (Perf (@Cond M p X l (A p) (sh p (inc p (inside p d)))
          (rd p (inc p (inside p d))) (known l) MkSSymbol
          (input p (inc p (inside p d))) (k p (inc p (inside p d))))))
        s q a (Code (child o ChoiceBody) (k p (inc p (inside p d)) (choices p
          d)))
        s' q') /\
    (forall p d, syntax_cut model configured p _ (child o ChoiceBody)
      (k p (inc p (inside p d)) (choices p d)) (body p d)) /\
    actual_returned A entered completed finished body v.
Proof.
  intros NA NC At Ret.
  set (head := fun p s => Perf (@Cond M p X l (A p)
    (sh p s) (rd p s) (known l) MkSSymbol (input p s) (k p s))).
  destruct (@select_returned
    (fun p => option (X * @cursor M E p (A p))%type)
    (fun p entry => forall d : In p active,
      match entry with
      | None => cuts p d = Code o (head p (inc p d))
      | Some (x,b) =>
          (exists s q a s' q',
            ((exists same : l = p, x = unAt (input p (inc p d)) same /\
                a = AnnounceAction X o p x) \/
             (l <> p /\ a = HearAction X o l p x)) /\
            primitive_action model configured (A p) (Code o (head p (inc p d)))
              s q a (Code (child o ChoiceBody) (k p (inc p d) x)) s' q') /\
          syntax_cut model configured p _ (child o ChoiceBody) (k p (inc p d) x)
            b /\
          cuts p d = b
      end) active) as (parts & Valid).
  - intros p d.
    destruct (syntax_cut_decomposition model configured p _ _ _ _ (At p d))
      as [Initial|(x & b & s & q & a & s' & q' & Sel & Step & Body & End)].
    + exists None. intro e.
      rewrite <- (roster_member_unique active NA p d e). exact Initial.
    + exists (Some (x,b)). intro e.
      rewrite <- (roster_member_unique active NA p d e).
      split; [exists s,q,a,s',q'; split; assumption|].
      split; assumption.
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
    set (pair := entered_value _ active obs).
    assert (Entry : forall p d, parts p (inside p d) = Some (pair p d)).
    { intros p d. rewrite <- Observed.
      exact (entered_value_spec _ active obs p d). }
    assert (Finished : includes (fun p => In p completed) (fun p => In p
      entered)).
    { intros p d.
      pose proof (Valid p (done p d) (done p d)) as H.
      pose proof (Ret p d) as Return.
      pose proof (Observed p (done p d)) as O.
      destruct (parts p (done p d)) as [[x b]|]; cbn in H,O.
      - eapply entered_domain_complete; [apply done; exact d|exact O].
      - rewrite H in Return. contradiction. }
    exists entered, inside, Finished,
      (fun p d => let '(x,b) := pair p d in x),
      (fun p d => let '(x,b) := pair p d in b).
    split; [apply entered_domain_nodup; exact NA|].
    assert (Body : forall p d,
      let '(x,b) := pair p d in
      (exists s q a s' q',
        ((exists same : l = p, x = unAt (input p (inc p (inside p d))) same /\
            a = AnnounceAction X o p x) \/
         (l <> p /\ a = HearAction X o l p x)) /\
        primitive_action model configured (A p)
          (Code o (head p (inc p (inside p d))))
          s q a (Code (child o ChoiceBody) (k p (inc p (inside p d)) x)) s' q')
            /\
      syntax_cut model configured p _ (child o ChoiceBody)
        (k p (inc p (inside p d)) x) b /\ cuts p (inside p d) = b).
    { intros p d. pose proof (Valid p (inside p d) (inside p d)) as H.
      rewrite Entry in H. destruct (pair p d) as [x b]. exact H. }
    split.
    + intros p d. pose proof (Body p d) as H.
      destruct (pair p d) as [x b]. exact (proj1 H).
    + split.
      * intros p d. pose proof (Body p d) as H.
        destruct (pair p d) as [x b]. exact (proj1 (proj2 H)).
      * intros p d. pose proof (Body p (Finished p d)) as H.
        destruct (pair p (Finished p d)) as [x b]. cbn in H |- *.
        rewrite <- (proj2 (proj2 H)).
        rewrite (roster_member_unique active NA p
          (inside p (Finished p d)) (done p d)).
        apply Ret.
Qed.

End ConcreteFamilies.

Print Assumptions replay_app_actual.
Print Assumptions replay_bind_actual.
Print Assumptions replay_cond_actual.
Print Assumptions archived_cut_actual_syntax.
