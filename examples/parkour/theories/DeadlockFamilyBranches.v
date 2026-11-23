From Stdlib Require Import Lists.List.
Require Import DeadlockFamilyLog DeadlockPlayedFamily DeadlockLogDecompose
  DeadlockLogScope DeadlockLocalLog DeadlockChronology DeadlockSource
  DeadlockLocal DeadlockCoherence DeadlockObservedCut DeadlockPlayedValues
  DeadlockPartialValues DeadlockState DeadlockWellFormed Parkour.Symbol
  Choreography.Choreo2 Control.Monad.Tree.
Import ListNotations.
Set Universe Polymorphism.

Definition branch_fst {U V : Type} (pair : U * V) : U :=
  match pair with (x,_) => x end.
Definition branch_snd {U V : Type} (pair : U * V) : V :=
  match pair with (_,y) => y end.
Local Notation fst := branch_fst.
Local Notation snd := branch_snd.

Lemma branch_pair_eta {U V : Type} (pair : U * V) :
  pair = (fst pair, snd pair).
Proof. destruct pair; reflexivity. Qed.

(* select_returned is monomorphic in its value universe. The finite proof
   below also permits archived entries, whose types quantify over cursors. *)
Lemma select_branch_cuts (T : Symbol -> Type) (P : forall p, T p -> Prop) rs :
  (forall p, In p rs -> exists x : T p, P p x) ->
  exists v : values T (fun p => In p rs), forall p d, P p (v p d).
Proof.
  induction rs as [|r rs IH]; intro Witness.
  - exists (fun p (d : False) => False_rect (T p) d).
    intros p d; contradiction.
  - destruct (Witness r (or_introl eq_refl)) as [x Px].
    destruct IH as [v Pv].
    { intros p d. apply Witness. now right. }
    assert (tail_member : forall p, r <> p -> In p (r :: rs) -> In p rs).
    { intros p Ne [Eq|Member]; [contradiction|exact Member]. }
    set (all := fun p (d : In p (r :: rs)) =>
      match List.list_eq_dec BinNat.N.eq_dec r p with
      | left e => eq_rect r T x p e
      | right ne => v p (tail_member p ne d)
      end).
    exists all. intros p d. unfold all.
    destruct (List.list_eq_dec BinNat.N.eq_dec r p) as [e|ne].
    + destruct e. exact Px.
    + apply Pv.
Qed.

Lemma sibling_regions_disjoint o a b z :
  a <> b -> extends (child o a) z -> extends (child o b) z -> False.
Proof.
  intros Ne [u E] [v F]. rewrite E in F.
  unfold child in F. rewrite <- !app_assoc in F.
  apply app_inv_head in F. injection F as Eq _. contradiction.
Qed.

Definition option_present {T} (v : option T) : bool :=
  match v with Some _ => true | None => false end.

Definition present_payload {T} (v : option T) : v <> None -> T :=
  match v as w return w <> None -> T with
  | Some x => fun _ => x
  | None => fun H => False_rect T (H eq_refl)
  end.

Lemma present_payload_eq {T} (v : option T) (H : v <> None) :
  v = Some (present_payload v H).
Proof. destruct v; [reflexivity|contradiction]. Qed.

Section Branches.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol)
  (A : Symbol -> Type) (c : forall p, Choreo M p (A p)).
Local Notation cut := (logged_cut model stores input R A c).
Local Notation entry := (observed_entry model stores input R A c).
Local Notation log := (actor_log model stores input R A c).
Local Notation site := (entry_site model stores input R A c).
Local Notation stamp := (stamped model stores input R A c).
Local Notation sm := (shared_model model).
Variable past : list payload_event.
Variable ar : actor_archive model stores input R A c.
Local Notation node := (at_node model stores input R A c past).
Local Notation ret := (finished model stores input R A c).
Local Notation good := (owns_region model stores input R A c ar).
Local Notation region := (in_region model stores input R A c ar).

Lemma log_entry_scope p B o code tr t e :
  log p B (Code o code) tr t -> In e tr -> extends o (site p e).
Proof.
  intros Run Member.
  pose proof (proj1 (actor_log_scope model stores input R A c p B o code tr t Run)) as Scope.
  clear Run.
  induction Scope as [|a tr Ha Htr IH]; [contradiction|].
  destruct Member as [<-|Member]; [exact Ha|now apply IH].
Qed.

Local Arguments cursor_at {M E Store Input model stores input R A c p B} _.
Local Arguments tokens {M E Store Input model stores input R A c p B} _.
Local Arguments LoggedCut {M E Store Input model stores input R A c p B} _ _.

Definition app_cursor_shape p X Y o (f : Choreo M p (X -> Y))
    (x : Choreo M p X) (parent : cut p Y)
    (fc : cut p (X -> Y)) (xc : cut p X) :=
  (cursor_at parent = Code o (App f x) /\
   cursor_at fc = Code (child o AppFunction) f /\
   cursor_at xc = Code (child o AppArgument) x) \/
  cursor_at parent = Fork (cursor_at fc) (cursor_at xc) \/
  exists g a,
    cursor_at fc = Returned g /\
    cursor_at xc = Returned a /\
    cursor_at parent = Returned (g a).

Lemma app_local_children p X Y o (f : Choreo M p (X -> Y))
    (x : Choreo M p X) (parent : cut p Y) :
  node p Y o (App f x) parent ->
  exists (fc : cut p (X -> Y)) (xc : cut p X),
    node p (X -> Y) (child o AppFunction) f fc /\
    node p X (child o AppArgument) x xc /\
    (forall e, In e (tokens parent) <->
      In e (tokens fc) \/ In e (tokens xc)) /\
    app_cursor_shape p X Y o f x parent fc xc.
Proof.
  intros [Run Stamps].
  destruct (local_log_app_cases sm p (entry p) (stamp p)
    (stamped_primitive_cursor model stores input R A c p) X Y o f x
    (tokens parent) (cursor_at parent) Run)
    as [[Empty Shape]|[(fl & xl & cf & cx & F & Xr & Shuffle & Shape)|
      (fl & xl & g & a & F & Xr & Shuffle & Shape)]].
  - exists (LoggedCut (Code (child o AppFunction) f) []),
      (LoggedCut (Code (child o AppArgument) x) []).
    split; [split; [constructor|intros e H; contradiction]|].
    split; [split; [constructor|intros e H; contradiction]|].
    split.
    + intros e. rewrite Empty. cbn. tauto.
    + left. repeat split; try exact Shape; reflexivity.
  - exists (LoggedCut cf fl), (LoggedCut cx xl).
    assert (Part := log_shuffle_member _ _ _ Shuffle).
    split; [split; [exact F|intros e Member; apply Stamps, Part; now left]|].
    split; [split; [exact Xr|intros e Member; apply Stamps, Part; now right]|].
    split; [exact Part|]. right; left; exact Shape.
  - exists (LoggedCut (Returned g) fl), (LoggedCut (Returned a) xl).
    assert (Part := log_shuffle_member _ _ _ Shuffle).
    split; [split; [exact F|intros e Member; apply Stamps, Part; now left]|].
    split; [split; [exact Xr|intros e Member; apply Stamps, Part; now right]|].
    split; [exact Part|]. right; right. exists g,a. auto.
Qed.

Lemma app_children_return p X Y o f x parent fc xc :
  @app_cursor_shape p X Y o f x parent fc xc ->
  forall v, ret p Y parent v ->
    exists g a, ret p (X -> Y) fc g /\ ret p X xc a /\ v = g a.
Proof.
  intros [[Parent _]|[Parent|(g & a & F & Xr & Parent)]] v Return;
    unfold finished in *; rewrite Parent in Return; cbn in Return;
    try contradiction.
  exists g,a. rewrite F, Xr. cbn. auto.
Qed.

Lemma app_child_regions p X Y o f x (parent : cut p Y)
    (fc : cut p (X -> Y)) (xc : cut p X) :
  node p _ (child o AppFunction) f fc ->
  node p _ (child o AppArgument) x xc ->
  (forall e, In e (tokens parent) <->
    In e (tokens fc) \/ In e (tokens xc)) ->
  (forall e, In e (tokens parent) <-> region p o e) ->
  (forall e, In e (tokens fc) <-> region p (child o AppFunction) e) /\
  (forall e, In e (tokens xc) <-> region p (child o AppArgument) e).
Proof.
  intros [F _] [Xr _] Part Exact.
  assert (FS : forall e, In e (tokens fc) -> extends (child o AppFunction) (site p e)).
  { intros; eapply log_entry_scope; eassumption. }
  assert (XS : forall e, In e (tokens xc) -> extends (child o AppArgument) (site p e)).
  { intros; eapply log_entry_scope; eassumption. }
  split; intros e; split.
  - intro H. split; [apply (proj1 (Exact e)), Part; now left|now apply FS].
  - intros [Seen Scope].
    assert (H : In e (tokens parent)).
    { apply Exact. split; [exact Seen|now apply extends_child in Scope]. }
    apply Part in H as [H|H]; [exact H|].
    exfalso; eapply (sibling_regions_disjoint o AppFunction AppArgument);
      [discriminate|exact Scope|now apply XS].
  - intro H. split; [apply (proj1 (Exact e)), Part; now right|now apply XS].
  - intros [Seen Scope].
    assert (H : In e (tokens parent)).
    { apply Exact. split; [exact Seen|now apply extends_child in Scope]. }
    apply Part in H as [H|H]; [|exact H].
    exfalso; eapply (sibling_regions_disjoint o AppArgument AppFunction);
      [discriminate|exact Scope|now apply FS].
Qed.

Lemma logged_replay_app_partition S F B
    (f : programs M (fun p => F p -> B p) S) (x : programs M F S)
    active inc o (cuts : family cut B active) :
  good B active o cuts ->
  family_at cut node S B (fun p s => App (f p s) (x p s)) active inc o cuts ->
  exists (fs : family cut (fun p => F p -> B p) active)
    (xs : family cut F active),
    good _ active (child o AppFunction) fs /\
    good _ active (child o AppArgument) xs /\
    family_at cut node S _ f active inc (child o AppFunction) fs /\
    family_at cut node S _ x active inc (child o AppArgument) xs /\
    (forall p d, app_cursor_shape p (F p) (B p) o
      (f p (inc p d)) (x p (inc p d)) (cuts p d) (fs p d) (xs p d)) /\
    (forall p d e, In e (tokens (cuts p d)) <->
      In e (tokens (fs p d)) \/ In e (tokens (xs p d))).
Proof.
  intros Good At. destruct Good as [ND [Cover Exact]].
  destruct (@select_branch_cuts
    (fun p => (cut p (F p -> B p) * cut p (F p))%type)
    (fun p pair => forall d : In p active,
      node p _ (child o AppFunction) (f p (inc p d)) (fst pair) /\
      node p _ (child o AppArgument) (x p (inc p d)) (snd pair) /\
      (forall e, In e (tokens (cuts p d)) <->
        In e (tokens (fst pair)) \/ In e (tokens (snd pair))) /\
      app_cursor_shape p (F p) (B p) o (f p (inc p d))
        (x p (inc p d)) (cuts p d) (fst pair) (snd pair)) active)
    as [pairs Valid].
  { intros p d. destruct (app_local_children p _ _ o
      (f p (inc p d)) (x p (inc p d)) (cuts p d) (At p d))
      as (fc & xc & Cert).
    exists (fc,xc). intros e.
    now rewrite <- (roster_member_unique active ND p d e). }
  exists (fun p d => fst (pairs p d)), (fun p d => snd (pairs p d)).
  assert (ChildExact : forall p d,
    (forall e, In e (tokens (fst (pairs p d))) <->
      region p (child o AppFunction) e) /\
    (forall e, In e (tokens (snd (pairs p d))) <->
      region p (child o AppArgument) e)).
  { intros p d. destruct (Valid p d d) as [FAt [XAt [Part Shape]]].
    eapply app_child_regions; eauto. }
  split.
  - split; [exact ND|]. split.
    + intros p e [Seen Scope]. eapply Cover. split; [exact Seen|now apply extends_child in Scope].
    + intros p d. exact (proj1 (ChildExact p d)).
  - split.
    + split; [exact ND|]. split.
      * intros p e [Seen Scope]. eapply Cover. split; [exact Seen|now apply extends_child in Scope].
      * intros p d. exact (proj2 (ChildExact p d)).
    + split; [intros p d; exact (proj1 (Valid p d d))|].
      split; [intros p d; exact (proj1 (proj2 (Valid p d d)))|].
      split.
      * intros p d. exact (proj2 (proj2 (proj2 (Valid p d d)))).
      * intros p d. exact (proj1 (proj2 (proj2 (Valid p d d)))).
Qed.

Lemma logged_replay_app S F B
    (f : programs M (fun p => F p -> B p) S) (x : programs M F S)
    active inc o (cuts : family cut B active) :
  good B active o cuts ->
  family_at cut node S B (fun p s => App (f p s) (x p s)) active inc o cuts ->
  exists (fs : family cut (fun p => F p -> B p) active)
    (xs : family cut F active),
    good _ active (child o AppFunction) fs /\
    good _ active (child o AppArgument) xs /\
    family_at cut node S _ f active inc (child o AppFunction) fs /\
    family_at cut node S _ x active inc (child o AppArgument) xs /\
    (forall p d, app_cursor_shape p (F p) (B p) o
      (f p (inc p d)) (x p (inc p d)) (cuts p d) (fs p d) (xs p d)).
Proof.
  intros Good At.
  destruct (logged_replay_app_partition S F B f x active inc o cuts Good At)
    as (fs & xs & FG & XG & FA & XA & Shape & Partition).
  exists fs,xs. split; [exact FG|]. split; [exact XG|].
  split; [exact FA|]. split; assumption.
Qed.

Definition bind_cursor_shape p X Y o (t : Choreo M p X)
    (k : X -> Choreo M p Y) (parent : cut p Y)
    (prefix : cut p X) (body : option (X * cut p Y)) :=
  match body with
  | None =>
    tokens parent = tokens prefix /\
    ((cursor_at parent = Code o (Bind t k) /\
      cursor_at prefix = Code (child o BindPrefix) t) \/
      cursor_at parent = Seq o (cursor_at prefix) k)
  | Some (x,b) =>
    ret p X prefix x /\ node p Y (child o BindBody) (k x) b /\
    cursor_at parent = cursor_at b /\
    tokens parent = tokens prefix ++ tokens b
  end.

Lemma bind_local_children p X Y o (t : Choreo M p X)
    (k : X -> Choreo M p Y) (parent : cut p Y) :
  node p Y o (Bind t k) parent ->
  exists (prefix : cut p X) (body : option (X * cut p Y)),
    node p X (child o BindPrefix) t prefix /\
    bind_cursor_shape p X Y o t k parent prefix body.
Proof.
  intros [Run Stamps].
  destruct (local_log_bind_cases sm p (entry p) (stamp p)
    (stamped_primitive_cursor model stores input R A c p) X Y o t k
    (tokens parent) (cursor_at parent) Run)
    as [[Empty Shape]|[(ct & Prefix & Shape)|
      (pl & bl & x & Part & Prefix & Body)]].
  - exists (LoggedCut (Code (child o BindPrefix) t) []), None.
    split.
    + split; [constructor|intros e H; contradiction].
    + split; [exact Empty|]. left. auto.
  - exists (LoggedCut ct (tokens parent)), None.
    split; [split; assumption|]. split; [reflexivity|]. now right.
  - exists (LoggedCut (Returned x) pl),
      (Some (x, LoggedCut (cursor_at parent) bl)).
    split.
    + split; [exact Prefix|]. intros e H. apply Stamps. rewrite Part.
      apply in_append_large; now left.
    + split; [reflexivity|]. split.
      * split; [exact Body|]. intros e H. apply Stamps. rewrite Part.
        apply in_append_large; now right.
      * split; [reflexivity|exact Part].
Qed.

Lemma bind_child_regions p X Y o t k (parent : cut p Y)
    (prefix : cut p X) body :
  node p X (child o BindPrefix) t prefix ->
  bind_cursor_shape p X Y o t k parent prefix body ->
  (forall e, In e (tokens parent) <-> region p o e) ->
  (forall e, In e (tokens prefix) <-> region p (child o BindPrefix) e) /\
  match body with
  | None => forall e, ~ region p (child o BindBody) e
  | Some (x,b) => forall e, In e (tokens b) <-> region p (child o BindBody) e
  end.
Proof.
  intros [Prefix _] Shape Exact.
  assert (PS : forall e, In e (tokens prefix) ->
    extends (child o BindPrefix) (site p e)).
  { intros; eapply log_entry_scope; eassumption. }
  destruct body as [[x b]|].
  - destruct Shape as [Returned [[Body _] [Cursor Part]]].
    assert (BS : forall e, In e (tokens b) ->
      extends (child o BindBody) (site p e)).
    { intros; eapply log_entry_scope; eassumption. }
    assert (Partition : forall e, In e (tokens parent) <->
      In e (tokens prefix) \/ In e (tokens b)).
    { intro e. rewrite Part. apply in_append_large. }
    split; intro e; split.
    + intro H. split; [apply (proj1 (Exact e)), Partition; now left|now apply PS].
    + intros [Seen Scope]. assert (Member : In e (tokens parent)).
      { apply Exact. split; [exact Seen|now apply extends_child in Scope]. }
      apply Partition in Member as [H|H]; [exact H|].
      exfalso; eapply (sibling_regions_disjoint o BindPrefix BindBody);
        [discriminate|exact Scope|now apply BS].
    + intro H. split; [apply (proj1 (Exact e)), Partition; now right|now apply BS].
    + intros [Seen Scope]. assert (Member : In e (tokens parent)).
      { apply Exact. split; [exact Seen|now apply extends_child in Scope]. }
      apply Partition in Member as [H|H]; [|exact H].
      exfalso; eapply (sibling_regions_disjoint o BindBody BindPrefix);
        [discriminate|exact Scope|now apply PS].
  - destruct Shape as [Part Shape]. split.
    + intro e. rewrite <- Part. split.
      * intro H. split; [exact (proj1 (proj1 (Exact e) H))|].
        apply PS. now rewrite <- Part.
      * intros [Seen Scope]. apply Exact. split; [exact Seen|now apply extends_child in Scope].
    + intros e [Seen Scope].
      assert (Member : In e (tokens parent)).
      { apply Exact. split; [exact Seen|now apply extends_child in Scope]. }
      rewrite Part in Member.
      eapply (sibling_regions_disjoint o BindBody BindPrefix);
        [discriminate|exact Scope|now apply PS].
Qed.

Lemma bind_finished_entered p X Y o t k (parent : cut p Y)
    (prefix : cut p X) body y :
  bind_cursor_shape p X Y o t k parent prefix body ->
  ret p Y parent y -> body <> None.
Proof.
  destruct body as [[x b]|]; [discriminate|].
  intros [_ [[Shape _]|Shape]] Done; unfold finished in Done;
    rewrite Shape in Done; contradiction.
Qed.

Lemma logged_replay_bind S F B (t : programs M F S)
    (k : forall p, S p -> F p -> Choreo M p (B p))
    active completed inc o (cuts : family cut B active)
    (done : includes (fun p => In p completed) (fun p => In p active))
    (v : values B (fun p => In p completed)) :
  NoDup active -> NoDup completed ->
  good B active o cuts ->
  family_at cut node S B (fun p s => Bind (t p s) (k p s)) active inc o cuts ->
  family_returned cut ret B active completed done cuts v ->
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (completed_inside : includes (fun p => In p completed) (fun p => In p entered))
    (prefix : family cut F active)
    (x : values F (fun p => In p entered))
    (body : family cut B entered),
    NoDup entered /\
    good F active (child o BindPrefix) prefix /\
    family_at cut node S F t active inc (child o BindPrefix) prefix /\
    family_returned cut ret F active entered inside prefix x /\
    good B entered (child o BindBody) body /\
    (forall p d, node p _ (child o BindBody)
      (k p (inc p (inside p d)) (x p d)) (body p d)) /\
    family_returned cut ret B entered completed completed_inside body v /\
    (forall p d,
      (exists e : In p entered, inside p e = d /\
        cursor_at (cuts p d) = cursor_at (body p e)) \/
      (cursor_at (cuts p d) = Code o (Bind (t p (inc p d)) (k p (inc p d))) /\
        cursor_at (prefix p d) = Code (child o BindPrefix) (t p (inc p d))) \/
      cursor_at (cuts p d) = Seq o (cursor_at (prefix p d)) (k p (inc p d))).
Proof.
  intros ND NC [_ [Cover Exact]] At Done.
  destruct (@select_branch_cuts
    (fun p => (cut p (F p) * option (F p * cut p (B p)))%type)
    (fun p pair => forall d : In p active,
      node p _ (child o BindPrefix) (t p (inc p d)) (fst pair) /\
      bind_cursor_shape p (F p) (B p) o (t p (inc p d))
        (k p (inc p d)) (cuts p d) (fst pair) (snd pair)) active)
    as [pairs Valid].
  { intros p d. destruct (bind_local_children p _ _ o
      (t p (inc p d)) (k p (inc p d)) (cuts p d) (At p d))
      as (prefix & body & Cert).
    exists (prefix,body). intro e.
    now rewrite <- (roster_member_unique active ND p d e). }
  set (total := fun p =>
    match in_dec (List.list_eq_dec BinNat.N.eq_dec) p active with
    | left d => snd (pairs p d)
    | right _ => None
    end).
  set (entered := filter (fun p => option_present (total p)) active).
  assert (Entered : forall p,
    In p entered <-> In p active /\ total p <> None).
  { intro p. unfold entered. rewrite filter_In.
    destruct (total p); cbn; intuition discriminate. }
  assert (Selected : forall p d, total p = snd (pairs p d)).
  { intros p d. unfold total.
    destruct (in_dec (List.list_eq_dec BinNat.N.eq_dec) p active) as [e|No].
    - now rewrite (roster_member_unique active ND p e d).
    - contradiction. }
  set (inside := fun p (d : In p entered) => proj1 (proj1 (Entered p) d)).
  set (prefix := fun p d => fst (pairs p d)).
  set (payload := fun p (d : In p entered) =>
    present_payload (total p) (proj2 (proj1 (Entered p) d))).
  set (x := fun p d => fst (payload p d)).
  set (body := fun p d => snd (payload p d)).
  assert (Payload : forall p d,
    snd (pairs p (inside p d)) = Some (x p d, body p d)).
  { intros p d. rewrite <- Selected.
    unfold x, body, payload.
    rewrite <- branch_pair_eta. apply present_payload_eq. }
  assert (Finished : forall p, In p completed -> In p entered).
  { intros p d. apply Entered. split; [exact (done p d)|].
    rewrite (Selected p (done p d)).
    eapply bind_finished_entered.
    - exact (proj2 (Valid p (done p d) (done p d))).
    - apply Done. }
  assert (Regions : forall p d,
    (forall e, In e (tokens (prefix p d)) <->
      region p (child o BindPrefix) e) /\
    match snd (pairs p d) with
    | None => forall e, ~ region p (child o BindBody) e
    | Some (a,b) => forall e, In e (tokens b) <-> region p (child o BindBody) e
    end).
  { intros p d. destruct (Valid p d d) as [Prefix Shape].
    eapply bind_child_regions; eauto. }
  assert (BodyCert : forall p d,
    ret p _ (prefix p (inside p d)) (x p d) /\
    node p _ (child o BindBody) (k p (inc p (inside p d)) (x p d)) (body p d) /\
    cursor_at (cuts p (inside p d)) = cursor_at (body p d) /\
    tokens (cuts p (inside p d)) =
      tokens (prefix p (inside p d)) ++ tokens (body p d)).
  { intros p d. pose proof (proj2 (Valid p (inside p d) (inside p d))) as Cert.
    rewrite (Payload p d) in Cert. exact Cert. }
  exists entered, inside, Finished, prefix, x, body.
  split; [unfold entered; now apply NoDup_filter|].
  split.
  - split; [exact ND|]. split.
    + intros p e [Seen Scope]. eapply Cover.
      split; [exact Seen|now apply extends_child in Scope].
    + intros p d. exact (proj1 (Regions p d)).
  - split; [intros p d; exact (proj1 (Valid p d d))|].
    split; [intros p d; exact (proj1 (BodyCert p d))|].
    split.
    + split; [unfold entered; now apply NoDup_filter|]. split.
      * intros p e [Seen Scope].
        assert (Parent : region p o e).
        { split; [exact Seen|now apply extends_child in Scope]. }
        pose proof (Cover p e Parent) as Present.
        apply Entered. split; [exact Present|].
        rewrite (Selected p Present).
        pose proof (proj2 (Regions p Present)) as Reg.
        destruct (snd (pairs p Present)) as [[a b]|]; [discriminate|].
        exfalso. exact (Reg e (conj Seen Scope)).
      * intros p d. pose proof (proj2 (Regions p (inside p d))) as Reg.
        rewrite (Payload p d) in Reg. exact Reg.
    + split; [intros p d; exact (proj1 (proj2 (BodyCert p d)))|].
      split.
      * intros p d. pose proof (Done p d) as Return.
        rewrite <- (roster_member_unique active ND p
          (inside p (Finished p d)) (done p d)) in Return.
        unfold finished in *.
        rewrite (proj1 (proj2 (proj2 (BodyCert p (Finished p d))))) in Return.
        exact Return.
      * intros p d. pose proof (proj2 (Valid p d d)) as Shape.
        destruct (snd (pairs p d)) as [[a b]|] eqn:Pick.
        -- assert (Member : In p entered).
           { apply Entered. split; [exact d|].
             rewrite (Selected p d), Pick. discriminate. }
           left. exists Member. split; [apply roster_member_unique; exact ND|].
           assert (Eq : inside p Member = d) by (apply roster_member_unique; exact ND).
           rewrite <- Eq. exact (proj1 (proj2 (proj2 (BodyCert p Member)))).
        -- right. exact (proj2 Shape).
Qed.
Corollary concrete_replay_app S F B
    (f : programs M (fun p => F p -> B p) S) (x : programs M F S)
    active inc o (cuts : family cut B active) :
  good B active o cuts ->
  family_at cut node S B (fun p s => App (f p s) (x p s)) active inc o cuts ->
  exists (fs : family cut (fun p => F p -> B p) active)
    (xs : family cut F active),
    good _ active (child o AppFunction) fs /\
    good _ active (child o AppArgument) xs /\
    family_at cut node S _ f active inc (child o AppFunction) fs /\
    family_at cut node S _ x active inc (child o AppArgument) xs /\
    forall p d v, ret p _ (cuts p d) v ->
      exists g a, ret p _ (fs p d) g /\ ret p _ (xs p d) a /\ v = g a.
Proof.
  intros Good At.
  destruct (logged_replay_app S F B f x active inc o cuts Good At)
    as (fs & xs & FG & XG & FA & XA & Shape).
  exists fs,xs. split; [exact FG|]. split; [exact XG|].
  split; [exact FA|]. split; [exact XA|].
  intros p d v. eapply app_children_return. exact (Shape p d).
Qed.

Corollary concrete_replay_bind S F B (t : programs M F S)
    (k : forall p, S p -> F p -> Choreo M p (B p))
    active completed inc o (cuts : family cut B active)
    (done : includes (fun p => In p completed) (fun p => In p active))
    (v : values B (fun p => In p completed)) :
  NoDup active -> NoDup completed ->
  good B active o cuts ->
  family_at cut node S B (fun p s => Bind (t p s) (k p s)) active inc o cuts ->
  family_returned cut ret B active completed done cuts v ->
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (completed_inside : includes (fun p => In p completed) (fun p => In p entered))
    (prefix : family cut F active)
    (x : values F (fun p => In p entered))
    (body : family cut B entered),
    NoDup entered /\
    good F active (child o BindPrefix) prefix /\
    family_at cut node S F t active inc (child o BindPrefix) prefix /\
    family_returned cut ret F active entered inside prefix x /\
    good B entered (child o BindBody) body /\
    (forall p d, node p _ (child o BindBody)
      (k p (inc p (inside p d)) (x p d)) (body p d)) /\
    family_returned cut ret B entered completed completed_inside body v.
Proof.
  intros ND NC Good At Done.
  destruct (logged_replay_bind S F B t k active completed inc o cuts done v
    ND NC Good At Done)
    as (entered & inside & completed_inside & prefix & x & body &
      NE & PG & PA & PR & BG & BA & BR & Shape).
  exists entered,inside,completed_inside,prefix,x,body.
  split; [exact NE|]. split; [exact PG|]. split; [exact PA|].
  split; [exact PR|]. split; [exact BG|]. split; assumption.
Qed.
End Branches.

Print Assumptions logged_replay_app.
Print Assumptions logged_replay_bind.
Print Assumptions concrete_replay_app.
Print Assumptions concrete_replay_bind.
