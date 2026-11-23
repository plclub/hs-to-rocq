From Stdlib Require Import Lists.List.
From ParkourTheories.Choreography Require Import Occurrences.
Import ListNotations.

(* Structural compatibility is a certificate about coexisting ACTION
   positions. It must be established from the common source shape/history;
   arbitrary equal-session paths need not have this property.

   Bind and App themselves are not actions. A Cond action can be an
   ancestor of another action only through ChoiceBody. *)
Inductive compatible : occurrence -> occurrence -> Prop :=
| CompatibleRoots : compatible [] []
| CompatibleUnder e p q : compatible p q -> compatible (e :: p) (e :: q)
| CompatiblePrefixBody p q : compatible (BindPrefix :: p) (BindBody :: q)
| CompatibleBodyPrefix p q : compatible (BindBody :: p) (BindPrefix :: q)
| CompatibleFunctionArgument p q : compatible (AppFunction :: p) (AppArgument ::
  q)
| CompatibleArgumentFunction p q : compatible (AppArgument :: p) (AppFunction ::
  q)
| CompatibleChoiceBody p : compatible [] (ChoiceBody :: p)
| CompatibleBodyChoice p : compatible (ChoiceBody :: p) [].

(* Mandatory structural order, not a scheduler's chosen App interleaving. *)
Inductive source_before : occurrence -> occurrence -> Prop :=
| BeforeBindBody p q : source_before (BindPrefix :: p) (BindBody :: q)
| BeforeChoiceBody p : source_before [] (ChoiceBody :: p)
| BeforeUnder e p q :
    source_before p q -> source_before (e :: p) (e :: q).

Lemma source_before_asymmetric p q :
  source_before p q -> ~ source_before q p.
Proof.
  intro H; induction H as [p q|p|e p q H IH];
    intro Reverse; inversion Reverse; subst.
  now apply IH.
Qed.

Lemma source_before_irreflexive p : ~ source_before p p.
Proof.
  intro H; exact (source_before_asymmetric p p H H).
Qed.

Lemma source_before_transitive p q r :
  source_before p q -> source_before q r -> source_before p r.
Proof.
  intro H; revert r; induction H as [p q|p|e p q H IH];
    intros r Next; inversion Next; subst; try constructor.
  now apply IH.
Qed.

Lemma compatible_reflexive p : compatible p p.
Proof.
  induction p as [|e p IH]; constructor; assumption.
Qed.

Lemma compatible_symmetric p q : compatible p q -> compatible q p.
Proof.
  intro H; induction H; constructor; assumption.
Qed.

Lemma compatible_context prefix p q :
  compatible p q -> compatible (prefix ++ p) (prefix ++ q).
Proof.
  intro H; induction prefix as [|e prefix IH]; cbn; [exact H|].
  now constructor.
Qed.

Lemma source_before_context prefix p q :
  source_before p q -> source_before (prefix ++ p) (prefix ++ q).
Proof.
  intro H; induction prefix as [|e prefix IH]; cbn; [exact H|].
  now constructor.
Qed.

Lemma source_lane_cancel e p q :
  source_lane (e :: p) = source_lane (e :: q) ->
  source_lane p = source_lane q.
Proof.
  destruct e; cbn; intro E; try exact E; now injection E.
Qed.

Theorem equal_lane_order p q :
  compatible p q -> source_lane p = source_lane q ->
  p = q \/ source_before p q \/ source_before q p.
Proof.
  intro C; induction C; intro E.
  - now left.
  - apply source_lane_cancel in E.
    destruct (IHC E) as [->|[H|H]].
    + now left.
    + right; left; now constructor.
    + right; right; now constructor.
  - right; left; constructor.
  - right; right; constructor.
  - discriminate E.
  - discriminate E.
  - right; left; constructor.
  - right; right; constructor.
Qed.

(* Ranks describe finite history positions only. Requiring a natural-valued
   ranking of EVERY syntax position would be impossible: arbitrarily many
   ChoiceBody descendants in a Bind prefix precede its fixed body. *)
Definition respects (events : list occurrence) (rank : occurrence -> nat) :=
  forall p q, In p events -> In q events ->
    source_before p q -> rank p < rank q.
