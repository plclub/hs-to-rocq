From Stdlib Require Import micromega.Lia.
Require Import FingerTreeProofs.CoreSize.

Local Obligation Tactic := idtac.

Definition interval_measure {v : Type} {a : Type}
  (as_ bs : Data.FingerTree.FingerTree (IntInterval v) (Node v a)) : nat :=
  size as_ + size bs.

Ltac interval_identity_do tac :=
  match goal with
  | Hord : GHC.Base.Ord ?vv |- _ =>
      let Hid := open_constr:(fun x : IntInterval vv =>
        match x as x0 return
          @GHC.Base.mappend (IntInterval vv)
            ltac:(typeclasses eauto) ltac:(typeclasses eauto) x0
            (@GHC.Base.mempty (IntInterval vv)
              ltac:(typeclasses eauto) ltac:(typeclasses eauto)) = x0 with
        | NoInterval => eq_refl
        | MkIntInterval i h => eq_refl
        end) in
      pose proof Hid as Hid_proof;
      tac Hid_proof
  end.

Ltac interval_union_decrease_with Hid_proof :=
  unfold interval_measure in *;
  match goal with
  | Hv0 : (Data.FingerTree.op_ZCzl__ ?x0 ?r0) = ?fv0,
    Hs0 : (?l0, ?r0') = ?fv1,
    Hv2 : (Data.FingerTree.op_ZCzl__ ?x2 ?r2) = ?fv2,
    Hs : (?l, ?r) = ?fv3 |- _ =>
      unfold fv0 in Hv0; symmetry in Hv0;
      pose proof (viewl_size_lt _ _ x0 r0 Hv0) as Hview_as;
      unfold fv1 in Hs0; symmetry in Hs0;
      pose proof (split_size_bounds Hid_proof _ _ _ l0 r0' Hs0)
        as Hsplit_bs;
      unfold fv2 in Hv2; symmetry in Hv2;
      pose proof (viewl_size_lt _ _ x2 r2 Hv2) as Hview_r0;
      unfold fv3 in Hs; symmetry in Hs;
      pose proof (split_size_bounds Hid_proof _ _ _ l r Hs)
        as Hsplit_as;
      lia
  end.

Ltac interval_union_decrease :=
  interval_identity_do interval_union_decrease_with.

Ltac interval_union_termination :=
  intros;
  match goal with
  | |- well_founded _ => apply PeanoNat.Nat.lt_wf_0
  | _ => interval_union_decrease
  end.

Ltac interval_inRange_decrease_with Hid_proof :=
  unfold interval_measure in *;
  match goal with
  | Hv : (Data.FingerTree.op_ZCzl__ ?x ?r) = ?fv |- _ =>
      unfold fv in Hv;
      pose proof (viewl_size_lt _ _ x r (eq_sym Hv)) as Hview;
      match type of Hv with
      | _ = Data.FingerTree.viewl (Data.FingerTree.dropUntil ?p ?t) =>
          pose proof (dropUntil_size_le Hid_proof _ p t) as Hdrop
      end;
      lia
  end.

Ltac interval_inRange_decrease :=
  interval_identity_do interval_inRange_decrease_with.

Ltac interval_inRange_termination :=
  intros;
  match goal with
  | |- well_founded _ => apply PeanoNat.Nat.lt_wf_0
  | _ => interval_inRange_decrease
  end.
