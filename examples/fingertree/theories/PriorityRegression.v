Require Import Data.PriorityQueue.FingerTree.
From Stdlib Require Import Lists.List.
Import ListNotations.

Module Queue := Data.PriorityQueue.FingerTree.

(* The public empty equation must not require an inhabitant of either type. *)
Lemma minViewWithKey_empty {K V : Type} `{GHC.Base.Ord K} :
  Queue.minViewWithKey (Queue.empty : Queue.PQueue K V) = None.
Proof. cbv. reflexivity. Qed.

Check @minViewWithKey_empty.
Print Assumptions minViewWithKey_empty.

Lemma minView_empty {K V : Type} `{GHC.Base.Ord K} :
  Queue.minView (Queue.empty : Queue.PQueue K V) = None.
Proof. unfold Queue.minView. rewrite minViewWithKey_empty. reflexivity. Qed.

Check @minView_empty.
Print Assumptions minView_empty.

(* Empty_set has no Default element. Both public observations still reduce. *)
Lemma empty_payload_views :
  Queue.minViewWithKey (Queue.empty : Queue.PQueue bool Empty_set) = None /\
  Queue.minView (Queue.empty : Queue.PQueue bool Empty_set) = None.
Proof. split; [apply minViewWithKey_empty | apply minView_empty]. Qed.

Check empty_payload_views.
Print Assumptions empty_payload_views.

Lemma minViewWithKey_singleton {K V : Type} `{GHC.Base.Ord K} (k : K) (v : V)
  (refl_le : GHC.Base.op_zlze__ k k = true) :
  Queue.minViewWithKey (Queue.singleton k v) =
    Some ((k, v), (Queue.empty : Queue.PQueue K V)).
Proof.
  cbn.
  rewrite refl_le.
  reflexivity.
Qed.

Check @minViewWithKey_singleton.
Print Assumptions minViewWithKey_singleton.

(* The minimum lies inside the insertion order, so split leaves entries on
   both sides. Equal-priority entries have distinct payloads; repeated public
   views check their order and retain both sides of the reappend. No deferred
   Foldable/assocs unfolding is needed for this finite observation. *)
Lemma minViewWithKey_priority_payload_ties_reappend :
  let q := Queue.add true 30
             (Queue.add false 21
               (Queue.add false 20 (Queue.singleton true 10))) in
  match Queue.minViewWithKey q with
  | Some (a, q1) =>
    match Queue.minViewWithKey q1 with
    | Some (b, q2) =>
      match Queue.minViewWithKey q2 with
      | Some (c, q3) =>
        match Queue.minViewWithKey q3 with
        | Some (d, q4) =>
            Some ([a; b; c; d], Queue.null q4,
                  option_map fst (Queue.minViewWithKey q4))
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None => None
  end = Some ([(false, 20); (false, 21); (true, 10); (true, 30)], true, None).
Proof. reflexivity. Qed.

Check minViewWithKey_priority_payload_ties_reappend.
Print Assumptions minViewWithKey_priority_payload_ties_reappend.
