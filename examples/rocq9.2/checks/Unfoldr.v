(* This checks the generated source definition, not a replacement algorithm.
   The unfolding proof uses only the existing guarded DeferredFix interface. *)
Require Data.OldList.
Require HsToRocq.DeferredFix.
From Stdlib Require Import Arith.Wf_nat Arith.PeanoNat.

(* In particular, neither the seed nor the element type requires Default. *)
Check (@Data.OldList.unfoldr) :
  forall (b a : Type), (b -> option (a * b)%type) -> b -> list a.
Print Assumptions Data.OldList.unfoldr.

Lemma unfoldr_rank_eq {B A : Type}
  (f : B -> option (A * B)%type) (rank : B -> nat)
  (decreases : forall b a b', f b = Some (a, b') -> rank b' < rank b)
  (b : B) :
  Data.OldList.unfoldr f b =
    match f b with
    | Some (a, b') => cons a (Data.OldList.unfoldr f b')
    | None => nil
    end.
Proof.
  unfold Data.OldList.unfoldr, HsToRocq.DeferredFix.deferredFix1.
  cbn beta zeta.
  (* Take the functional directly from the generated definition. *)
  match goal with
  | |- @HsToRocq.DeferredFix.deferredFix _ _ ?d ?body _ = _ =>
      apply (@HsToRocq.DeferredFix.deferredFix_eq_on B (list A) d body
        (fun _ => True) (ltof B rank))
  end.
  - apply well_founded_ltof.
  - intros g h x _ agree.
    destruct (f x) as [[a b']|] eqn:step; [|reflexivity].
    f_equal. apply agree; [exact I|].
    apply (decreases x a b' step).
  - exact I.
Qed.

(* A finite producer: the seed 3 emits 2, then 1, then 0, then stops. *)
Definition countdown_step (n : nat) : option (nat * nat)%type :=
  match n with
  | O => None
  | S n' => Some (n', n')
  end.

Lemma countdown_decreases :
  forall n a n', countdown_step n = Some (a, n') -> n' < n.
Proof.
  intros [|n] a n' step; [discriminate|].
  inversion step; subst. apply Nat.lt_succ_diag_r.
Qed.

Example unfoldr_countdown_three :
  Data.OldList.unfoldr countdown_step 3 = cons 2 (cons 1 (cons 0 nil)).
Proof.
  rewrite (unfoldr_rank_eq countdown_step (fun n => n) countdown_decreases 3).
  cbn [countdown_step].
  rewrite (unfoldr_rank_eq countdown_step (fun n => n) countdown_decreases 2).
  cbn [countdown_step].
  rewrite (unfoldr_rank_eq countdown_step (fun n => n) countdown_decreases 1).
  cbn [countdown_step].
  rewrite (unfoldr_rank_eq countdown_step (fun n => n) countdown_decreases 0).
  reflexivity.
Qed.

Check @unfoldr_rank_eq.
Print Assumptions unfoldr_rank_eq.
Check countdown_decreases.
Print Assumptions countdown_decreases.
Check unfoldr_countdown_three.
Print Assumptions unfoldr_countdown_three.
