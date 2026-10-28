Require Import Coq.Arith.Wf_nat.
Require Import Lia.

Definition shorter (xs ys : list bool) : Prop := length xs < length ys.

Lemma shorter_well_founded : well_founded shorter.
Proof. exact (well_founded_ltof _ (@length bool)). Defined.

(* Prove both decreasing calls and well-foundedness, including measure pullback. *)
Ltac solve_shorter copy_length :=
  Coq.Program.Tactics.program_simpl;
  solve [exact shorter_well_founded |
         apply Coq.Program.Wf.measure_wf; exact shorter_well_founded |
         unfold shorter; rewrite !copy_length; simpl; lia].
