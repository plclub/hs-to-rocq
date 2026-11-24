Require Import Stdlib.Program.Program HsToRocq.Err.
(* Program conditionals currently use this relative compatibility path. *)
Module Bool.
  Module Sumbool := Corelib.Init.Sumbool.
End Bool.
Local Obligation Tactic := idtac.

#[local] Instance DefaultFingerTree {v a} : Default (FingerTree v a) :=
  {| default := Empty |}.
#[local] Instance DefaultSplit {t a} `{Default t} `{Default a} : Default (Split t a) :=
  {| default := MkSplit default default default |}.
#[local] Instance DefaultNode {v a} `{GHC.Base.Monoid v} `{Default a}
  : Default (Node v a) :=
  {| default := Node2 GHC.Base.mempty default default |}.

Ltac core_inhabitant :=
  program_simpl;
  match goal with
  | |- Default ?a =>
      match goal with
      | x : a |- _ => exact (Build_Default _ x)
      | t : FingerTree _ a |- _ =>
          destruct t;
          [ cbn in *;
            first [congruence |
              match goal with
              | h : andb (negb ?b) ?b = true |- _ => destruct b; discriminate
              end |
              match goal with
              | h : forall wildcard, ~ (wildcard = ?p /\ _) |- _ =>
                  exfalso; apply (h p); split; reflexivity
              end]
          | constructor; assumption
          | match goal with
            | d : Digit a |- _ => destruct d; constructor; assumption
            end ]
      end
  end.
