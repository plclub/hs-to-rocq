Require Import Coq.Lists.List Coq.Arith.Wf_nat Coq.micromega.Lia.
Local Obligation Tactic := idtac.
Ltac solve_local_measured :=
  Coq.Program.Tactics.program_simpl;
  solve [apply lt_wf | simpl; Lia.lia].

Ltac solve_local_split parts :=
  Coq.Program.Tactics.program_simpl;
  try solve [apply lt_wf];
  repeat match goal with
  | H : ?split ?xs = pair ?l ?r |- _ =>
      let Hlen := fresh "Hlen" in
      pose proof (parts _ xs) as Hlen;
      rewrite H in Hlen; cbn in Hlen; clear H
  | H : pair ?l ?r = ?split ?xs |- _ =>
      let Hlen := fresh "Hlen" in
      pose proof (parts _ xs) as Hlen;
      rewrite <- H in Hlen; cbn in Hlen; clear H
  end;
  cbn in *; Lia.lia.

Ltac destruct_accessibility :=
  repeat match goal with
  | |- context[?acc] =>
      match type of acc with
      | Acc _ _ => destruct acc; cbn
      end
  end.

Declare Scope inline_list_scope.
Delimit Scope inline_list_scope with inline_list.
Notation "'identity_step'" := (fun xs => xs) : inline_list_scope.
