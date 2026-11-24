(* A direct axiom, its transitive dependency, and an independent closed proof. *)
Axiom rogue : True.
Lemma witness : True. exact rogue. Qed.
Lemma dependent_witness : True. exact witness. Qed.
Lemma closed_control : True. exact I. Qed.

Goal True. Proof. idtac "AUDIT: rogue". exact I. Qed.
Check @rogue.
Print Assumptions rogue.

Goal True. Proof. idtac "AUDIT: witness". exact I. Qed.
Check @witness.
Print Assumptions witness.

Goal True. Proof. idtac "AUDIT: dependent_witness". exact I. Qed.
Check @dependent_witness.
Print Assumptions dependent_witness.

Goal True. Proof. idtac "AUDIT: closed_control". exact I. Qed.
Check @closed_control.
Print Assumptions closed_control.
