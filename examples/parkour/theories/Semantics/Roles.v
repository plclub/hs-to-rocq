From Stdlib Require Import Logic.Eqdep_dec.
From Stdlib Require Lists.List NArith.BinNat.
Require Parkour.Symbol.

(* Only decidable equality UIP, never an equality/proof-irrelevance axiom. *)
Definition symbol_eq_dec (s t : Parkour.Symbol.Symbol) :=
  List.list_eq_dec BinNat.N.eq_dec s t.

Lemma symbol_uip (s t : Parkour.Symbol.Symbol) (p q : s = t) : p = q.
Proof. apply UIP_dec. exact symbol_eq_dec. Qed.
