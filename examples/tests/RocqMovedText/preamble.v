(* From syntax and extra whitespace must not prevent loading the moved file. *)
From Coq.Program   Require Import   Wf.
From Coq .Program Require Wf.
From Coq(* "Coq.Program.Wf" (* nested *) *) .Program Require Import Wf.
Require Coq.Arith.PeanoNat.
Check Coq.Program.Wf.Fix_sub.
Check Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check Coq.Program.Wf .WfExtensionality.fix_sub_eq_ext.
(* FIELD tokens can follow trivia without changing the qualified reference. *)
Check Coq .Program
  .Wf(* "Coq.Program.Wf" (* nested *) *) .WfExtensionality .fix_sub_eq_ext.
Check Coq .Init(* shim *) .Logic.I.
Check Coq .Arith.PeanoNat .Nat.add_comm.
Check Coq.Init.Logic.I (* command dot *) .
Check(Coq.Arith.PeanoNat.Nat.add_comm).

Notation "² x" := x (at level 9, only parsing).
Check ²Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.

(* A subscript can continue an identifier but cannot start one. *)
Notation "₁ x" := x (at level 9, only parsing).
Check ₁Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check ₁Coq.Init.Logic.I.

(* Symbolic tokens can include several dots without qualifying the next name. *)
Notation "+. x" := x (at level 9, only parsing).
Notation "+.. x" := x (at level 9, only parsing).
Notation "+... x" := x (at level 9, only parsing).
Notation "'..' x" := x (at level 9, only parsing).
Notation ".... x" := x (at level 9, only parsing).
Notation "(. x" := x (at level 9, only parsing).
Notation "⊕.. x" := x (at level 9, only parsing).
Notation "... x" := x (at level 9, only parsing).
Check +.Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check +..Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check +...Coq.Init.Logic.I.
Check ..Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check ....Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check (.Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check ⊕..Coq.Init.Logic.I.
(* Ellipsis requires whitespace before the next token in both compilers. *)
Check ... Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check +.(* Coq paths in comments stay unchanged. *)Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.

Notation "x ..... y" := (let _ : nat := x in y) (at level 50).
Check O.....Coq.Init.Logic.I.
Check Coq.Init.Datatypes.O.....Coq.Init.Logic.I.
Check Coq.Init.Datatypes.O (* notation *) .....Coq.Init.Logic.I.
Check 0.....Coq.Init.Logic.I.

Module MyCoq := Nat.
Check MyCoq.add.

Module My'Coq := Nat.
Check My'Coq.add.
Module My1Coq := Nat.
Check My1Coq.add.

(* The leading apostrophe is a pattern token, not part of the constructor. *)
Definition tickFirst (p : nat * nat) : nat :=
  let 'Coq.Init.Datatypes.pair a b := p in a.
Example tickFirst_ok : tickFirst (3, 4) = 3 := eq_refl.

(* U+1DC0 and non-breaking U+00A0 are identifier characters in both compilers. *)
Module A᷀Coq := Nat.
Check A᷀Coq.add.
Module A Coq := Nat.
Check A Coq.add.

Module UserCoq.
  Module Init.
    Module Decimal.
      Module Little := Nat.
    End Decimal.
  End Init.
  Module Program.
    Module Wf.
      Module WfExtensionality := Nat.
    End Wf.
  End Program.
End UserCoq.
Check UserCoq.Init.Decimal.Little.add.
Check UserCoq.Program.Wf.WfExtensionality.add.

Module Other.
  Module Coq := UserCoq.
End Other.
Check Other.Coq.Init.Decimal.Little.add.
Check Other.Coq.Program.Wf.WfExtensionality.add.
Check Other .Coq .Program.Wf .WfExtensionality.add.
Check Other(* "Coq.Init.Decimal" *) .Coq.Init.Decimal.Little.add.

Module Other'1 := Other.
Check Other'1.Coq.Init.Decimal.Little.add.
Check Other'1.Coq.Program.Wf.WfExtensionality.add.

Module My₁Coq := Nat.
Module Other₁ := Other.
Check ₁My₁Coq.add.
Check ₁Other₁.Coq.Init.Decimal.Little.add.
Check ₁Other₁.Coq.Program.Wf.WfExtensionality.add.
Check +.My₁Coq.add.
Check +..Other'1.Coq.Init.Decimal.Little.add.
Check ..Other₁.Coq.Program.Wf.WfExtensionality.add.
Check (.Other.Coq.Init.Decimal.Little.add.
