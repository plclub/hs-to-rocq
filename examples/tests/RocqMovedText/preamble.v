(* From syntax and extra whitespace must not prevent loading the moved file. *)
From Coq.Program   Require Import   Wf.
Require Coq.Arith.PeanoNat.
Check Coq.Program.Wf.Fix_sub.
Check Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check(Coq.Arith.PeanoNat.Nat.add_comm).

Notation "² x" := x (at level 9, only parsing).
Check ²Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.

Module MyCoq := Nat.
Check MyCoq.add.

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
