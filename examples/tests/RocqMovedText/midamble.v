(* Midambles use the same text rewrite as preambles. *)
Check Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check Coq .Program.Wf .WfExtensionality.fix_sub_eq_ext.
Check Coq.Program(* "Coq.Program.Wf" *) .Wf .WfExtensionality .fix_sub_eq_ext.
Check Coq .Init(* shim *) .Logic.I.
Check ²Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check ₁Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check ₁Coq.Init.Logic.I.
Check ₁My₁Coq.add.
Check ₁Other₁.Coq.Init.Decimal.Little.add.
Check ₁Other₁.Coq.Program.Wf.WfExtensionality.add.
Check +.Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check +..Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check +...Coq.Init.Logic.I.
Check ..Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check ....Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check (.Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check ⊕..Coq.Init.Logic.I.
Check ... Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check +.(* Coq paths in comments stay unchanged. *)Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
Check O.....Coq.Init.Logic.I.
Check Coq.Init.Datatypes.O.....Coq.Init.Logic.I.
Check 0.....Coq.Init.Logic.I.
Check +.My₁Coq.add.
Check +..Other'1.Coq.Init.Decimal.Little.add.
Check ..Other₁.Coq.Program.Wf.WfExtensionality.add.
Check (.Other.Coq.Init.Decimal.Little.add.
Check MyCoq.add.
Check My'Coq.add.
Check My1Coq.add.
Check (eq_refl : tickFirst (3, 4) = 3).
Check A᷀Coq.add.
Check A Coq.add.
Check UserCoq.Init.Decimal.Little.add.
Check UserCoq.Program.Wf.WfExtensionality.add.
Check Other.Coq.Init.Decimal.Little.add.
Check Other.Coq.Program.Wf.WfExtensionality.add.
Check Other .Coq .Program.Wf .WfExtensionality.add.
Check Other(* "Coq.Init.Decimal" *) .Coq.Init.Decimal.Little.add.
Check Other'1.Coq.Init.Decimal.Little.add.
Check Other'1.Coq.Program.Wf.WfExtensionality.add.
Check(Coq.Arith.PeanoNat.Nat.add_comm).
Check(@Coq.Init.Logic.I).
Check(@Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext).

(* The numeral ends before Coq, even without intervening whitespace. *)
Definition adjacentNumeral := (fun (n : nat) (_ : True) => n) 1Coq.Init.Logic.I.
Example adjacentNumeral_ok : adjacentNumeral = 1 := eq_refl.
