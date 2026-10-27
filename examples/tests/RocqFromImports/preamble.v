Check Coq.Init.Logic.I.

(* Comments separate tokens; their strings and dots are not commands. *)
From (* "From Coq.Program Require Wf." *) Other
  Require (* . *) Import
  Coq.Init.Decimal.
Check fromUserLibrary : bool.
Check (eq_refl : fromUserLibrary = true).

From Other Require Export Coq.Init.Decimal.
From Other Require Coq.Init.Decimal.
Check Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
