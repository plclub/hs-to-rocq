Require Import Coq.Strings.String.
Open Scope string_scope.

Definition preambleLiteral : string := "Coq.Init.Decimal".
(* A missed closing quote must not hide the following moved reference. *)
Check @Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
