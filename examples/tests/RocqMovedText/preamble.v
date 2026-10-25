(* From syntax and extra whitespace must not prevent loading the moved file. *)
From Coq.Program   Require Import   Wf.
Check Coq.Program.Wf.Fix_sub.
Check Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
