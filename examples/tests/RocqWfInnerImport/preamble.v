(* Preserve the old unqualified inner-module import, not just full paths. *)
From Coq.Program Require Import Wf.
Import WfExtensionality.
Check fix_sub_eq_ext.
(* Ensure the unqualified import selects the intended theorem. *)
Check (eq_refl : @fix_sub_eq_ext =
  @Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext).
