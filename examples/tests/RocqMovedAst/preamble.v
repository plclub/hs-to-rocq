(* No moved text reference or exact-line Require Import can load the new file.
   Coq 8 loads the inner module through Wf; Rocq 9 needs the static header. *)
From Coq.Program Require Wf.
