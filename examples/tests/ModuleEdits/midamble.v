(* Require Import must expose an ordinary helper value, not just its notation. *)
Check supportMarker : bool.

(* Import only the generated wrapper, so manual notation must be re-exported. *)
Import ModuleEdits.Support.Notations.
Example manual_notation_reexport : manual_support_flag = false := eq_refl.

(* Original-module axiomatization must retain the translated data declaration. *)
Check Pack : bool -> Payload.
Fail Check opaqueOriginal.
