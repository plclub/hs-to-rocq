From ITree Require Import ITreeDefinition.

(* The example uses the identity computation type. No source or endpoint
   contains a local call. This shared interpretation fixes the otherwise
   immaterial model parameters without assuming progress of any effect. *)
Inductive event : Type -> Type := .
Definition interpret {X : Type} (x : X) : itree event X := Ret x.
Definition store := unit.
Definition initial_store {Role : Type} (_ : Role) : store := tt.
Definition input_state := tt.
Definition reply {Role X : Type} (_ : Role) (e : event X) :
    store -> X -> store -> Prop := match e with end.
