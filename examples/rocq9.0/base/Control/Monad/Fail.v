(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Stdlib.Program.Tactics.
Require Stdlib.Program.Wf.
Require Import Stdlib.Program.WfExtensionality.

(* Converted imports: *)

Require GHC.Base.

(* Converted type declarations: *)

Record MonadFail__Dict (m : Type -> Type) := MonadFail__Dict_Build {
  fail__ : forall {a : Type}, GHC.Base.String -> m a }.

#[global] Definition MonadFail (m : Type -> Type) `{GHC.Base.Monad m} :=
  forall r__, (MonadFail__Dict m -> r__) -> r__.
Existing Class MonadFail.

#[global] Definition fail `{g__0__ : MonadFail m}
   : forall {a : Type}, GHC.Base.String -> m a :=
  g__0__ _ (fail__ m).

(* Converted value declarations: *)

#[local] Definition MonadFail__option_fail
   : forall {a : Type}, GHC.Base.String -> option a :=
  fun {a : Type} => fun arg_0__ => None.

#[global]
Program Instance MonadFail__option : MonadFail option :=
  fun _ k__ => k__ {| fail__ := fun (a : Type) => MonadFail__option_fail |}.

#[local] Definition MonadFail__list_fail
   : forall {a : Type}, GHC.Base.String -> list a :=
  fun {a : Type} => fun arg_0__ => nil.

#[global]
Program Instance MonadFail__list : MonadFail list :=
  fun _ k__ => k__ {| fail__ := fun (a : Type) => MonadFail__list_fail |}.

(* Skipping instance `Control.Monad.Fail.MonadFail__IO' of class
   `Control.Monad.Fail.MonadFail' *)

(* External variables:
     None Type list nil option GHC.Base.Monad GHC.Base.String
*)
