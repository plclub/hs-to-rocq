(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Stdlib.Program.Tactics.
Require Stdlib.Program.Wf.
Require Import Stdlib.Program.WfExtensionality.

(* Preamble *)


(* Converted imports: *)

Require GHC.Base.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

#[global] Definition maybe {b : Type} {a : Type}
   : b -> (a -> b) -> option a -> b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | n, _, None => n
    | _, f, Some x => f x
    end.

#[global] Definition isJust {a : Type} : option a -> bool :=
  fun arg_0__ => match arg_0__ with | None => false | _ => true end.

#[global] Definition isNothing {a : Type} : option a -> bool :=
  fun arg_0__ => match arg_0__ with | None => true | _ => false end.

(* Skipping definition `Data.Maybe.fromJust' *)

#[global] Definition fromMaybe {a : Type} : a -> option a -> a :=
  fun d x => match x with | None => d | Some v => v end.

#[global] Definition maybeToList {a : Type} : option a -> list a :=
  fun arg_0__ => match arg_0__ with | None => nil | Some x => cons x nil end.

#[global] Definition listToMaybe {a : Type} : list a -> option a :=
  GHC.Base.foldr (GHC.Base.const GHC.Base.∘ Some) None.

Fixpoint mapMaybe {a : Type} {b : Type} (arg_0__ : a -> option b) (arg_1__
                    : list a) : list b
  := match arg_0__, arg_1__ with
     | _, nil => nil
     | f, cons x xs =>
         let rs := mapMaybe f xs in match f x with | None => rs | Some r => cons r rs end
     end.

#[global] Definition catMaybes {a : Type} : list (option a) -> list a :=
  mapMaybe GHC.Base.id.

#[global] Definition mapMaybeFB {b} {r} {a}
   : (b -> r -> r) -> (a -> option b) -> a -> r -> r :=
  fun cons_ f x next =>
    match f x with
    | None => next
    | Some r => cons_ r next
    end.

(* External variables:
     None Some Type bool cons false list nil option true GHC.Base.const
     GHC.Base.foldr GHC.Base.id GHC.Base.op_z2218U__
*)
