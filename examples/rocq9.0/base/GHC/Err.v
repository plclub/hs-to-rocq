Require Import GHC.Base.
Require Import GHC.Num.

Require Import HsToRocq.Err.

Export String.StringSyntax.
Export Ascii.AsciiSyntax.


(* The use of [Qed] is crucial, this way we cannot look through [error] in our proofs. *)
Definition error {a} `{Default a} : String -> a.
Proof. exact (fun _ => default). Qed.

(* The use of [Qed] is crucial, this way we cannot look through [error] in our proofs. *)
Definition undefined {a} `{Default a} : a.
Proof. exact default. Qed.


Definition errorWithoutStackTrace {a} `{Default a} :
  String -> a := error.

Definition patternFailure {a} `{Default a} : a.
Proof. exact default. Qed.


(* ------------------------------------- *)

(* Partial versions of prelude functions *)

Definition head {a} `{Default a} (xs : list a) : a :=
  match xs with
  | (x::_) => x
  | _      => default
  end.
