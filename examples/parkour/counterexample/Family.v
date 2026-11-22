From Stdlib Require Import Strings.String Lists.List.
Require Import Parkour.Symbol Parkour.Codec Choreography.Choreo2.
Import ListNotations.

Definition A : Symbol := GHC.Base.hs_string__ "A".
Definition B : Symbol := GHC.Base.hs_string__ "B".
Definition roles := [A; B].
Definition Id (X : Type) := X.

Definition choice (p : Symbol) : At bool A p := Mk_At (fun _ => true).
Definition payload (p : Symbol) : At unit A p := Mk_At (fun _ => tt).
Definition branch (p : Symbol) (_ : bool) : Choreo Id p (At unit B p) :=
  op_z7eUzg__ (payload p) (@MkSSymbol B).
Definition program (p : Symbol) : Choreo Id p (At unit B p) :=
  cond (choice p) (branch p).
