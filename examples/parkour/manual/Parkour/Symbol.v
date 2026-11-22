From Stdlib Require Lists.List NArith.BinNat.
Require GHC.Base.

(* A Symbol literal and the term-level result of symbolVal use the same
   sequence of Haskell characters. The index determines the singleton. *)
Definition Symbol := GHC.Base.String.
Inductive SSymbol (s : Symbol) : Type := MkSSymbol.
Arguments MkSSymbol {s}.

#[mode="-"] Class KnownSymbol (s : Symbol) := knownSymbol : SSymbol s.
#[global] Instance known (s : Symbol) : KnownSymbol s := MkSSymbol.
Definition symbolVal {s : Symbol} {proxy : Symbol -> Type}
  `{KnownSymbol s} (_ : proxy s) : GHC.Base.String := s.

(* GHC's homogeneous :~: shares Rocq's equality eliminator. *)
Definition Equal {T} (x y : T) := x = y.
Notation Refl := eq_refl.

Inductive Decision (P : Prop) :=
| Proved : P -> Decision P
| Disproved : (P -> GHC.Base.Void) -> Decision P.
Arguments Proved {P} _.
Arguments Disproved {P} _.

Definition decide {s t : Symbol} (_ : SSymbol s) (_ : SSymbol t)
  : Decision (s = t) :=
  match List.list_eq_dec BinNat.N.eq_dec s t with
  | left pf => Proved pf
  | right dpf => Disproved (fun pf => False_rect _ (dpf pf))
  end.
