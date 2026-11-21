Require GHC.Base.
Require Data.Functor.Identity.

(* The splices themselves run in GHC. The generated mkLoc functions also
   expose TH declaration builders: preserve their syntax trees. Their only
   quotation effect is pure, so the pure fragment uses Identity. *)
Definition Q := Data.Functor.Identity.Identity.
Inductive Name := mkName : GHC.Base.String -> Name.
Inductive TyLit := StrTyLit : GHC.Base.String -> TyLit.
Inductive Ty := ConT : Name -> Ty | LitT : TyLit -> Ty | AppT : Ty -> Ty -> Ty.
Inductive Pat := VarP : Name -> Pat.
Inductive Exp := ConE : Name -> Exp.
Inductive Body := NormalB : Exp -> Body.
Inductive Dec :=
| SigD : Name -> Ty -> Dec
| ValD : Pat -> Body -> list Dec -> Dec.
