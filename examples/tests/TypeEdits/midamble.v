(* Preserve the requested result alias, rather than just inferring its sort. *)
Goal True.
  let ty := type of Small in constr_eq ty typeEditsSort.
  exact I.
Qed.

(* The motive varies with b only when b is an index and a is a parameter. *)
Check Product_rect :
  forall (a : Type) (P : forall b : Type, Product a b -> Type),
    (forall (b : Type) (x : a) (y : b), P b (@MkProduct a b x y)) ->
    forall (b : Type) (p : Product a b), P b p.

(* The same token denotes unit outside the constructor's added scope. *)
Check ScopedBool : bool -> Scoped.
Check DefaultUnit : unit -> Scoped.
Check @MkTrimmed : forall a : Type, a -> Trimmed a.
