Require GHC.Base.

(* GHC represents a Haskell2010 left operator section using leftSection. *)
Definition leftSection {a b : Type} (f : a -> b) (x : a) := f x.

(* The base edits omit the standard Functor instance for (->) r.
   ReaderT's Contravariant instance maps over runReaderT's result. *)
#[global] Instance functor (r : Type) : GHC.Base.Functor (fun a => r -> a) :=
  fun _ k => k {| GHC.Base.fmap__ := fun _ _ f g x => f (g x);
                  GHC.Base.op_zlzd____ := fun _ _ x _ _ => x |}.
