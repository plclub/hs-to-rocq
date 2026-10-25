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

Require Data.Bifoldable.
Require Data.Bifunctor.
Require Data.Either.
Require Data.Functor.
Require Data.Functor.Const.
Require Import Data.Functor.Identity.
Require Data.Functor.Utils.
Require GHC.Base.
Require GHC.Prim.
Require GHC.Tuple.
Import Data.Functor.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Record Bitraversable__Dict (t : Type -> Type -> Type) :=
  Bitraversable__Dict_Build {
  bitraverse__ : forall {f : Type -> Type},
  forall {a : Type},
  forall {c : Type},
  forall {b : Type},
  forall {d : Type},
  forall `{GHC.Base.Applicative f},
  (a -> f c) -> (b -> f d) -> t a b -> f (t c d) }.

#[global] Definition Bitraversable (t : Type -> Type -> Type)
  `{Data.Bifunctor.Bifunctor t} `{Data.Bifoldable.Bifoldable t} :=
  forall r__, (Bitraversable__Dict t -> r__) -> r__.
Existing Class Bitraversable.

#[global] Definition bitraverse `{g__0__ : Bitraversable t}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) -> (b -> f d) -> t a b -> f (t c d) :=
  g__0__ _ (bitraverse__ t).

(* Converted value declarations: *)

#[local] Definition Bitraversable__pair_type_bitraverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) -> GHC.Tuple.pair_type a b -> f (GHC.Tuple.pair_type c d) :=
  fun {f : Type -> Type}
  {a : Type}
  {c : Type}
  {b : Type}
  {d : Type}
  `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair a b => GHC.Base.liftA2 GHC.Tuple.pair2 (f a) (g b)
      end.

#[global]
Program Instance Bitraversable__pair_type : Bitraversable GHC.Tuple.pair_type :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun (f : Type -> Type)
           (a : Type)
           (c : Type)
           (b : Type)
           (d : Type)
           `(GHC.Base.Applicative f) =>
             Bitraversable__pair_type_bitraverse |}.

#[local] Definition Bitraversable__triple_type_bitraverse {inst_x : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     GHC.Tuple.triple_type inst_x a b -> f (GHC.Tuple.triple_type inst_x c d) :=
  fun {f : Type -> Type}
  {a : Type}
  {c : Type}
  {b : Type}
  {d : Type}
  `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair x a) b => GHC.Base.liftA2 (GHC.Tuple.pair3 x) (f a) (g b)
      end.

#[global]
Program Instance Bitraversable__triple_type {x : Type}
   : Bitraversable (GHC.Tuple.triple_type x) :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun (f : Type -> Type)
           (a : Type)
           (c : Type)
           (b : Type)
           (d : Type)
           `(GHC.Base.Applicative f) =>
             Bitraversable__triple_type_bitraverse |}.

#[local] Definition Bitraversable__quad_type_bitraverse {inst_x : Type} {inst_y
   : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     GHC.Tuple.quad_type inst_x inst_y a b ->
     f (GHC.Tuple.quad_type inst_x inst_y c d) :=
  fun {f : Type -> Type}
  {a : Type}
  {c : Type}
  {b : Type}
  {d : Type}
  `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair x y) a) b =>
          GHC.Base.liftA2 (GHC.Tuple.pair4 x y) (f a) (g b)
      end.

#[global]
Program Instance Bitraversable__quad_type {x : Type} {y : Type}
   : Bitraversable (GHC.Tuple.quad_type x y) :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun (f : Type -> Type)
           (a : Type)
           (c : Type)
           (b : Type)
           (d : Type)
           `(GHC.Base.Applicative f) =>
             Bitraversable__quad_type_bitraverse |}.

#[local] Definition Bitraversable__quint_type_bitraverse {inst_x : Type} {inst_y
   : Type} {inst_z : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     GHC.Tuple.quint_type inst_x inst_y inst_z a b ->
     f (GHC.Tuple.quint_type inst_x inst_y inst_z c d) :=
  fun {f : Type -> Type}
  {a : Type}
  {c : Type}
  {b : Type}
  {d : Type}
  `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair x y) z) a) b =>
          GHC.Base.liftA2 (GHC.Tuple.pair5 x y z) (f a) (g b)
      end.

#[global]
Program Instance Bitraversable__quint_type {x : Type} {y : Type} {z : Type}
   : Bitraversable (GHC.Tuple.quint_type x y z) :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun (f : Type -> Type)
           (a : Type)
           (c : Type)
           (b : Type)
           (d : Type)
           `(GHC.Base.Applicative f) =>
             Bitraversable__quint_type_bitraverse |}.

#[local] Definition Bitraversable__sext_type_bitraverse {inst_x : Type} {inst_y
   : Type} {inst_z : Type} {inst_w : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     GHC.Tuple.sext_type inst_x inst_y inst_z inst_w a b ->
     f (GHC.Tuple.sext_type inst_x inst_y inst_z inst_w c d) :=
  fun {f : Type -> Type}
  {a : Type}
  {c : Type}
  {b : Type}
  {d : Type}
  `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair (pair x y) z) w) a) b =>
          GHC.Base.liftA2 (GHC.Tuple.pair6 x y z w) (f a) (g b)
      end.

#[global]
Program Instance Bitraversable__sext_type {x : Type} {y : Type} {z : Type} {w
   : Type}
   : Bitraversable (GHC.Tuple.sext_type x y z w) :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun (f : Type -> Type)
           (a : Type)
           (c : Type)
           (b : Type)
           (d : Type)
           `(GHC.Base.Applicative f) =>
             Bitraversable__sext_type_bitraverse |}.

#[local] Definition Bitraversable__sept_type_bitraverse {inst_x : Type} {inst_y
   : Type} {inst_z : Type} {inst_w : Type} {inst_v : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v a b ->
     f (GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v c d) :=
  fun {f : Type -> Type}
  {a : Type}
  {c : Type}
  {b : Type}
  {d : Type}
  `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair (pair (pair x y) z) w) v) a) b =>
          GHC.Base.liftA2 (GHC.Tuple.pair7 x y z w v) (f a) (g b)
      end.

#[global]
Program Instance Bitraversable__sept_type {x : Type} {y : Type} {z : Type} {w
   : Type} {v : Type}
   : Bitraversable (GHC.Tuple.sept_type x y z w v) :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun (f : Type -> Type)
           (a : Type)
           (c : Type)
           (b : Type)
           (d : Type)
           `(GHC.Base.Applicative f) =>
             Bitraversable__sept_type_bitraverse |}.

#[local] Definition Bitraversable__Either_bitraverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) -> Data.Either.Either a b -> f (Data.Either.Either c d) :=
  fun {f : Type -> Type}
  {a : Type}
  {c : Type}
  {b : Type}
  {d : Type}
  `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Data.Either.Left a => Data.Functor.op_zlzdzg__ Data.Either.Left (f a)
      | _, g, Data.Either.Right b => Data.Functor.op_zlzdzg__ Data.Either.Right (g b)
      end.

#[global]
Program Instance Bitraversable__Either : Bitraversable Data.Either.Either :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun (f : Type -> Type)
           (a : Type)
           (c : Type)
           (b : Type)
           (d : Type)
           `(GHC.Base.Applicative f) =>
             Bitraversable__Either_bitraverse |}.

#[local] Definition Bitraversable__Const_bitraverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     Data.Functor.Const.Const a b -> f (Data.Functor.Const.Const c d) :=
  fun {f : Type -> Type}
  {a : Type}
  {c : Type}
  {b : Type}
  {d : Type}
  `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Data.Functor.Const.Mk_Const a =>
          Data.Functor.op_zlzdzg__ Data.Functor.Const.Mk_Const (f a)
      end.

#[global]
Program Instance Bitraversable__Const
   : Bitraversable Data.Functor.Const.Const :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun (f : Type -> Type)
           (a : Type)
           (c : Type)
           (b : Type)
           (d : Type)
           `(GHC.Base.Applicative f) =>
             Bitraversable__Const_bitraverse |}.

(* Skipping instance `Data.Bitraversable.Bitraversable__K1' of class
   `Data.Bitraversable.Bitraversable' *)

#[global] Definition bisequence {t : Type -> Type -> Type} {f : Type -> Type} {a
   : Type} {b : Type} `{Bitraversable t} `{GHC.Base.Applicative f}
   : t (f a) (f b) -> f (t a b) :=
  bitraverse GHC.Base.id GHC.Base.id.

#[global] Definition bisequenceA {t : Type -> Type -> Type} {f : Type -> Type}
  {a : Type} {b : Type} `{Bitraversable t} `{GHC.Base.Applicative f}
   : t (f a) (f b) -> f (t a b) :=
  bisequence.

#[global] Definition bimapM {t : Type -> Type -> Type} {f : Type -> Type} {a
   : Type} {c : Type} {b : Type} {d : Type} `{Bitraversable t}
  `{GHC.Base.Applicative f}
   : (a -> f c) -> (b -> f d) -> t a b -> f (t c d) :=
  bitraverse.

#[global] Definition bifor {t : Type -> Type -> Type} {f : Type -> Type} {a
   : Type} {b : Type} {c : Type} {d : Type} `{Bitraversable t}
  `{GHC.Base.Applicative f}
   : t a b -> (a -> f c) -> (b -> f d) -> f (t c d) :=
  fun t f g => bitraverse f g t.

#[global] Definition biforM {t : Type -> Type -> Type} {f : Type -> Type} {a
   : Type} {b : Type} {c : Type} {d : Type} `{Bitraversable t}
  `{GHC.Base.Applicative f}
   : t a b -> (a -> f c) -> (b -> f d) -> f (t c d) :=
  bifor.

#[global] Definition bimapAccumL {t : Type -> Type -> Type} {a : Type} {b
   : Type} {c : Type} {d : Type} {e : Type} `{Bitraversable t}
   : (a -> b -> (a * c)%type) ->
     (a -> d -> (a * e)%type) -> a -> t b d -> (a * t c e)%type :=
  fun f g s t =>
    Data.Functor.Utils.runStateL (bitraverse (Data.Functor.Utils.Mk_StateL
                                              GHC.Base.∘
                                              GHC.Base.flip f) (Data.Functor.Utils.Mk_StateL GHC.Base.∘ GHC.Base.flip g)
                                  t) s.

#[global] Definition bimapAccumR {t : Type -> Type -> Type} {a : Type} {b
   : Type} {c : Type} {d : Type} {e : Type} `{Bitraversable t}
   : (a -> b -> (a * c)%type) ->
     (a -> d -> (a * e)%type) -> a -> t b d -> (a * t c e)%type :=
  fun f g s t =>
    Data.Functor.Utils.runStateR (bitraverse (Data.Functor.Utils.Mk_StateR
                                              GHC.Base.∘
                                              GHC.Base.flip f) (Data.Functor.Utils.Mk_StateR GHC.Base.∘ GHC.Base.flip g)
                                  t) s.

#[global] Definition bimapDefault {t : Type -> Type -> Type} {a : Type} {b
   : Type} {c : Type} {d : Type} `{Bitraversable t}
   : (a -> b) -> (c -> d) -> t a c -> t b d :=
  GHC.Prim.coerce (bitraverse : (a -> Identity b) ->
                   (c -> Identity d) -> t a c -> Identity (t b d)).

(* Skipping definition `Data.Bitraversable.bifoldMapDefault' *)

(* External variables:
     Identity Type op_zt__ pair Data.Bifoldable.Bifoldable Data.Bifunctor.Bifunctor
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Functor.op_zlzdzg__
     Data.Functor.Const.Const Data.Functor.Const.Mk_Const
     Data.Functor.Utils.Mk_StateL Data.Functor.Utils.Mk_StateR
     Data.Functor.Utils.runStateL Data.Functor.Utils.runStateR GHC.Base.Applicative
     GHC.Base.flip GHC.Base.id GHC.Base.liftA2 GHC.Base.op_z2218U__ GHC.Prim.coerce
     GHC.Tuple.pair2 GHC.Tuple.pair3 GHC.Tuple.pair4 GHC.Tuple.pair5 GHC.Tuple.pair6
     GHC.Tuple.pair7 GHC.Tuple.pair_type GHC.Tuple.quad_type GHC.Tuple.quint_type
     GHC.Tuple.sept_type GHC.Tuple.sext_type GHC.Tuple.triple_type
*)
