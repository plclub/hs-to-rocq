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

Require Corelib.Program.Basics.
Require Data.Either.
Require Data.Functor.Const.
Require Data.Monoid.
Require Data.SemigroupInternal.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Tuple.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Record Bifoldable__Dict (p : Type -> Type -> Type) := Bifoldable__Dict_Build {
  bifold__ : forall {m : Type}, forall `{GHC.Base.Monoid m}, p m m -> m ;
  bifoldMap__ : forall {m : Type},
  forall {a : Type},
  forall {b : Type},
  forall `{GHC.Base.Monoid m}, (a -> m) -> (b -> m) -> p a b -> m ;
  bifoldl__ : forall {c : Type},
  forall {a : Type},
  forall {b : Type}, (c -> a -> c) -> (c -> b -> c) -> c -> p a b -> c ;
  bifoldr__ : forall {a : Type},
  forall {c : Type},
  forall {b : Type}, (a -> c -> c) -> (b -> c -> c) -> c -> p a b -> c }.

#[global] Definition Bifoldable (p : Type -> Type -> Type) :=
  forall r__, (Bifoldable__Dict p -> r__) -> r__.
Existing Class Bifoldable.

#[global] Definition bifold `{g__0__ : Bifoldable p}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, p m m -> m :=
  g__0__ _ (bifold__ p).

#[global] Definition bifoldMap `{g__0__ : Bifoldable p}
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (b -> m) -> p a b -> m :=
  g__0__ _ (bifoldMap__ p).

#[global] Definition bifoldl `{g__0__ : Bifoldable p}
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type}, (c -> a -> c) -> (c -> b -> c) -> c -> p a b -> c :=
  g__0__ _ (bifoldl__ p).

#[global] Definition bifoldr `{g__0__ : Bifoldable p}
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type}, (a -> c -> c) -> (b -> c -> c) -> c -> p a b -> c :=
  g__0__ _ (bifoldr__ p).

(* Converted value declarations: *)

#[local] Definition Bifoldable__pair_type_bifoldMap
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> GHC.Tuple.pair_type a b -> m :=
  fun {m : Type} {a : Type} {b : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair a b => GHC.Base.mappend (f a) (g b)
      end.

#[local] Definition Bifoldable__pair_type_bifold
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, GHC.Tuple.pair_type m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Bifoldable__pair_type_bifoldMap GHC.Base.id GHC.Base.id.

#[local] Definition Bifoldable__pair_type_bifoldl
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type},
     (c -> a -> c) -> (c -> b -> c) -> c -> GHC.Tuple.pair_type a b -> c :=
  fun {c : Type} {a : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__pair_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                         GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

#[local] Definition Bifoldable__pair_type_bifoldr
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     (a -> c -> c) -> (b -> c -> c) -> c -> GHC.Tuple.pair_type a b -> c :=
  fun {a : Type} {c : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__pair_type_bifoldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

#[global]
Program Instance Bifoldable__pair_type : Bifoldable GHC.Tuple.pair_type :=
  fun _ k__ =>
    k__ {| bifold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__pair_type_bifold ;
           bifoldMap__ := fun (m : Type) (a : Type) (b : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__pair_type_bifoldMap ;
           bifoldl__ := fun (c : Type) (a : Type) (b : Type) =>
             Bifoldable__pair_type_bifoldl ;
           bifoldr__ := fun (a : Type) (c : Type) (b : Type) =>
             Bifoldable__pair_type_bifoldr |}.

#[local] Definition Bifoldable__Const_bifoldMap
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> Data.Functor.Const.Const a b -> m :=
  fun {m : Type} {a : Type} {b : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Data.Functor.Const.Mk_Const a => f a
      end.

#[local] Definition Bifoldable__Const_bifold
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, Data.Functor.Const.Const m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Bifoldable__Const_bifoldMap GHC.Base.id GHC.Base.id.

#[local] Definition Bifoldable__Const_bifoldl
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type},
     (c -> a -> c) -> (c -> b -> c) -> c -> Data.Functor.Const.Const a b -> c :=
  fun {c : Type} {a : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__Const_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                    (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                     GHC.Base.flip f)) (Data.SemigroupInternal.Mk_Dual
                                                                                        GHC.Base.∘
                                                                                        (Data.SemigroupInternal.Mk_Endo
                                                                                         GHC.Base.∘
                                                                                         GHC.Base.flip g)) t)) z.

#[local] Definition Bifoldable__Const_bifoldr
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     (a -> c -> c) -> (b -> c -> c) -> c -> Data.Functor.Const.Const a b -> c :=
  fun {a : Type} {c : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__Const_bifoldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

#[global]
Program Instance Bifoldable__Const : Bifoldable Data.Functor.Const.Const :=
  fun _ k__ =>
    k__ {| bifold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__Const_bifold ;
           bifoldMap__ := fun (m : Type) (a : Type) (b : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__Const_bifoldMap ;
           bifoldl__ := fun (c : Type) (a : Type) (b : Type) => Bifoldable__Const_bifoldl ;
           bifoldr__ := fun (a : Type) (c : Type) (b : Type) =>
             Bifoldable__Const_bifoldr |}.

(* Skipping instance `Data.Bifoldable.Bifoldable__K1' of class
   `Data.Bifoldable.Bifoldable' *)

#[local] Definition Bifoldable__triple_type_bifoldMap {inst_x : Type}
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> GHC.Tuple.triple_type inst_x a b -> m :=
  fun {m : Type} {a : Type} {b : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair _ a) b => GHC.Base.mappend (f a) (g b)
      end.

#[local] Definition Bifoldable__triple_type_bifold {inst_x : Type}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, GHC.Tuple.triple_type inst_x m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Bifoldable__triple_type_bifoldMap GHC.Base.id GHC.Base.id.

#[local] Definition Bifoldable__triple_type_bifoldl {inst_x : Type}
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type},
     (c -> a -> c) -> (c -> b -> c) -> c -> GHC.Tuple.triple_type inst_x a b -> c :=
  fun {c : Type} {a : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__triple_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                          (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                           GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

#[local] Definition Bifoldable__triple_type_bifoldr {inst_x : Type}
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     (a -> c -> c) -> (b -> c -> c) -> c -> GHC.Tuple.triple_type inst_x a b -> c :=
  fun {a : Type} {c : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__triple_type_bifoldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

#[global]
Program Instance Bifoldable__triple_type {x : Type}
   : Bifoldable (GHC.Tuple.triple_type x) :=
  fun _ k__ =>
    k__ {| bifold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__triple_type_bifold ;
           bifoldMap__ := fun (m : Type) (a : Type) (b : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__triple_type_bifoldMap ;
           bifoldl__ := fun (c : Type) (a : Type) (b : Type) =>
             Bifoldable__triple_type_bifoldl ;
           bifoldr__ := fun (a : Type) (c : Type) (b : Type) =>
             Bifoldable__triple_type_bifoldr |}.

#[local] Definition Bifoldable__quad_type_bifoldMap {inst_x : Type} {inst_y
   : Type}
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> GHC.Tuple.quad_type inst_x inst_y a b -> m :=
  fun {m : Type} {a : Type} {b : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair _ _) a) b => GHC.Base.mappend (f a) (g b)
      end.

#[local] Definition Bifoldable__quad_type_bifold {inst_x : Type} {inst_y : Type}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, GHC.Tuple.quad_type inst_x inst_y m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Bifoldable__quad_type_bifoldMap GHC.Base.id GHC.Base.id.

#[local] Definition Bifoldable__quad_type_bifoldl {inst_x : Type} {inst_y
   : Type}
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type},
     (c -> a -> c) ->
     (c -> b -> c) -> c -> GHC.Tuple.quad_type inst_x inst_y a b -> c :=
  fun {c : Type} {a : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__quad_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                         GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

#[local] Definition Bifoldable__quad_type_bifoldr {inst_x : Type} {inst_y
   : Type}
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     (a -> c -> c) ->
     (b -> c -> c) -> c -> GHC.Tuple.quad_type inst_x inst_y a b -> c :=
  fun {a : Type} {c : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__quad_type_bifoldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

#[global]
Program Instance Bifoldable__quad_type {x : Type} {y : Type}
   : Bifoldable (GHC.Tuple.quad_type x y) :=
  fun _ k__ =>
    k__ {| bifold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__quad_type_bifold ;
           bifoldMap__ := fun (m : Type) (a : Type) (b : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__quad_type_bifoldMap ;
           bifoldl__ := fun (c : Type) (a : Type) (b : Type) =>
             Bifoldable__quad_type_bifoldl ;
           bifoldr__ := fun (a : Type) (c : Type) (b : Type) =>
             Bifoldable__quad_type_bifoldr |}.

#[local] Definition Bifoldable__quint_type_bifoldMap {inst_x : Type} {inst_y
   : Type} {inst_z : Type}
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> GHC.Tuple.quint_type inst_x inst_y inst_z a b -> m :=
  fun {m : Type} {a : Type} {b : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair _ _) _) a) b => GHC.Base.mappend (f a) (g b)
      end.

#[local] Definition Bifoldable__quint_type_bifold {inst_x : Type} {inst_y
   : Type} {inst_z : Type}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m},
     GHC.Tuple.quint_type inst_x inst_y inst_z m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Bifoldable__quint_type_bifoldMap GHC.Base.id GHC.Base.id.

#[local] Definition Bifoldable__quint_type_bifoldl {inst_x : Type} {inst_y
   : Type} {inst_z : Type}
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type},
     (c -> a -> c) ->
     (c -> b -> c) -> c -> GHC.Tuple.quint_type inst_x inst_y inst_z a b -> c :=
  fun {c : Type} {a : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__quint_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                         (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                          GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

#[local] Definition Bifoldable__quint_type_bifoldr {inst_x : Type} {inst_y
   : Type} {inst_z : Type}
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     (a -> c -> c) ->
     (b -> c -> c) -> c -> GHC.Tuple.quint_type inst_x inst_y inst_z a b -> c :=
  fun {a : Type} {c : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__quint_type_bifoldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

#[global]
Program Instance Bifoldable__quint_type {x : Type} {y : Type} {z : Type}
   : Bifoldable (GHC.Tuple.quint_type x y z) :=
  fun _ k__ =>
    k__ {| bifold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__quint_type_bifold ;
           bifoldMap__ := fun (m : Type) (a : Type) (b : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__quint_type_bifoldMap ;
           bifoldl__ := fun (c : Type) (a : Type) (b : Type) =>
             Bifoldable__quint_type_bifoldl ;
           bifoldr__ := fun (a : Type) (c : Type) (b : Type) =>
             Bifoldable__quint_type_bifoldr |}.

#[local] Definition Bifoldable__sext_type_bifoldMap {inst_x : Type} {inst_y
   : Type} {inst_z : Type} {inst_w : Type}
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) ->
     (b -> m) -> GHC.Tuple.sext_type inst_x inst_y inst_z inst_w a b -> m :=
  fun {m : Type} {a : Type} {b : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair (pair _ _) _) _) a) b =>
          GHC.Base.mappend (f a) (g b)
      end.

#[local] Definition Bifoldable__sext_type_bifold {inst_x : Type} {inst_y : Type}
  {inst_z : Type} {inst_w : Type}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m},
     GHC.Tuple.sext_type inst_x inst_y inst_z inst_w m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Bifoldable__sext_type_bifoldMap GHC.Base.id GHC.Base.id.

#[local] Definition Bifoldable__sext_type_bifoldl {inst_x : Type} {inst_y
   : Type} {inst_z : Type} {inst_w : Type}
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type},
     (c -> a -> c) ->
     (c -> b -> c) ->
     c -> GHC.Tuple.sext_type inst_x inst_y inst_z inst_w a b -> c :=
  fun {c : Type} {a : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__sext_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                         GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

#[local] Definition Bifoldable__sext_type_bifoldr {inst_x : Type} {inst_y
   : Type} {inst_z : Type} {inst_w : Type}
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     (a -> c -> c) ->
     (b -> c -> c) ->
     c -> GHC.Tuple.sext_type inst_x inst_y inst_z inst_w a b -> c :=
  fun {a : Type} {c : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__sext_type_bifoldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

#[global]
Program Instance Bifoldable__sext_type {x : Type} {y : Type} {z : Type} {w
   : Type}
   : Bifoldable (GHC.Tuple.sext_type x y z w) :=
  fun _ k__ =>
    k__ {| bifold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__sext_type_bifold ;
           bifoldMap__ := fun (m : Type) (a : Type) (b : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__sext_type_bifoldMap ;
           bifoldl__ := fun (c : Type) (a : Type) (b : Type) =>
             Bifoldable__sext_type_bifoldl ;
           bifoldr__ := fun (a : Type) (c : Type) (b : Type) =>
             Bifoldable__sext_type_bifoldr |}.

#[local] Definition Bifoldable__sept_type_bifoldMap {inst_x : Type} {inst_y
   : Type} {inst_z : Type} {inst_w : Type} {inst_v : Type}
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) ->
     (b -> m) -> GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v a b -> m :=
  fun {m : Type} {a : Type} {b : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair (pair (pair _ _) _) _) _) a) b =>
          GHC.Base.mappend (f a) (g b)
      end.

#[local] Definition Bifoldable__sept_type_bifold {inst_x : Type} {inst_y : Type}
  {inst_z : Type} {inst_w : Type} {inst_v : Type}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m},
     GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Bifoldable__sept_type_bifoldMap GHC.Base.id GHC.Base.id.

#[local] Definition Bifoldable__sept_type_bifoldl {inst_x : Type} {inst_y
   : Type} {inst_z : Type} {inst_w : Type} {inst_v : Type}
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type},
     (c -> a -> c) ->
     (c -> b -> c) ->
     c -> GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v a b -> c :=
  fun {c : Type} {a : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__sept_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                         GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

#[local] Definition Bifoldable__sept_type_bifoldr {inst_x : Type} {inst_y
   : Type} {inst_z : Type} {inst_w : Type} {inst_v : Type}
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     (a -> c -> c) ->
     (b -> c -> c) ->
     c -> GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v a b -> c :=
  fun {a : Type} {c : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__sept_type_bifoldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

#[global]
Program Instance Bifoldable__sept_type {x : Type} {y : Type} {z : Type} {w
   : Type} {v : Type}
   : Bifoldable (GHC.Tuple.sept_type x y z w v) :=
  fun _ k__ =>
    k__ {| bifold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__sept_type_bifold ;
           bifoldMap__ := fun (m : Type) (a : Type) (b : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__sept_type_bifoldMap ;
           bifoldl__ := fun (c : Type) (a : Type) (b : Type) =>
             Bifoldable__sept_type_bifoldl ;
           bifoldr__ := fun (a : Type) (c : Type) (b : Type) =>
             Bifoldable__sept_type_bifoldr |}.

#[local] Definition Bifoldable__Either_bifoldMap
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> Data.Either.Either a b -> m :=
  fun {m : Type} {a : Type} {b : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Data.Either.Left a => f a
      | _, g, Data.Either.Right b => g b
      end.

#[local] Definition Bifoldable__Either_bifold
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, Data.Either.Either m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Bifoldable__Either_bifoldMap GHC.Base.id GHC.Base.id.

#[local] Definition Bifoldable__Either_bifoldl
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type},
     (c -> a -> c) -> (c -> b -> c) -> c -> Data.Either.Either a b -> c :=
  fun {c : Type} {a : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__Either_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                     (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                      GHC.Base.flip f)) (Data.SemigroupInternal.Mk_Dual
                                                                                         GHC.Base.∘
                                                                                         (Data.SemigroupInternal.Mk_Endo
                                                                                          GHC.Base.∘
                                                                                          GHC.Base.flip g)) t)) z.

#[local] Definition Bifoldable__Either_bifoldr
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     (a -> c -> c) -> (b -> c -> c) -> c -> Data.Either.Either a b -> c :=
  fun {a : Type} {c : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__Either_bifoldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

#[global]
Program Instance Bifoldable__Either : Bifoldable Data.Either.Either :=
  fun _ k__ =>
    k__ {| bifold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__Either_bifold ;
           bifoldMap__ := fun (m : Type) (a : Type) (b : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__Either_bifoldMap ;
           bifoldl__ := fun (c : Type) (a : Type) (b : Type) =>
             Bifoldable__Either_bifoldl ;
           bifoldr__ := fun (a : Type) (c : Type) (b : Type) =>
             Bifoldable__Either_bifoldr |}.

#[global] Definition bifoldr' {t : Type -> Type -> Type} {a : Type} {c : Type}
  {b : Type} `{Bifoldable t}
   : (a -> c -> c) -> (b -> c -> c) -> c -> t a b -> c :=
  fun f g z0 xs =>
    let g' := fun k x z => k (g x z) in
    let f' := fun k x z => k (f x z) in bifoldl f' g' GHC.Base.id xs z0.

(* Skipping definition `Data.Bifoldable.bifoldr1' *)

#[global] Definition bifoldrM {t : Type -> Type -> Type} {m : Type -> Type} {a
   : Type} {c : Type} {b : Type} `{Bifoldable t} `{GHC.Base.Monad m}
   : (a -> c -> m c) -> (b -> c -> m c) -> c -> t a b -> m c :=
  fun f g z0 xs =>
    let g' := fun k x z => g x z GHC.Base.>>= k in
    let f' := fun k x z => f x z GHC.Base.>>= k in
    bifoldl f' g' GHC.Base.return_ xs z0.

#[global] Definition bifoldl' {t : Type -> Type -> Type} {a : Type} {b : Type}
  {c : Type} `{Bifoldable t}
   : (a -> b -> a) -> (a -> c -> a) -> a -> t b c -> a :=
  fun f g z0 xs =>
    let g' := fun x k z => k (g z x) in
    let f' := fun x k z => k (f z x) in bifoldr f' g' GHC.Base.id xs z0.

(* Skipping definition `Data.Bifoldable.bifoldl1' *)

#[global] Definition bifoldlM {t : Type -> Type -> Type} {m : Type -> Type} {a
   : Type} {b : Type} {c : Type} `{Bifoldable t} `{GHC.Base.Monad m}
   : (a -> b -> m a) -> (a -> c -> m a) -> a -> t b c -> m a :=
  fun f g z0 xs =>
    let g' := fun x k z => g z x GHC.Base.>>= k in
    let f' := fun x k z => f z x GHC.Base.>>= k in
    bifoldr f' g' GHC.Base.return_ xs z0.

#[global] Definition bitraverse_ {t : Type -> Type -> Type} {f : Type -> Type}
  {a : Type} {c : Type} {b : Type} {d : Type} `{Bifoldable t}
  `{GHC.Base.Applicative f}
   : (a -> f c) -> (b -> f d) -> t a b -> f unit :=
  fun f g =>
    bifoldr (_GHC.Base.*>_ GHC.Base.∘ f) (_GHC.Base.*>_ GHC.Base.∘ g) (GHC.Base.pure
                                                                       tt).

#[global] Definition bifor_ {t : Type -> Type -> Type} {f : Type -> Type} {a
   : Type} {b : Type} {c : Type} {d : Type} `{Bifoldable t} `{GHC.Base.Applicative
  f}
   : t a b -> (a -> f c) -> (b -> f d) -> f unit :=
  fun t f g => bitraverse_ f g t.

#[global] Definition bimapM_ {t : Type -> Type -> Type} {f : Type -> Type} {a
   : Type} {c : Type} {b : Type} {d : Type} `{Bifoldable t} `{GHC.Base.Applicative
  f}
   : (a -> f c) -> (b -> f d) -> t a b -> f unit :=
  bitraverse_.

#[global] Definition biforM_ {t : Type -> Type -> Type} {f : Type -> Type} {a
   : Type} {b : Type} {c : Type} {d : Type} `{Bifoldable t} `{GHC.Base.Applicative
  f}
   : t a b -> (a -> f c) -> (b -> f d) -> f unit :=
  bifor_.

#[global] Definition bisequence_ {t : Type -> Type -> Type} {f : Type -> Type}
  {a : Type} {b : Type} `{Bifoldable t} `{GHC.Base.Applicative f}
   : t (f a) (f b) -> f unit :=
  bifoldr _GHC.Base.*>_ _GHC.Base.*>_ (GHC.Base.pure tt).

#[global] Definition bisequenceA_ {t : Type -> Type -> Type} {f : Type -> Type}
  {a : Type} {b : Type} `{Bifoldable t} `{GHC.Base.Applicative f}
   : t (f a) (f b) -> f unit :=
  bisequence_.

(* Skipping definition `Data.Bifoldable.biasum' *)

(* Skipping definition `Data.Bifoldable.bimsum' *)

#[global] Definition biList {t : Type -> Type -> Type} {a : Type} `{Bifoldable
  t}
   : t a a -> list a :=
  bifoldr cons cons nil.

#[global] Definition binull {t : Type -> Type -> Type} {a : Type} {b : Type}
  `{Bifoldable t}
   : t a b -> bool :=
  bifoldr (fun arg_0__ arg_1__ => false) (fun arg_2__ arg_3__ => false) true.

#[global] Definition bilength {t : Type -> Type -> Type} {a : Type} {b : Type}
  `{Bifoldable t}
   : t a b -> GHC.Num.Int :=
  bifoldl' (fun arg_0__ arg_1__ =>
              match arg_0__, arg_1__ with
              | c, _ => c GHC.Num.+ #1
              end) (fun arg_4__ arg_5__ =>
                      match arg_4__, arg_5__ with
                      | c, _ => c GHC.Num.+ #1
                      end) #0.

#[global] Definition biany {t : Type -> Type -> Type} {a : Type} {b : Type}
  `{Bifoldable t}
   : (a -> bool) -> (b -> bool) -> t a b -> bool :=
  fun p q =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getAny (bifoldMap
                                    (Data.SemigroupInternal.Mk_Any GHC.Base.∘ p) (Data.SemigroupInternal.Mk_Any
                                     GHC.Base.∘
                                     q)).

#[global] Definition bielem {t : Type -> Type -> Type} {a : Type} `{Bifoldable
  t} `{GHC.Base.Eq_ a}
   : a -> t a a -> bool :=
  fun x =>
    biany (GHC.Prim.rightSection _GHC.Base.==_ x) (GHC.Prim.rightSection
                                                   _GHC.Base.==_ x).

#[global] Definition biconcat {t : Type -> Type -> Type} {a : Type} `{Bifoldable
  t}
   : t (list a) (list a) -> list a :=
  bifold.

(* Skipping definition `Data.Bifoldable.bimaximum' *)

(* Skipping definition `Data.Bifoldable.biminimum' *)

#[global] Definition bisum {t : Type -> Type -> Type} {a : Type} `{Bifoldable t}
  `{GHC.Num.Num a}
   : t a a -> a :=
  Corelib.Program.Basics.compose Data.SemigroupInternal.getSum (bifoldMap
                                  Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.Mk_Sum).

#[global] Definition biproduct {t : Type -> Type -> Type} {a : Type}
  `{Bifoldable t} `{GHC.Num.Num a}
   : t a a -> a :=
  Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct (bifoldMap
                                  Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Product).

#[global] Definition biconcatMap {t : Type -> Type -> Type} {a : Type} {c
   : Type} {b : Type} `{Bifoldable t}
   : (a -> list c) -> (b -> list c) -> t a b -> list c :=
  bifoldMap.

#[global] Definition biand {t : Type -> Type -> Type} `{Bifoldable t}
   : t bool bool -> bool :=
  Corelib.Program.Basics.compose Data.SemigroupInternal.getAll (bifoldMap
                                  Data.SemigroupInternal.Mk_All Data.SemigroupInternal.Mk_All).

#[global] Definition bior {t : Type -> Type -> Type} `{Bifoldable t}
   : t bool bool -> bool :=
  Corelib.Program.Basics.compose Data.SemigroupInternal.getAny (bifoldMap
                                  Data.SemigroupInternal.Mk_Any Data.SemigroupInternal.Mk_Any).

#[global] Definition biall {t : Type -> Type -> Type} {a : Type} {b : Type}
  `{Bifoldable t}
   : (a -> bool) -> (b -> bool) -> t a b -> bool :=
  fun p q =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getAll (bifoldMap
                                    (Data.SemigroupInternal.Mk_All GHC.Base.∘ p) (Data.SemigroupInternal.Mk_All
                                     GHC.Base.∘
                                     q)).

(* Skipping definition `Data.Bifoldable.bimaximumBy' *)

(* Skipping definition `Data.Bifoldable.biminimumBy' *)

#[global] Definition binotElem {t : Type -> Type -> Type} {a : Type}
  `{Bifoldable t} `{GHC.Base.Eq_ a}
   : a -> t a a -> bool :=
  fun x => negb GHC.Base.∘ bielem x.

#[global] Definition bifind {t : Type -> Type -> Type} {a : Type} `{Bifoldable
  t}
   : (a -> bool) -> t a a -> option a :=
  fun p =>
    let finder :=
      fun x => Data.Monoid.Mk_First (if p x : bool then Some x else None) in
    Data.Monoid.getFirst GHC.Base.∘ bifoldMap finder finder.

(* External variables:
     None Some Type bool cons false list negb nil option pair true tt unit
     Corelib.Program.Basics.compose Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Functor.Const.Const Data.Functor.Const.Mk_Const
     Data.Monoid.Mk_First Data.Monoid.getFirst Data.SemigroupInternal.Mk_All
     Data.SemigroupInternal.Mk_Any Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getAll Data.SemigroupInternal.getAny
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.flip GHC.Base.id GHC.Base.mappend GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zgzgze__ GHC.Base.op_ztzg__ GHC.Base.pure
     GHC.Base.return_ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
     GHC.Prim.rightSection GHC.Tuple.pair_type GHC.Tuple.quad_type
     GHC.Tuple.quint_type GHC.Tuple.sept_type GHC.Tuple.sext_type
     GHC.Tuple.triple_type
*)
