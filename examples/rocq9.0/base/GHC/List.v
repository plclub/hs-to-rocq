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

Require String.
Export String.StringSyntax.

Require Import GHC.Base.
(* _==_ notation *)

Require Import ZArith.
Require Import ZArith.BinInt.

(* Hand-translated version of the prelude definitions
   of these functions. *)

Fixpoint take {a:Type} (n:Z) (xs:list a) : list a :=
  if (n <=? 0)%Z then nil
  else match xs with
       | nil => nil
       | cons y ys => cons y (take (n - 1) ys)
       end.

Fixpoint drop {a:Type} (n:Z) (xs:list a) : list a :=
  if (n <=? 0)%Z then xs
  else match xs with
       | nil => nil
       | cons y ys => drop (n - 1) ys
       end.

(* TODO: mark impossible case with default. *)

Fixpoint scanr {a b:Type} (f : a -> b -> b) (q0 : b)
        (xs: list a) :=
 match xs with
 | nil => (cons q0 nil)
 | cons y ys => match (scanr f q0 ys) with
               | cons q qs => cons (f y q) (cons q qs)
               | nil => nil  (* impossible case  *)
               end
end.


Definition splitAt {a : Type}(n:Z)(xs:list a) :=
  (take n xs, drop n xs).

Definition replicate {a:Type}(n:Z): a -> list a.
destruct (0 <=? n)%Z eqn:E; [|exact (fun _ => nil)].
apply Zle_bool_imp_le in E.
apply natlike_rec2 with (P := fun _ => a -> list a)(z := n).
- exact (fun _ => nil).
- intros n1 Pf rec x. exact (cons x (rec x)).
- exact E.
Defined.

(* Converted imports: *)

Require Corelib.Init.Datatypes.
Require Data.Maybe.
Require Import GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require HsToRocq.Err.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

#[global] Definition prel_list_str : String :=
  GHC.Base.hs_string__ "Prelude.".

#[global] Definition errorEmptyList {a} `{_ : HsToRocq.Err.Default a}
   : String -> a :=
  fun fun_ =>
    GHC.Err.error (Corelib.Init.Datatypes.app prel_list_str
                                              (Corelib.Init.Datatypes.app fun_ (GHC.Base.hs_string__ ": empty list"))).

#[global] Definition badHead {a} `{_ : HsToRocq.Err.Default a} : a :=
  errorEmptyList (GHC.Base.hs_string__ "head").

#[global] Definition head {a} `{_ : HsToRocq.Err.Default a} : list a -> a :=
  fun arg_0__ => match arg_0__ with | cons x _ => x | nil => badHead end.

#[global] Definition uncons {a : Type} : list a -> option (a * list a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => None
    | cons x xs => Some (pair x xs)
    end.

#[global] Definition unsnoc {a : Type} : list a -> option (list a * a)%type :=
  foldr (fun x =>
           Some ∘ Data.Maybe.maybe (pair nil x) (fun '(pair a b) => pair (cons x a) b))
  None.

#[global] Definition tail {a} `{_ : HsToRocq.Err.Default a}
   : list a -> list a :=
  fun arg_0__ =>
    match arg_0__ with
    | cons _ xs => xs
    | nil => errorEmptyList (GHC.Base.hs_string__ "tail")
    end.

(* Skipping definition `GHC.Base.foldl' *)

#[global] Definition lastError {a} `{_ : HsToRocq.Err.Default a} : a :=
  errorEmptyList (GHC.Base.hs_string__ "last").

#[global] Definition last {a} `{_ : HsToRocq.Err.Default a} : list a -> a :=
  fun xs =>
    foldl (fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, x => x end)
    lastError xs.

#[global] Definition init {a} `{_ : HsToRocq.Err.Default a}
   : list a -> list a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => errorEmptyList (GHC.Base.hs_string__ "init")
    | cons x xs =>
        let fix init' arg_2__ arg_3__
          := match arg_2__, arg_3__ with
             | _, nil => nil
             | y, cons z zs => cons y (init' z zs)
             end in
        init' x xs
    end.

#[global] Definition null {a : Type} : list a -> bool :=
  fun arg_0__ => match arg_0__ with | nil => true | cons _ _ => false end.

Fixpoint lenAcc {a} (arg_0__ : list a) (arg_1__ : GHC.Num.Int) : GHC.Num.Int
  := match arg_0__, arg_1__ with
     | nil, n => n
     | cons _ ys, n => lenAcc ys (n GHC.Num.+ #1)
     end.

#[global] Definition length {a : Type} : list a -> GHC.Num.Int :=
  fun xs => lenAcc xs #0.

#[global] Definition lengthFB {x}
   : x -> (GHC.Num.Int -> GHC.Num.Int) -> GHC.Num.Int -> GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, r => fun a => r (a GHC.Num.+ #1)
    end.

#[global] Definition idLength : GHC.Num.Int -> GHC.Num.Int :=
  id.

Fixpoint filter {a : Type} (arg_0__ : a -> bool) (arg_1__ : list a) : list a
  := match arg_0__, arg_1__ with
     | _pred, nil => nil
     | pred, cons x xs =>
         if pred x : bool then cons x (filter pred xs) else
         filter pred xs
     end.

#[global] Definition filterFB {a} {b}
   : (a -> b -> b) -> (a -> bool) -> a -> b -> b :=
  fun c p x r => if p x : bool then c x r else r.

(* Skipping definition `GHC.Base.foldl'' *)

#[global] Definition foldl1 {a} `{_ : HsToRocq.Err.Default a}
   : (a -> a -> a) -> list a -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, cons x xs => foldl f x xs
    | _, nil => errorEmptyList (GHC.Base.hs_string__ "foldl1")
    end.

#[global] Definition foldl1' {a} `{_ : HsToRocq.Err.Default a}
   : (a -> a -> a) -> list a -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, cons x xs => foldl' f x xs
    | _, nil => errorEmptyList (GHC.Base.hs_string__ "foldl1'")
    end.

#[global] Definition sum {a : Type} `{GHC.Num.Num a} : list a -> a :=
  foldl' _GHC.Num.+_ #0.

#[global] Definition product {a : Type} `{GHC.Num.Num a} : list a -> a :=
  foldl' _GHC.Num.*_ #1.

#[global] Definition scanl {b : Type} {a : Type}
   : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo (f : (b -> a -> b)) (q : b) (ls : list a) : list b
      := cons q (match ls with
               | nil => nil
               | cons x xs => scanlGo f (f q x) xs
               end) in
  scanlGo.

#[global] Definition scanlFB {b} {a} {c}
   : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun f c => fun b g => (fun x => let b' := f x b in c b' (g b')).

#[global] Definition constScanl {a} {b} : a -> b -> a :=
  const.

#[global] Definition scanl1 {a : Type} : (a -> a -> a) -> list a -> list a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, cons x xs => scanl f x xs
    | _, nil => nil
    end.

#[global] Definition scanl' {b : Type} {a : Type}
   : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo' (f : (b -> a -> b)) (q : b) (ls : list a) : list b
      := cons q (match ls with
               | nil => nil
               | cons x xs => scanlGo' f (f q x) xs
               end) in
  scanlGo'.

#[global] Definition scanlFB' {b} {a} {c}
   : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun f c => fun b g => (fun x => let b' := f x b in c b' (g b')).

#[global] Definition foldr' {a : Type} {b : Type}
   : (a -> b -> b) -> b -> list a -> b :=
  fun f z0 xs => let f' := fun k x z => k (f x z) in foldl f' id xs z0.

#[global] Definition foldr1 {a} `{_ : HsToRocq.Err.Default a}
   : (a -> a -> a) -> list a -> a :=
  fun f =>
    let fix go arg_0__
      := match arg_0__ with
         | cons x nil => x
         | cons x xs => f x (go xs)
         | nil => errorEmptyList (GHC.Base.hs_string__ "foldr1")
         end in
    go.

(* Skipping definition `GHC.List.scanr' *)

#[global] Definition strictUncurryScanr {a} {b} {c}
   : (a -> b -> c) -> (a * b)%type -> c :=
  fun f pair_ => let 'pair x y := pair_ in f x y.

#[global] Definition scanrFB {a} {b} {c}
   : (a -> b -> b) -> (b -> c -> c) -> a -> (b * c)%type -> (b * c)%type :=
  fun f c =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | x, pair r est => pair (f x r) (c r est)
      end.

Fixpoint scanr1 {a} `{_ : HsToRocq.Err.Default a} (arg_0__ : a -> a -> a)
                (arg_1__ : list a) : list a
  := match arg_0__, arg_1__ with
     | _, nil => nil
     | _, cons x nil => cons x nil
     | f, cons x xs =>
         match scanr1 f xs with
         | (cons q _ as qs) => cons (f x q) qs
         | _ => GHC.Err.patternFailure
         end
     end.

#[global] Definition maximum {a} `{_ : HsToRocq.Err.Default a} {_ : Eq_ a} {_
   : Ord a}
   : list a -> a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => errorEmptyList (GHC.Base.hs_string__ "maximum")
    | xs => foldl1' max xs
    end.

#[global] Definition minimum {a} `{_ : HsToRocq.Err.Default a} {_ : Eq_ a} {_
   : Ord a}
   : list a -> a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => errorEmptyList (GHC.Base.hs_string__ "minimum")
    | xs => foldl1' min xs
    end.

(* Skipping definition `GHC.List.iterate' *)

(* Skipping definition `GHC.List.iterateFB' *)

(* Skipping definition `GHC.List.iterate'' *)

(* Skipping definition `GHC.List.iterate'FB' *)

(* Skipping definition `GHC.List.repeat' *)

(* Skipping definition `GHC.List.repeatFB' *)

(* Skipping definition `GHC.List.replicate' *)

(* Skipping definition `GHC.List.cycle' *)

Fixpoint takeWhile {a : Type} (arg_0__ : a -> bool) (arg_1__ : list a) : list a
  := match arg_0__, arg_1__ with
     | _, nil => nil
     | p, cons x xs => if p x : bool then cons x (takeWhile p xs) else nil
     end.

#[global] Definition takeWhileFB {a} {b}
   : (a -> bool) -> (a -> b -> b) -> b -> a -> b -> b :=
  fun p c n => fun x r => if p x : bool then c x r else n.

Fixpoint dropWhile {a : Type} (arg_0__ : a -> bool) (arg_1__ : list a) : list a
  := match arg_0__, arg_1__ with
     | _, nil => nil
     | p, (cons x xs' as xs) => if p x : bool then dropWhile p xs' else xs
     end.

(* Skipping definition `GHC.List.take' *)

(* Skipping definition `GHC.List.unsafeTake' *)

#[global] Definition flipSeq {a} {b} : a -> b -> a :=
  fun x _n => x.

#[global] Definition takeFB {a} {b}
   : (a -> b -> b) -> b -> a -> (GHC.Num.Int -> b) -> GHC.Num.Int -> b :=
  fun c n x xs =>
    fun m =>
      let 'num_0__ := m in
      if num_0__ == #1 : bool then c x n else
      c x (xs (m GHC.Num.- #1)).

(* Skipping definition `GHC.List.drop' *)

(* Skipping definition `GHC.List.splitAt' *)

Fixpoint span {a : Type} (arg_0__ : a -> bool) (arg_1__ : list a) : (list a *
                                                                     list a)%type
  := match arg_0__, arg_1__ with
     | _, (nil as xs) => pair xs xs
     | p, (cons x xs' as xs) =>
         if p x : bool then let 'pair ys zs := span p xs' in pair (cons x ys) zs else
         pair nil xs
     end.

Fixpoint break {a : Type} (arg_0__ : a -> bool) (arg_1__ : list a) : (list a *
                                                                      list a)%type
  := match arg_0__, arg_1__ with
     | _, (nil as xs) => pair xs xs
     | p, (cons x xs' as xs) =>
         if p x : bool then pair nil xs else
         let 'pair ys zs := break p xs' in
         pair (cons x ys) zs
     end.

#[global] Definition reverse {a : Type} : list a -> list a :=
  fun l =>
    let fix rev arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | nil, a => a
         | cons x xs, a => rev xs (cons x a)
         end in
    rev l nil.

Fixpoint and (arg_0__ : list bool) : bool
  := match arg_0__ with
     | nil => true
     | cons x xs => andb x (and xs)
     end.

Fixpoint or (arg_0__ : list bool) : bool
  := match arg_0__ with
     | nil => false
     | cons x xs => orb x (or xs)
     end.

Fixpoint any {a : Type} (arg_0__ : a -> bool) (arg_1__ : list a) : bool
  := match arg_0__, arg_1__ with
     | _, nil => false
     | p, cons x xs => orb (p x) (any p xs)
     end.

Fixpoint all {a : Type} (arg_0__ : a -> bool) (arg_1__ : list a) : bool
  := match arg_0__, arg_1__ with
     | _, nil => true
     | p, cons x xs => andb (p x) (all p xs)
     end.

Fixpoint elem {a : Type} `{Eq_ a} (arg_0__ : a) (arg_1__ : list a) : bool
  := match arg_0__, arg_1__ with
     | _, nil => false
     | x, cons y ys => orb (x == y) (elem x ys)
     end.

Fixpoint notElem {a : Type} `{Eq_ a} (arg_0__ : a) (arg_1__ : list a) : bool
  := match arg_0__, arg_1__ with
     | _, nil => true
     | x, cons y ys => andb (x /= y) (notElem x ys)
     end.

Fixpoint lookup {a : Type} {b : Type} `{Eq_ a} (arg_0__ : a) (arg_1__
                  : list (a * b)%type) : option b
  := match arg_0__, arg_1__ with
     | _key, nil => None
     | key, cons (pair x y) xys => if key == x : bool then Some y else lookup key xys
     end.

(* Skipping definition `Coq.Lists.List.flat_map' *)

#[global] Definition concat {a : Type} : list (list a) -> list a :=
  foldr Corelib.Init.Datatypes.app nil.

#[global] Definition tooLarge {a} `{_ : HsToRocq.Err.Default a}
   : GHC.Num.Int -> a :=
  fun arg_0__ =>
    GHC.Err.error (Corelib.Init.Datatypes.app prel_list_str (GHC.Base.hs_string__
                                               "!!: index too large")).

#[global] Definition negIndex {a} `{_ : HsToRocq.Err.Default a} : a :=
  GHC.Err.error (Corelib.Init.Datatypes.app prel_list_str (GHC.Base.hs_string__
                                             "!!: negative index")).

#[global] Definition op_znzn__ {a} `{_ : HsToRocq.Err.Default a}
   : list a -> GHC.Num.Int -> a :=
  fun xs n =>
    if n < #0 : bool then negIndex else
    foldr (fun x r k =>
             let 'num_0__ := k in
             if num_0__ == #0 : bool then x else
             r (k GHC.Num.- #1)) tooLarge xs n.

Notation "'_!!_'" := (op_znzn__).

Infix "!!" := (_!!_) (at level 99).

#[global] Definition op_znz3fU__ {a : Type}
   : list a -> GHC.Num.Int -> option a :=
  fun xs n =>
    if n < #0 : bool then None else
    foldr (fun x r k =>
             let 'num_0__ := k in
             if num_0__ == #0 : bool then Some x else
             r (k GHC.Num.- #1)) (const None) xs n.

Notation "'_!?_'" := (op_znz3fU__).

Infix "!?" := (_!?_) (at level 99).

#[global] Definition foldr2 {a} {b} {c}
   : (a -> b -> c -> c) -> c -> list a -> list b -> c :=
  fun k z =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | nil, _ys => z
         | _xs, nil => z
         | cons x xs, cons y ys => k x y (go xs ys)
         end in
    go.

#[global] Definition foldr2_left {a} {b} {c} {d}
   : (a -> b -> c -> d) -> d -> a -> (list b -> c) -> list b -> d :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | _k, z, _x, _r, nil => z
    | k, _z, x, r, cons y ys => k x y (r ys)
    end.

#[global] Definition foldr3 {a} {b} {c} {d}
   : (a -> b -> c -> d -> d) -> d -> list a -> list b -> list c -> d :=
  fun k z =>
    let fix go arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | nil, _, _ => z
         | _, nil, _ => z
         | _, _, nil => z
         | cons a as_, cons b bs, cons c cs => k a b c (go as_ bs cs)
         end in
    go.

#[global] Definition foldr3_left {a} {b} {c} {d} {e}
   : (a -> b -> c -> d -> e) ->
     e -> a -> (list b -> list c -> d) -> list b -> list c -> e :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
    | k, _z, a, r, cons b bs, cons c cs => k a b c (r bs cs)
    | _, z, _, _, _, _ => z
    end.

Fixpoint zip {a : Type} {b : Type} (arg_0__ : list a) (arg_1__ : list b) : list
                                                                           (a * b)%type
  := match arg_0__, arg_1__ with
     | nil, _bs => nil
     | _as, nil => nil
     | cons a as_, cons b bs => cons (pair a b) (zip as_ bs)
     end.

#[global] Definition zipFB {a} {b} {c} {d}
   : ((a * b)%type -> c -> d) -> a -> b -> c -> d :=
  fun c => fun x y r => c (pair x y) r.

Fixpoint zip3 {a : Type} {b : Type} {c : Type} (arg_0__ : list a) (arg_1__
                : list b) (arg_2__ : list c) : list (a * b * c)%type
  := match arg_0__, arg_1__, arg_2__ with
     | cons a as_, cons b bs, cons c cs => cons (pair (pair a b) c) (zip3 as_ bs cs)
     | _, _, _ => nil
     end.

#[global] Definition zip3FB {a} {b} {c} {xs} {xs'}
   : ((a * b * c)%type -> xs -> xs') -> a -> b -> c -> xs -> xs' :=
  fun cons_ => fun a b c r => cons_ (pair (pair a b) c) r.

#[global] Definition zipWith {a : Type} {b : Type} {c : Type}
   : (a -> b -> c) -> list a -> list b -> list c :=
  fun f =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | nil, _ => nil
         | _, nil => nil
         | cons x xs, cons y ys => cons (f x y) (go xs ys)
         end in
    go.

#[global] Definition zipWithFB {a} {b} {c} {d} {e}
   : (a -> b -> c) -> (d -> e -> a) -> d -> e -> b -> c :=
  fun c f => fun x y r => c (f x y) r.

#[global] Definition zipWith3 {a : Type} {b : Type} {c : Type} {d : Type}
   : (a -> b -> c -> d) -> list a -> list b -> list c -> list d :=
  fun z =>
    let fix go arg_0__ arg_1__ arg_2__
      := match arg_0__, arg_1__, arg_2__ with
         | cons a as_, cons b bs, cons c cs => cons (z a b c) (go as_ bs cs)
         | _, _, _ => nil
         end in
    go.

#[global] Definition zipWith3FB {d} {xs} {xs'} {a} {b} {c}
   : (d -> xs -> xs') -> (a -> b -> c -> d) -> a -> b -> c -> xs -> xs' :=
  fun cons_ func => fun a b c r => cons_ (func a b c) r.

#[global] Definition unzip {a : Type} {b : Type}
   : list (a * b)%type -> (list a * list b)%type :=
  foldr (fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | pair a b, pair as_ bs => pair (cons a as_) (cons b bs)
           end) (pair nil nil).

#[global] Definition unzip3 {a : Type} {b : Type} {c : Type}
   : list (a * b * c)%type -> (list a * list b * list c)%type :=
  foldr (fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | pair (pair a b) c, pair (pair as_ bs) cs =>
               pair (pair (cons a as_) (cons b bs)) (cons c cs)
           end) (pair (pair nil nil) nil).

Module Notations.
Notation "'_GHC.List.!!_'" := (op_znzn__).
Infix "GHC.List.!!" := (_!!_) (at level 99).
Notation "'_GHC.List.!?_'" := (op_znz3fU__).
Infix "GHC.List.!?" := (_!?_) (at level 99).
End Notations.

(* External variables:
     Eq_ None Ord Some String Type andb bool cons const false foldl foldl' foldr id
     list max min nil op_z2218U__ op_zeze__ op_zl__ op_zsze__ op_zt__ option orb pair
     true Corelib.Init.Datatypes.app Data.Maybe.maybe GHC.Err.error
     GHC.Err.patternFailure GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ HsToRocq.Err.Default
*)
