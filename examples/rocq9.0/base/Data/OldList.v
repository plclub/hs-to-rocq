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

Require Corelib.Init.Datatypes.
Require Stdlib.Lists.List.
Require Data.Maybe.
Require Data.Ord.
Require Data.Tuple.
Require Import GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Require GHC.Tuple.
Require HsToRocq.Err.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive SnocBuilder a : Type :=
  | Mk_SnocBuilder : GHC.Num.Word -> list a -> list a -> SnocBuilder a.

Arguments Mk_SnocBuilder {_} _ _ _.

(* Midamble *)

Require Import GHC.Char.
Require GHC.Unicode.
Require Stdlib.Lists.List.
Require Import Lia.
Import Ascii.AsciiSyntax.
Import String.StringSyntax.


Fixpoint ascending {a0} (arg_48__: a0 -> a0 -> comparison) (a:a0) (as_:list a0 -> list a0) (bs: list a0)
         {struct bs} : list (list a0)
        := let j_53__ : list (list a0) :=
             match arg_48__ , a , as_ , bs with
               | cmp , a , as_ , bs => cons (as_ (cons a nil))
                                           (match bs with
                                           | cons a (cons b xs) =>  if GHC.Base.eq_comparison (cmp a b) Gt : bool
                                                                   then descending cmp b (cons a nil) xs
                                                                   else ascending cmp b (fun y => cons a y) xs
                                           | xs => cons xs nil
                                           end)
             end in
           match arg_48__ , a , as_ , bs with
             | cmp , a , as_ , cons b bs => if negb (GHC.Base.eq_comparison (cmp a b) Gt)
                                            then ascending cmp b (fun arg_54__ =>
                                                                   match arg_54__ with
                                                                     | ys => as_ (cons a ys)
                                                                   end) bs
                                            else j_53__
             | _ , _ , _ , _ => j_53__
           end
with descending {a0} (arg_40__: a0 -> a0 -> comparison) (a:a0) (arg_42__:list a0) arg_43__
     {struct arg_43__} :=
       let j_45__  : list (list a0) :=
           match arg_40__ , a , arg_42__ , arg_43__ with
           | cmp , a , as_ , bs => cons (cons a as_)
                                       (match bs with
                                        | cons a (cons b xs) =>  if GHC.Base.eq_comparison (cmp a b) Gt : bool
                                                                then descending cmp b (cons a nil) xs
                                                                else ascending cmp b (fun y => cons a y) xs
                                        | xs => cons xs nil
                                        end)
           end in
       match arg_40__ , a , arg_42__ , arg_43__ with
       | cmp , a , as_ , cons b bs => if GHC.Base.eq_comparison (cmp a b) Gt : bool
                                     then descending cmp b (cons a as_) bs
                                     else j_45__
       | _ , _ , _ , _ => j_45__
       end.

Definition sequences {a0} (cmp : a0 -> a0 -> comparison) (ys:list a0) : list (list a0)  :=
    match ys with
      | cons a (cons b xs) =>  if GHC.Base.eq_comparison (cmp a b) Gt : bool
                              then descending cmp b (cons a nil) xs
                              else ascending cmp b (fun y => cons a y) xs
      | xs => cons xs nil
    end.


Fixpoint merge {a0} (cmp: a0 -> a0 -> comparison) (l1:list a0) (l2: list a0) : list a0 :=
  let fix merge_aux l2 :=
      match l1 , l2 with
      | (cons a as' as as_) , (cons b bs' as bs) =>
        if GHC.Base.eq_comparison (cmp a b) Gt : bool
        then cons b (merge_aux bs')
        else cons a (merge cmp as' bs)
      | nil , bs => bs
      | as_ , nil => as_
      end in
  merge_aux l2.

Fixpoint mergePairs {a0} (cmp: a0 -> a0 -> comparison) xs
        := match xs with
             | cons a (cons b xs) => cons (merge cmp a b) (mergePairs cmp xs)
             | xs => xs
           end.


Lemma mergePairs_length : forall n, forall a cmp (xs : list (list a)) x y,
      le (length xs) n ->
      lt (length (mergePairs cmp (cons x (cons y xs)))) (2 + n).
induction n. intros; simpl. destruct xs; inversion H. simpl. auto.
intros.
destruct xs.
simpl in *. lia.
destruct xs.
simpl in *. lia.
assert (L : le (length xs) n).
simpl in H. lia.
specialize (IHn a cmp xs l l0 L).
simpl in *. lia.
Qed.

Program Fixpoint mergeAll {a0} (cmp: a0 -> a0 -> comparison)
        (xs : list (list a0)) {measure (length xs) } : list a0 :=
  match xs with
  | nil        => nil
  | cons x nil => x
  | cons x (cons y xs) => mergeAll cmp (mergePairs cmp (cons x (cons y xs)))
  end.
Next Obligation.
simpl.
destruct xs. simpl. auto.
destruct xs. simpl. auto.
apply Nat.succ_lt_mono.
pose (MP := mergePairs_length (length xs) a0 cmp xs l l0 ltac:(auto)). clearbody MP.
simpl in *.
lia.
Defined.

Definition sortBy {a} (cmp : a -> a -> comparison) (xs : list a): list a :=
     mergeAll cmp (sequences cmp xs).

(* -------------------------------------------- *)

Lemma dropWhile_cons_prop : forall {A} (c:A) s p s',
  cons c s' = GHC.List.dropWhile p s ->
  p c = false.
Proof.
  induction s.
  + intros. simpl in *. discriminate.
  + intros p s' H. simpl in H.
    destruct (p a) eqn:Hp.
    ++ eapply IHs. eauto.
    ++ inversion H. subst. auto.
Qed.

Lemma dropWhile_cons_length : forall {A} (c:A) s p s',
  cons c s' = GHC.List.dropWhile p s ->
  lt (length s') (length s).
Proof.
  induction s.
  + intros. simpl in *. discriminate.
  + intros p s' H. simpl in *.
    destruct (p a) eqn:Hp.
    pose (K := IHs p s' H). clearbody K.
    lia.
    inversion H. subst.
    auto.
Qed.

Lemma break_length {A} {p} {s:list A} : forall {w} {s''},
  pair w s'' = List.break p s ->  le (length s'') (length s).
Proof.
  induction s.
  + simpl. intros w s'' h. inversion h. subst. simpl. auto.
  + simpl. intros w s'' h1.
    destruct (p a) eqn:Hp.
    ++ inversion h1. subst. simpl. auto.
    ++ destruct (List.break p s) as [ys zs] eqn:B.
       inversion h1. subst.
       pose (K := IHs ys zs eq_refl). clearbody K.
       auto.
Qed.


Program Fixpoint words (s : GHC.Base.String) { measure (length s) }
  : list GHC.Base.String :=
  match (GHC.List.dropWhile GHC.Unicode.isSpace s) with
    | nil => nil
    | s'  =>
     let 'pair w s'' := GHC.List.break GHC.Unicode.isSpace s' in
     cons w (words s'')
  end.
Next Obligation.
  destruct (List.dropWhile Unicode.isSpace s) eqn:D. contradiction.
  symmetry in D.
  pose (h0 := dropWhile_cons_prop _ _ _ _ D). clearbody h0.
  pose (h1 := dropWhile_cons_length _ _ _ _ D). clearbody h1.
  simpl in Heq_anonymous.
  rewrite h0 in Heq_anonymous.
  destruct (List.break Unicode.isSpace l) as [ys zs] eqn:B.
  inversion Heq_anonymous. subst.
  symmetry in B.
  pose (h2 := break_length B).
  lia.
Defined.

Program Fixpoint lines (s : GHC.Base.String) { measure (length s) }
  : list GHC.Base.String :=
  if (List.null s) then nil else
  let cons_ := fun '(pair h t) => cons h t in
  cons_ (let 'pair l s' := GHC.List.break
                             (fun arg_4__ =>
                                arg_4__ == newline) s in
         pair l (match s' with | nil => nil | cons _ s'' => lines s'' end)).
Next Obligation.
  pose (h0 := break_length Heq_anonymous). clearbody h0. simpl in h0.
  lia.
Defined.

(* Converted value declarations: *)

#[global] Definition dropWhileEnd {a : Type}
   : (a -> bool) -> list a -> list a :=
  fun p =>
    foldr (fun x xs =>
             if andb (p x) (GHC.List.null xs) : bool
             then nil
             else cons x xs) nil.

Fixpoint stripPrefix {a : Type} `{Eq_ a} (arg_0__ arg_1__ : list a) : option
                                                                      (list a)
  := match arg_0__, arg_1__ with
     | nil, ys => Some ys
     | cons x xs, cons y ys => if x == y : bool then stripPrefix xs ys else None
     | _, _ => None
     end.

(* Skipping definition `Data.OldList.elemIndex' *)

(* Skipping definition `Data.OldList.elemIndices' *)

#[global] Definition find {a : Type} : (a -> bool) -> list a -> option a :=
  fun p => Data.Maybe.listToMaybe ∘ GHC.List.filter p.

(* Skipping definition `Data.OldList.findIndex' *)

(* Skipping definition `Data.OldList.findIndices' *)

Fixpoint isPrefixOf {a : Type} `{Eq_ a} (arg_0__ arg_1__ : list a) : bool
  := match arg_0__, arg_1__ with
     | nil, _ => true
     | _, nil => false
     | cons x xs, cons y ys => andb (x == y) (isPrefixOf xs ys)
     end.

Fixpoint dropLength {a} {b} (arg_0__ : list a) (arg_1__ : list b) : list b
  := match arg_0__, arg_1__ with
     | nil, y => y
     | _, nil => nil
     | cons _ x', cons _ y' => dropLength x' y'
     end.

Fixpoint dropLengthMaybe {a} {b} (arg_0__ : list a) (arg_1__ : list b) : option
                                                                         (list b)
  := match arg_0__, arg_1__ with
     | nil, y => Some y
     | _, nil => None
     | cons _ x', cons _ y' => dropLengthMaybe x' y'
     end.

#[global] Definition isSuffixOf {a : Type} `{Eq_ a}
   : list a -> list a -> bool :=
  fun ns hs =>
    Data.Maybe.maybe false id (dropLengthMaybe ns hs >>=
                               (fun delta => return_ (ns == dropLength delta hs))).

(* Skipping definition `Data.OldList.isInfixOf' *)

Fixpoint elem_by {a} (arg_0__ : (a -> a -> bool)) (arg_1__ : a) (arg_2__
                   : list a) : bool
  := match arg_0__, arg_1__, arg_2__ with
     | _, _, nil => false
     | eq, y, cons x xs => orb (eq x y) (elem_by eq y xs)
     end.

#[global] Definition nubBy {a : Type} : (a -> a -> bool) -> list a -> list a :=
  fun eq l =>
    let fix nubBy' arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | nil, _ => nil
         | cons y ys, xs =>
             if elem_by eq y xs : bool then nubBy' ys xs else
             cons y (nubBy' ys (cons y xs))
         end in
    nubBy' l nil.

#[global] Definition nub {a : Type} `{Eq_ a} : list a -> list a :=
  nubBy _==_.

Fixpoint deleteBy {a : Type} (arg_0__ : a -> a -> bool) (arg_1__ : a) (arg_2__
                    : list a) : list a
  := match arg_0__, arg_1__, arg_2__ with
     | _, _, nil => nil
     | eq, x, cons y ys => if eq x y : bool then ys else cons y (deleteBy eq x ys)
     end.

#[global] Definition delete {a : Type} `{Eq_ a} : a -> list a -> list a :=
  deleteBy _==_.

#[global] Definition op_zrzr__ {a : Type} `{Eq_ a}
   : list a -> list a -> list a :=
  foldl (flip delete).

Notation "'_\\_'" := (op_zrzr__).

Infix "\\" := (_\\_) (at level 99).

#[global] Definition unionBy {a : Type}
   : (a -> a -> bool) -> list a -> list a -> list a :=
  fun eq xs ys =>
    Corelib.Init.Datatypes.app xs (foldl (flip (deleteBy eq)) (nubBy eq ys) xs).

#[global] Definition union {a : Type} `{Eq_ a} : list a -> list a -> list a :=
  unionBy _==_.

#[global] Definition intersectBy {a : Type}
   : (a -> a -> bool) -> list a -> list a -> list a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, nil, _ => nil
    | _, _, nil => nil
    | eq, xs, ys =>
        Stdlib.Lists.List.flat_map (fun x =>
                                      if GHC.List.any (eq x) ys : bool then cons x nil else
                                      nil) xs
    end.

#[global] Definition intersect {a : Type} `{Eq_ a}
   : list a -> list a -> list a :=
  intersectBy _==_.

(* Skipping definition `Data.OldList.intersperse' *)

Fixpoint prependToAll {a} (arg_0__ : a) (arg_1__ : list a) : list a
  := match arg_0__, arg_1__ with
     | _, nil => nil
     | sep, cons x xs => cons sep (cons x (prependToAll sep xs))
     end.

(* Skipping definition `Data.OldList.intercalate' *)

(* Skipping definition `Data.OldList.transpose' *)

#[global] Definition select {a}
   : (a -> bool) -> a -> (list a * list a)%type -> (list a * list a)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | p, x, pair ts fs =>
        if p x : bool then pair (cons x ts) fs else
        pair ts (cons x fs)
    end.

#[global] Definition partition {a : Type}
   : (a -> bool) -> list a -> (list a * list a)%type :=
  fun p xs => foldr (select p) (pair nil nil) xs.

Fixpoint mapAccumL {acc : Type} {x : Type} {y : Type} (arg_0__
                     : acc -> x -> (acc * y)%type) (arg_1__ : acc) (arg_2__ : list x) : (acc *
                                                                                         list y)%type
  := match arg_0__, arg_1__, arg_2__ with
     | _, s, nil => pair s nil
     | f, s, cons x xs =>
         let 'pair s' y := f s x in
         let 'pair s'' ys := mapAccumL f s' xs in
         pair s'' (cons y ys)
     end.

#[global] Definition pairWithNil {acc} {y} : acc -> (acc * list y)%type :=
  fun x => pair x nil.

#[global] Definition mapAccumLF {acc} {x} {y}
   : (acc -> x -> (acc * y)%type) ->
     x -> (acc -> (acc * list y)%type) -> acc -> (acc * list y)%type :=
  fun f =>
    fun x r =>
      (fun s =>
         let 'pair s' y := f s x in
         let 'pair s'' ys := r s' in
         pair s'' (cons y ys)).

Fixpoint mapAccumR {acc : Type} {x : Type} {y : Type} (arg_0__
                     : acc -> x -> (acc * y)%type) (arg_1__ : acc) (arg_2__ : list x) : (acc *
                                                                                         list y)%type
  := match arg_0__, arg_1__, arg_2__ with
     | _, s, nil => pair s nil
     | f, s, cons x xs =>
         let 'pair s' ys := mapAccumR f s xs in
         let 'pair s'' y := f s' x in
         pair s'' (cons y ys)
     end.

Fixpoint insertBy {a : Type} (arg_0__ : a -> a -> comparison) (arg_1__ : a)
                  (arg_2__ : list a) : list a
  := match arg_0__, arg_1__, arg_2__ with
     | _, x, nil => cons x nil
     | cmp, x, (cons y ys' as ys) =>
         match cmp x y with
         | Gt => cons y (insertBy cmp x ys')
         | _ => cons x ys
         end
     end.

#[global] Definition insert {a : Type} `{Ord a} : a -> list a -> list a :=
  fun e ls => insertBy (compare) e ls.

#[global] Definition maximumBy {a} {_ : HsToRocq.Err.Default a} {_ : Eq_ a} {_
   : Ord a}
   : (a -> a -> comparison) -> list a -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, nil =>
        GHC.Err.errorWithoutStackTrace (GHC.Base.hs_string__
                                        "List.maximumBy: empty list")
    | cmp, xs =>
        let maxBy := fun x y => match cmp x y with | Gt => x | _ => y end in
        GHC.List.foldl1 maxBy xs
    end.

#[global] Definition minimumBy {a} {_ : HsToRocq.Err.Default a} {_ : Eq_ a} {_
   : Ord a}
   : (a -> a -> comparison) -> list a -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, nil =>
        GHC.Err.errorWithoutStackTrace (GHC.Base.hs_string__
                                        "List.minimumBy: empty list")
    | cmp, xs =>
        let minBy := fun x y => match cmp x y with | Gt => y | _ => x end in
        GHC.List.foldl1 minBy xs
    end.

Fixpoint genericLength {i : Type} {a : Type} `{GHC.Num.Num i} (arg_0__ : list a)
  : i
  := match arg_0__ with
     | nil => #0
     | cons _ l => #1 GHC.Num.+ genericLength l
     end.

#[global] Definition strictGenericLength {i} {b} `{(GHC.Num.Num i)}
   : list b -> i :=
  fun l =>
    let fix gl arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | nil, a => a
         | cons _ xs, a => let a' := a GHC.Num.+ #1 in GHC.Prim.seq a' (gl xs a')
         end in
    gl l #0.

Fixpoint genericTake {i : Type} {a : Type} `{GHC.Real.Integral i} (arg_0__ : i)
                     (arg_1__ : list a) : list a
  := match arg_0__, arg_1__ with
     | n, _ =>
         if n <= #0 : bool then nil else
         match arg_0__, arg_1__ with
         | _, nil => nil
         | n, cons x xs => cons x (genericTake (n GHC.Num.- #1) xs)
         end
     end.

Fixpoint genericDrop {i : Type} {a : Type} `{GHC.Real.Integral i} (arg_0__ : i)
                     (arg_1__ : list a) : list a
  := match arg_0__, arg_1__ with
     | n, xs =>
         if n <= #0 : bool then xs else
         match arg_0__, arg_1__ with
         | _, nil => nil
         | n, cons _ xs => genericDrop (n GHC.Num.- #1) xs
         end
     end.

Fixpoint genericSplitAt {i : Type} {a : Type} `{GHC.Real.Integral i} (arg_0__
                          : i) (arg_1__ : list a) : (list a * list a)%type
  := match arg_0__, arg_1__ with
     | n, xs =>
         if n <= #0 : bool then pair nil xs else
         match arg_0__, arg_1__ with
         | _, nil => pair nil nil
         | n, cons x xs =>
             let 'pair xs' xs'' := genericSplitAt (n GHC.Num.- #1) xs in
             pair (cons x xs') xs''
         end
     end.

(* Skipping definition `Data.OldList.genericIndex' *)

(* Skipping definition `Data.OldList.genericReplicate' *)

Fixpoint zipWith4 {a : Type} {b : Type} {c : Type} {d : Type} {e : Type}
                  (arg_0__ : a -> b -> c -> d -> e) (arg_1__ : list a) (arg_2__ : list b) (arg_3__
                    : list c) (arg_4__ : list d) : list e
  := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
     | z, cons a as_, cons b bs, cons c cs, cons d ds =>
         cons (z a b c d) (zipWith4 z as_ bs cs ds)
     | _, _, _, _, _ => nil
     end.

#[global] Definition zip4 {a : Type} {b : Type} {c : Type} {d : Type}
   : list a -> list b -> list c -> list d -> list (a * b * c * d)%type :=
  zipWith4 GHC.Tuple.pair4.

Fixpoint zipWith5 {a : Type} {b : Type} {c : Type} {d : Type} {e : Type} {f
                   : Type} (arg_0__ : a -> b -> c -> d -> e -> f) (arg_1__ : list a) (arg_2__
                    : list b) (arg_3__ : list c) (arg_4__ : list d) (arg_5__ : list e) : list f
  := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
     | z, cons a as_, cons b bs, cons c cs, cons d ds, cons e es =>
         cons (z a b c d e) (zipWith5 z as_ bs cs ds es)
     | _, _, _, _, _, _ => nil
     end.

#[global] Definition zip5 {a : Type} {b : Type} {c : Type} {d : Type} {e : Type}
   : list a ->
     list b -> list c -> list d -> list e -> list (a * b * c * d * e)%type :=
  zipWith5 GHC.Tuple.pair5.

Fixpoint zipWith6 {a : Type} {b : Type} {c : Type} {d : Type} {e : Type} {f
                   : Type} {g : Type} (arg_0__ : a -> b -> c -> d -> e -> f -> g) (arg_1__
                    : list a) (arg_2__ : list b) (arg_3__ : list c) (arg_4__ : list d) (arg_5__
                    : list e) (arg_6__ : list f) : list g
  := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__, arg_6__ with
     | z, cons a as_, cons b bs, cons c cs, cons d ds, cons e es, cons f fs =>
         cons (z a b c d e f) (zipWith6 z as_ bs cs ds es fs)
     | _, _, _, _, _, _, _ => nil
     end.

#[global] Definition zip6 {a : Type} {b : Type} {c : Type} {d : Type} {e : Type}
  {f : Type}
   : list a ->
     list b ->
     list c -> list d -> list e -> list f -> list (a * b * c * d * e * f)%type :=
  zipWith6 GHC.Tuple.pair6.

Fixpoint zipWith7 {a : Type} {b : Type} {c : Type} {d : Type} {e : Type} {f
                   : Type} {g : Type} {h : Type} (arg_0__ : a -> b -> c -> d -> e -> f -> g -> h)
                  (arg_1__ : list a) (arg_2__ : list b) (arg_3__ : list c) (arg_4__ : list d)
                  (arg_5__ : list e) (arg_6__ : list f) (arg_7__ : list g) : list h
  := match arg_0__
         , arg_1__
         , arg_2__
         , arg_3__
         , arg_4__
         , arg_5__
         , arg_6__
         , arg_7__ with
     | z
     , cons a as_
     , cons b bs
     , cons c cs
     , cons d ds
     , cons e es
     , cons f fs
     , cons g gs =>
         cons (z a b c d e f g) (zipWith7 z as_ bs cs ds es fs gs)
     | _, _, _, _, _, _, _, _ => nil
     end.

#[global] Definition zip7 {a : Type} {b : Type} {c : Type} {d : Type} {e : Type}
  {f : Type} {g : Type}
   : list a ->
     list b ->
     list c ->
     list d -> list e -> list f -> list g -> list (a * b * c * d * e * f * g)%type :=
  zipWith7 GHC.Tuple.pair7.

#[global] Definition zipWith4FB {e} {xs} {xs'} {a} {b} {c} {d}
   : (e -> xs -> xs') ->
     (a -> b -> c -> d -> e) -> a -> b -> c -> d -> xs -> xs' :=
  fun cons_ func => fun a b c d r => cons_ (func a b c d) r.

#[global] Definition zipWith5FB {f} {xs} {xs'} {a} {b} {c} {d} {e}
   : (f -> xs -> xs') ->
     (a -> b -> c -> d -> e -> f) -> a -> b -> c -> d -> e -> xs -> xs' :=
  fun cons_ func => fun a b c d e r => cons_ (func a b c d e) r.

#[global] Definition zipWith6FB {g} {xs} {xs'} {a} {b} {c} {d} {e} {f}
   : (g -> xs -> xs') ->
     (a -> b -> c -> d -> e -> f -> g) -> a -> b -> c -> d -> e -> f -> xs -> xs' :=
  fun cons_ func => fun a b c d e f r => cons_ (func a b c d e f) r.

#[global] Definition zipWith7FB {h} {xs} {xs'} {a} {b} {c} {d} {e} {f} {g}
   : (h -> xs -> xs') ->
     (a -> b -> c -> d -> e -> f -> g -> h) ->
     a -> b -> c -> d -> e -> f -> g -> xs -> xs' :=
  fun cons_ func => fun a b c d e f g r => cons_ (func a b c d e f g) r.

#[global] Definition foldr4 {a} {b} {c} {d} {e}
   : (a -> b -> c -> d -> e -> e) ->
     e -> list a -> list b -> list c -> list d -> e :=
  fun k z =>
    let fix go arg_0__ arg_1__ arg_2__ arg_3__
      := match arg_0__, arg_1__, arg_2__, arg_3__ with
         | cons a as_, cons b bs, cons c cs, cons d ds => k a b c d (go as_ bs cs ds)
         | _, _, _, _ => z
         end in
    go.

#[global] Definition foldr5 {a} {b} {c} {d} {e} {f}
   : (a -> b -> c -> d -> e -> f -> f) ->
     f -> list a -> list b -> list c -> list d -> list e -> f :=
  fun k z =>
    let fix go arg_0__ arg_1__ arg_2__ arg_3__ arg_4__
      := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
         | cons a as_, cons b bs, cons c cs, cons d ds, cons e es =>
             k a b c d e (go as_ bs cs ds es)
         | _, _, _, _, _ => z
         end in
    go.

#[global] Definition foldr6 {a} {b} {c} {d} {e} {f} {g}
   : (a -> b -> c -> d -> e -> f -> g -> g) ->
     g -> list a -> list b -> list c -> list d -> list e -> list f -> g :=
  fun k z =>
    let fix go arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__
      := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
         | cons a as_, cons b bs, cons c cs, cons d ds, cons e es, cons f fs =>
             k a b c d e f (go as_ bs cs ds es fs)
         | _, _, _, _, _, _ => z
         end in
    go.

#[global] Definition foldr7 {a} {b} {c} {d} {e} {f} {g} {h}
   : (a -> b -> c -> d -> e -> f -> g -> h -> h) ->
     h -> list a -> list b -> list c -> list d -> list e -> list f -> list g -> h :=
  fun k z =>
    let fix go arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__
      := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__, arg_6__ with
         | cons a as_
         , cons b bs
         , cons c cs
         , cons d ds
         , cons e es
         , cons f fs
         , cons g gs =>
             k a b c d e f g (go as_ bs cs ds es fs gs)
         | _, _, _, _, _, _, _ => z
         end in
    go.

#[global] Definition foldr4_left {a} {b} {c} {d} {e} {f}
   : (a -> b -> c -> d -> e -> f) ->
     f ->
     a -> (list b -> list c -> list d -> e) -> list b -> list c -> list d -> f :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__, arg_6__ with
    | k, _z, a, r, cons b bs, cons c cs, cons d ds => k a b c d (r bs cs ds)
    | _, z, _, _, _, _, _ => z
    end.

#[global] Definition foldr5_left {a} {b} {c} {d} {e} {f} {g}
   : (a -> b -> c -> d -> e -> f -> g) ->
     g ->
     a ->
     (list b -> list c -> list d -> list e -> f) ->
     list b -> list c -> list d -> list e -> g :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__ arg_7__ =>
    match arg_0__
        , arg_1__
        , arg_2__
        , arg_3__
        , arg_4__
        , arg_5__
        , arg_6__
        , arg_7__ with
    | k, _z, a, r, cons b bs, cons c cs, cons d ds, cons e es =>
        k a b c d e (r bs cs ds es)
    | _, z, _, _, _, _, _, _ => z
    end.

#[global] Definition foldr6_left {a} {b} {c} {d} {e} {f} {g} {h}
   : (a -> b -> c -> d -> e -> f -> g -> h) ->
     h ->
     a ->
     (list b -> list c -> list d -> list e -> list f -> g) ->
     list b -> list c -> list d -> list e -> list f -> h :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__ arg_7__ arg_8__ =>
    match arg_0__
        , arg_1__
        , arg_2__
        , arg_3__
        , arg_4__
        , arg_5__
        , arg_6__
        , arg_7__
        , arg_8__ with
    | k, _z, a, r, cons b bs, cons c cs, cons d ds, cons e es, cons f fs =>
        k a b c d e f (r bs cs ds es fs)
    | _, z, _, _, _, _, _, _, _ => z
    end.

#[global] Definition foldr7_left {a} {b} {c} {d} {e} {f} {g} {h} {i}
   : (a -> b -> c -> d -> e -> f -> g -> h -> i) ->
     i ->
     a ->
     (list b -> list c -> list d -> list e -> list f -> list g -> h) ->
     list b -> list c -> list d -> list e -> list f -> list g -> i :=
  fun arg_0__
  arg_1__
  arg_2__
  arg_3__
  arg_4__
  arg_5__
  arg_6__
  arg_7__
  arg_8__
  arg_9__ =>
    match arg_0__
        , arg_1__
        , arg_2__
        , arg_3__
        , arg_4__
        , arg_5__
        , arg_6__
        , arg_7__
        , arg_8__
        , arg_9__ with
    | k
    , _z
    , a
    , r
    , cons b bs
    , cons c cs
    , cons d ds
    , cons e es
    , cons f fs
    , cons g gs =>
        k a b c d e f g (r bs cs ds es fs gs)
    | _, z, _, _, _, _, _, _, _, _ => z
    end.

#[global] Definition unzip4 {a : Type} {b : Type} {c : Type} {d : Type}
   : list (a * b * c * d)%type -> (list a * list b * list c * list d)%type :=
  foldr (fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | pair (pair (pair a b) c) d, pair (pair (pair as_ bs) cs) ds =>
               pair (pair (pair (cons a as_) (cons b bs)) (cons c cs)) (cons d ds)
           end) (pair (pair (pair nil nil) nil) nil).

#[global] Definition unzip5 {a : Type} {b : Type} {c : Type} {d : Type} {e
   : Type}
   : list (a * b * c * d * e)%type ->
     (list a * list b * list c * list d * list e)%type :=
  foldr (fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | pair (pair (pair (pair a b) c) d) e
           , pair (pair (pair (pair as_ bs) cs) ds) es =>
               pair (pair (pair (pair (cons a as_) (cons b bs)) (cons c cs)) (cons d ds)) (cons
                     e es)
           end) (pair (pair (pair (pair nil nil) nil) nil) nil).

#[global] Definition unzip6 {a : Type} {b : Type} {c : Type} {d : Type} {e
   : Type} {f : Type}
   : list (a * b * c * d * e * f)%type ->
     (list a * list b * list c * list d * list e * list f)%type :=
  foldr (fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | pair (pair (pair (pair (pair a b) c) d) e) f
           , pair (pair (pair (pair (pair as_ bs) cs) ds) es) fs =>
               pair (pair (pair (pair (pair (cons a as_) (cons b bs)) (cons c cs)) (cons d ds))
                          (cons e es)) (cons f fs)
           end) (pair (pair (pair (pair (pair nil nil) nil) nil) nil) nil).

#[global] Definition unzip7 {a : Type} {b : Type} {c : Type} {d : Type} {e
   : Type} {f : Type} {g : Type}
   : list (a * b * c * d * e * f * g)%type ->
     (list a * list b * list c * list d * list e * list f * list g)%type :=
  foldr (fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | pair (pair (pair (pair (pair (pair a b) c) d) e) f) g
           , pair (pair (pair (pair (pair (pair as_ bs) cs) ds) es) fs) gs =>
               pair (pair (pair (pair (pair (pair (cons a as_) (cons b bs)) (cons c cs)) (cons
                                       d ds)) (cons e es)) (cons f fs)) (cons g gs)
           end) (pair (pair (pair (pair (pair (pair nil nil) nil) nil) nil) nil) nil).

#[global] Definition deleteFirstsBy {a : Type}
   : (a -> a -> bool) -> list a -> list a -> list a :=
  fun eq => foldl (flip (deleteBy eq)).

(* Skipping definition `Data.OldList.group' *)

(* Skipping definition `Data.OldList.groupBy' *)

(* Skipping definition `Data.OldList.inits' *)

#[global] Definition tails {a : Type} : list a -> list (list a) :=
  fun lst =>
    build' (fun _ =>
              (fun c n =>
                 let fix tailsGo xs
                   := c xs (match xs with | nil => n | cons _ xs' => tailsGo xs' end) in
                 tailsGo lst)).

(* Skipping definition `Data.OldList.subsequences' *)

Fixpoint nonEmptySubsequences {a} (arg_0__ : list a) : list (list a)
  := match arg_0__ with
     | nil => nil
     | cons x xs =>
         let f := fun ys r => cons ys (cons (cons x ys) r) in
         cons (cons x nil) (foldr f nil (nonEmptySubsequences xs))
     end.

(* Skipping definition `Data.OldList.permutations' *)

(* Skipping definition `Data.OldList.sortBy' *)

#[global] Definition sort {a : Type} `{Ord a} : list a -> list a :=
  sortBy compare.

#[global] Definition sortOn {b : Type} {a : Type} `{Ord b}
   : (a -> b) -> list a -> list a :=
  fun f =>
    map Data.Tuple.snd ∘
    (sortBy (Data.Ord.comparing Data.Tuple.fst) ∘
     map (fun x => let y := f x in GHC.Prim.seq y (pair y x))).

#[global] Definition singleton {a : Type} : a -> list a :=
  fun x => cons x nil.

(* Skipping definition `Data.OldList.unfoldr' *)

(* Skipping definition `Data.OldList.lines' *)

Axiom unlines : list String -> String.

(* Skipping definition `Data.OldList.words' *)

(* Skipping definition `Data.OldList.wordsFB' *)

#[global] Definition unwords : list String -> String :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => GHC.Base.hs_string__ ""
    | cons w ws =>
        let fix go arg_2__
          := match arg_2__ with
             | nil => GHC.Base.hs_string__ ""
             | cons v vs =>
                 cons (GHC.Char.hs_char__ " ") (Corelib.Init.Datatypes.app v (go vs))
             end in
        Corelib.Init.Datatypes.app w (go ws)
    end.

#[global] Definition tailUnwords : String -> String :=
  fun arg_0__ => match arg_0__ with | nil => nil | cons _ xs => xs end.

#[global] Definition unwordsFB : String -> String -> String :=
  fun w r => cons (GHC.Char.hs_char__ " ") (Corelib.Init.Datatypes.app w r).

(* Skipping definition `Data.OldList.sb' *)

#[global] Definition emptySB {a} : SnocBuilder a :=
  Mk_SnocBuilder #0 nil nil.

(* Skipping definition `Data.OldList.snocSB' *)

#[global] Definition toListSB {a} : SnocBuilder a -> list a :=
  fun '(Mk_SnocBuilder _ f r) =>
    Corelib.Init.Datatypes.app f (GHC.List.reverse r).

Module Notations.
Notation "'_Data.OldList.\\_'" := (op_zrzr__).
Infix "Data.OldList.\\" := (_\\_) (at level 99).
End Notations.

(* External variables:
     Eq_ Gt None Ord Some String Type andb bool build' compare comparison cons false
     flip foldl foldr id list map nil op_z2218U__ op_zeze__ op_zgzgze__ op_zlze__
     op_zt__ option orb pair return_ sortBy true Corelib.Init.Datatypes.app
     Data.Maybe.listToMaybe Data.Maybe.maybe Data.Ord.comparing Data.Tuple.fst
     Data.Tuple.snd GHC.Err.errorWithoutStackTrace GHC.List.any GHC.List.filter
     GHC.List.foldl1 GHC.List.null GHC.List.reverse GHC.Num.Num GHC.Num.Word
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Prim.seq
     GHC.Real.Integral GHC.Tuple.pair4 GHC.Tuple.pair5 GHC.Tuple.pair6
     GHC.Tuple.pair7 HsToRocq.Err.Default Stdlib.Lists.List.flat_map
*)
