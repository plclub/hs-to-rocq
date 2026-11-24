(* Inventory of every declaration in the translated queue module:
   3 datatypes, 9 public operations, 11 generated instances, 46 local methods
   (including inherited defaults), 3 internal operations, and 2 midamble
   declarations (DefaultPQueue and pqueue_size): 74 entries in total.

   Each entry checks presence and prints its transitive assumptions. Local
   methods are checked by qualified name; importing global instances alone
   would not establish that all translated methods were retained.

   Expected: deferredFix only for the 11 recursive PQueue Foldable methods,
   assocs, the 2 Eq and 7 Ord methods, and their 3 instances (24 entries).
   The other 50 queue entries are closed. OldList.unfoldr is an additional
   foundation entry, expected to depend only on deferredFix.

   This is a source-compilation and assumption audit, not a queue correctness
   theorem. PriorityRegression checks the approved minViewWithKey guard repair;
   PriorityOperations proves its general valid-input contract. *)
Require Data.PriorityQueue.FingerTree.
Require Data.OldList.

Module Queue := Data.PriorityQueue.FingerTree.

(* Datatypes. *)
Check @Queue.Prio.
Print Assumptions Queue.Prio.
Check @Queue.Entry.
Print Assumptions Queue.Entry.
Check @Queue.PQueue.
Print Assumptions Queue.PQueue.

(* All nine exported operations. *)
Check @Queue.empty.
Print Assumptions Queue.empty.
Check @Queue.singleton.
Print Assumptions Queue.singleton.
Check @Queue.union.
Print Assumptions Queue.union.
Check @Queue.insert.
Print Assumptions Queue.insert.
Check @Queue.add.
Print Assumptions Queue.add.
Check @Queue.fromList.
Print Assumptions Queue.fromList.
Check @Queue.null.
Print Assumptions Queue.null.
Check @Queue.minView.
Print Assumptions Queue.minView.
Check @Queue.minViewWithKey.
Print Assumptions Queue.minViewWithKey.

(* All eleven generated dictionaries. *)
Check @Queue.Functor__Entry.
Print Assumptions Queue.Functor__Entry.
Check @Queue.Foldable__Entry.
Print Assumptions Queue.Foldable__Entry.
Check @Queue.Semigroup__Prio.
Print Assumptions Queue.Semigroup__Prio.
Check @Queue.Monoid__Prio.
Print Assumptions Queue.Monoid__Prio.
Check @Queue.Measured__Prio__Entry.
Print Assumptions Queue.Measured__Prio__Entry.
Check @Queue.Functor__PQueue.
Print Assumptions Queue.Functor__PQueue.
Check @Queue.Foldable__PQueue.
Print Assumptions Queue.Foldable__PQueue.
Check @Queue.Semigroup__PQueue.
Print Assumptions Queue.Semigroup__PQueue.
Check @Queue.Monoid__PQueue.
Print Assumptions Queue.Monoid__PQueue.
Check @Queue.Eq___PQueue.
Print Assumptions Queue.Eq___PQueue.
Check @Queue.Ord__PQueue.
Print Assumptions Queue.Ord__PQueue.

(* Every Entry method, including inherited Foldable defaults. *)
Check @Queue.Functor__Entry_fmap.
Print Assumptions Queue.Functor__Entry_fmap.
Check @Queue.Functor__Entry_op_zlzd__.
Print Assumptions Queue.Functor__Entry_op_zlzd__.
Check @Queue.Foldable__Entry_foldMap.
Print Assumptions Queue.Foldable__Entry_foldMap.
Check @Queue.Foldable__Entry_fold.
Print Assumptions Queue.Foldable__Entry_fold.
Check @Queue.Foldable__Entry_foldr.
Print Assumptions Queue.Foldable__Entry_foldr.
Check @Queue.Foldable__Entry_foldl'.
Print Assumptions Queue.Foldable__Entry_foldl'.
Check @Queue.Foldable__Entry_foldMap'.
Print Assumptions Queue.Foldable__Entry_foldMap'.
Check @Queue.Foldable__Entry_foldl.
Print Assumptions Queue.Foldable__Entry_foldl.
Check @Queue.Foldable__Entry_foldr'.
Print Assumptions Queue.Foldable__Entry_foldr'.
Check @Queue.Foldable__Entry_length.
Print Assumptions Queue.Foldable__Entry_length.
Check @Queue.Foldable__Entry_null.
Print Assumptions Queue.Foldable__Entry_null.
Check @Queue.Foldable__Entry_product.
Print Assumptions Queue.Foldable__Entry_product.
Check @Queue.Foldable__Entry_sum.
Print Assumptions Queue.Foldable__Entry_sum.
Check @Queue.Foldable__Entry_toList.
Print Assumptions Queue.Foldable__Entry_toList.

(* Every Prio method. *)
Check @Queue.Semigroup__Prio_op_zlzlzgzg__.
Print Assumptions Queue.Semigroup__Prio_op_zlzlzgzg__.
Check @Queue.Monoid__Prio_mappend.
Print Assumptions Queue.Monoid__Prio_mappend.
Check @Queue.Monoid__Prio_mempty.
Print Assumptions Queue.Monoid__Prio_mempty.
Check @Queue.Monoid__Prio_mconcat.
Print Assumptions Queue.Monoid__Prio_mconcat.
Check @Queue.Measured__Prio__Entry_measure.
Print Assumptions Queue.Measured__Prio__Entry_measure.

(* Every PQueue method, including inherited defaults and Eq/Ord methods. *)
Check @Queue.Functor__PQueue_fmap.
Print Assumptions Queue.Functor__PQueue_fmap.
Check @Queue.Functor__PQueue_op_zlzd__.
Print Assumptions Queue.Functor__PQueue_op_zlzd__.
Check @Queue.Foldable__PQueue_foldMap.
Print Assumptions Queue.Foldable__PQueue_foldMap.
Check @Queue.Foldable__PQueue_fold.
Print Assumptions Queue.Foldable__PQueue_fold.
Check @Queue.Foldable__PQueue_foldr.
Print Assumptions Queue.Foldable__PQueue_foldr.
Check @Queue.Foldable__PQueue_foldl'.
Print Assumptions Queue.Foldable__PQueue_foldl'.
Check @Queue.Foldable__PQueue_foldMap'.
Print Assumptions Queue.Foldable__PQueue_foldMap'.
Check @Queue.Foldable__PQueue_foldl.
Print Assumptions Queue.Foldable__PQueue_foldl.
Check @Queue.Foldable__PQueue_foldr'.
Print Assumptions Queue.Foldable__PQueue_foldr'.
Check @Queue.Foldable__PQueue_length.
Print Assumptions Queue.Foldable__PQueue_length.
Check @Queue.Foldable__PQueue_null.
Print Assumptions Queue.Foldable__PQueue_null.
Check @Queue.Foldable__PQueue_product.
Print Assumptions Queue.Foldable__PQueue_product.
Check @Queue.Foldable__PQueue_sum.
Print Assumptions Queue.Foldable__PQueue_sum.
Check @Queue.Foldable__PQueue_toList.
Print Assumptions Queue.Foldable__PQueue_toList.
Check @Queue.Semigroup__PQueue_op_zlzlzgzg__.
Print Assumptions Queue.Semigroup__PQueue_op_zlzlzgzg__.
Check @Queue.Monoid__PQueue_mappend.
Print Assumptions Queue.Monoid__PQueue_mappend.
Check @Queue.Monoid__PQueue_mempty.
Print Assumptions Queue.Monoid__PQueue_mempty.
Check @Queue.Monoid__PQueue_mconcat.
Print Assumptions Queue.Monoid__PQueue_mconcat.
Check @Queue.Eq___PQueue_op_zeze__.
Print Assumptions Queue.Eq___PQueue_op_zeze__.
Check @Queue.Eq___PQueue_op_zsze__.
Print Assumptions Queue.Eq___PQueue_op_zsze__.
Check @Queue.Ord__PQueue_compare.
Print Assumptions Queue.Ord__PQueue_compare.
Check @Queue.Ord__PQueue_op_zl__.
Print Assumptions Queue.Ord__PQueue_op_zl__.
Check @Queue.Ord__PQueue_op_zlze__.
Print Assumptions Queue.Ord__PQueue_op_zlze__.
Check @Queue.Ord__PQueue_op_zg__.
Print Assumptions Queue.Ord__PQueue_op_zg__.
Check @Queue.Ord__PQueue_op_zgze__.
Print Assumptions Queue.Ord__PQueue_op_zgze__.
Check @Queue.Ord__PQueue_max.
Print Assumptions Queue.Ord__PQueue_max.
Check @Queue.Ord__PQueue_min.
Print Assumptions Queue.Ord__PQueue_min.

(* Internal operations and the two midamble declarations. *)
Check @Queue.unionPrio.
Print Assumptions Queue.unionPrio.
Check @Queue.below.
Print Assumptions Queue.below.
Check @Queue.assocs.
Print Assumptions Queue.assocs.
Check @Queue.DefaultPQueue.
Print Assumptions Queue.DefaultPQueue.
Check @Queue.pqueue_size.
Print Assumptions Queue.pqueue_size.

(* The newly restored source dependency. *)
Check @Data.OldList.unfoldr.
Print Assumptions Data.OldList.unfoldr.
