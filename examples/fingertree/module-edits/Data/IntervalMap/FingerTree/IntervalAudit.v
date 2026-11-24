(* Source-translation inventory: the 17 required generated dictionaries,
   13 public operations, and internal inRange from INTERVAL-CHECKPOINT.md.
   This presence/assumption audit does not establish their functional contracts. *)
Require Data.IntervalMap.FingerTree.

Print Assumptions Data.IntervalMap.FingerTree.Eq___Interval.
Print Assumptions Data.IntervalMap.FingerTree.Ord__Interval.
Print Assumptions Data.IntervalMap.FingerTree.Eq___Node.
Print Assumptions Data.IntervalMap.FingerTree.Ord__Node.
Print Assumptions Data.IntervalMap.FingerTree.Eq___IntervalMap.
Print Assumptions Data.IntervalMap.FingerTree.Ord__IntervalMap.
Print Assumptions Data.IntervalMap.FingerTree.Semigroup__IntInterval.
Print Assumptions Data.IntervalMap.FingerTree.Monoid__IntInterval.
Print Assumptions Data.IntervalMap.FingerTree.Semigroup__IntervalMap.
Print Assumptions Data.IntervalMap.FingerTree.Monoid__IntervalMap.
Print Assumptions Data.IntervalMap.FingerTree.Measured__IntInterval__Node.
Print Assumptions Data.IntervalMap.FingerTree.Functor__Node.
Print Assumptions Data.IntervalMap.FingerTree.Foldable__Node.
Print Assumptions Data.IntervalMap.FingerTree.Traversable__Node.
Print Assumptions Data.IntervalMap.FingerTree.Functor__IntervalMap.
Print Assumptions Data.IntervalMap.FingerTree.Foldable__IntervalMap.
Print Assumptions Data.IntervalMap.FingerTree.Traversable__IntervalMap.

Print Assumptions Data.IntervalMap.FingerTree.low.
Print Assumptions Data.IntervalMap.FingerTree.high.
Print Assumptions Data.IntervalMap.FingerTree.point.
Print Assumptions Data.IntervalMap.FingerTree.empty.
Print Assumptions Data.IntervalMap.FingerTree.singleton.
Print Assumptions Data.IntervalMap.FingerTree.insert.
Print Assumptions Data.IntervalMap.FingerTree.union.
Print Assumptions Data.IntervalMap.FingerTree.intersections.
Print Assumptions Data.IntervalMap.FingerTree.dominators.
Print Assumptions Data.IntervalMap.FingerTree.search.
Print Assumptions Data.IntervalMap.FingerTree.bounds.
Print Assumptions Data.IntervalMap.FingerTree.leastView.
Print Assumptions Data.IntervalMap.FingerTree.splitAfter.
Print Assumptions Data.IntervalMap.FingerTree.inRange.
