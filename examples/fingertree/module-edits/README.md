# Translation guidance

Module-specific guidance belongs under `Data/FingerTree/`,
`Data/IntervalMap/FingerTree/`, and `Data/PriorityQueue/FingerTree/`.
Translate the core first. Keep algorithms in the pinned Haskell source and use
edits to guide translation and prove termination, as required by the specification.

The user explicitly approved one exception: the queue's `minViewWithKey` body is
supplied with `redefine` to preserve its source empty-guard order. The example
README and `ASSUMPTIONS.md` record the decision, scope, and regression checks.
