# Ordering assertions

`DeadlockOrderExpect.v` was frozen before `theories/DeadlockOrder.v` was
created. `DeadlockOrderExpect.sha256` records the final pre-implementation
assertion file. Run its checksum check from the repository root.

The assertions use actual `DeadlockSource` positions and generated
`Choreography.Network.SessionId` constructors. They check session nesting,
same-session ordering, finite ordered sequences, relative history order,
and the conditional FIFO frontier theorem. Examples cover reused nested
App paths, Cond inside Bind, descendants of Cond, and opposite App branches.

History ranks are scoped to finite occurrence lists. No natural-valued rank
can preserve mandatory order on every possible source position.

These assertions do not establish frontier closure for actual cursors,
compatibility of an actual source execution's historical positions, or
refinement of raw queues. Those remain separate integration obligations.
In particular, raw queue keys combine data and choice traffic; a ghost
ordering invariant for those keys must combine both delivery kinds.

Build/check registration is intentionally left to the coordinating session.

## Validation

Rocq 9.0.1 compiled the frozen assertions and implementation with the
`parkour_rocq.py` warning policy (`-q -w +all`). Validation used an empty
temporary compilation tree: all 15 required generated/support modules and
`DeadlockLocal`, `DeadlockRuns`, and `DeadlockSource` were freshly compiled
before the two new files. It reused the compiled Rocq base and pinned ITree
installation; it did not rerun translation.

A separate assumption audit checked all 22 definitions and lemmas in
`DeadlockOrder`; every report was closed under the global context.
The assertion checksum remained unchanged.
