# Reviewed source occurrence amendment

Specification section 2 gives source receivers occurrence-based selection.
`take_pending` imposed an additional FIFO restriction. This amendment corrects
the source rule and keeps the original proposition about `take_pending`.

## Historical source and unchanged freezes

The original source is Git blob
`d97eeb4607c670944977fe0417addbc2fb3464c3`, present at
`bcc5d7a38eda6903a520759f1682bc68772205a4:examples/parkour/theories/DeadlockSource.v`.
Its SHA-256 is
`eec7c4d4b62cac0713521a83613ba5318940d7260cc7508ba21004346fed7d9c`,
exactly the original source entry in `DeadlockLibraryExpect.sha256`.

That manifest remains byte-for-byte unchanged, with SHA-256
`c91b31607d06c104e763fe3feb574bca467911b2ebd4b1a4981c721f44d68b66`.
The original source entry records provenance only. The checker verifies the
manifest digest but does not fetch or check the superseded source. It checks
the amended semantics and its acceptance fixture through
`DeadlockSourceOccurrenceAmendment.sha256` and `namespace-migration.tsv`.

The existing `DeadlockSourceExpect.v`, `DeadlockSourceExtraExpect.v`,
`DeadlockLibraryExpect.v`, and all their frozen propositions are unchanged.
In particular, the original FIFO rejection still states a fact about the
unchanged `take_pending` operator and is still proved. It is not reinterpreted
as a source-step rejection.

## Reviewed implementation difference

The amended source SHA-256 is
`224836b4f55e3c45dbca506c31965ff293d280c2db26806a74f701bf295e14eb`.
`DeadlockSourceOccurrenceAmendment.sha256` records it separately.

- `take_at` removes exactly the typed packet at a source occurrence; it may
  pass packets for other occurrences.
- `RReceive` and `RHear` use `take_at`.
- The old `source_lane`, `same_channel`, `take_pending`, and their constructors
  retain their original definitions.
- `take_pending_at` proves inclusion; `take_at_split` exposes exact removal.
- New source-only observations prove the acting role and the occurrence of
  an action behind a receive barrier. They use actual prefix syntax and do
  not invoke or guess a blocked continuation's argument.

Cursor, configuration, action, trace, local-model, and finality interfaces
are unchanged. The source operator still does not use EPP or target readiness.

## New pre-proof acceptance inputs

`DeadlockSourceOccurrenceExpect.v` was compiled and frozen before its case
proofs were written. Its SHA-256 is
`4ae247518f7dc77ee37bdb92fbd30589dc2d139dce7e53ba24b8722493064b8a`;
the adjacent expectation manifest records that digest independently.

The assertions require:

1. Exact packet removal and inclusion of every old `take_pending` selection.
2. A well-formed common two-send family, a real two-action `crun` with B
   delayed, an enabled first receive, and no second-occurrence receive before
   the first. The negative tests `cstep` at the actual reachable configuration,
   not just the packet-list helper.
3. An incoherent family rejected by well-formedness. At A its prefix sends to
   B; at B the prefix is self-communication from A to A. Its real two-send
   prefix leaves both packets pending. B can then receive its exact second
   occurrence, even though the unchanged FIFO helper rejects that selection.

The discrepancy control prevents reinstating hidden lane FIFO blocking.
It does not claim that an incoherent family is admitted by the public theorem.

## Remaining correspondence obligation

No theorem equating the old FIFO-restricted source with the occurrence-based
source on well-formed runs is asserted here. Such a theorem needs a source
invariant on occurrence-based reachable states. Wire FIFO correspondence also
needs one frontier across both data and choice traffic: delivery kind is not
part of the generated network queue key. In the `ParkourTheories` migration
([`namespace-migration.tsv`](namespace-migration.tsv) and
[`../scripts/frozen_inputs.py`](../scripts/frozen_inputs.py)), the amended
source splits across
[`../theories/Choreography/Occurrences.v`](../theories/Choreography/Occurrences.v),
[`../theories/Choreography/PendingDeliveries.v`](../theories/Choreography/PendingDeliveries.v),
[`../theories/Choreography/RoleSteps.v`](../theories/Choreography/RoleSteps.v),
and [`../theories/Choreography/Execution.v`](../theories/Choreography/Execution.v)
(with `take_at`, `take_pending`, `cstep`, `crun`, and `cfinal` renamed to
`take_at_occurrence`, `take_first_on_source_channel`, `choreography_step`,
`choreography_run`, and `choreography_final`), and the occurrence expectation
lives at [`Choreography/OccurrenceDelivery.v`](Choreography/OccurrenceDelivery.v).
