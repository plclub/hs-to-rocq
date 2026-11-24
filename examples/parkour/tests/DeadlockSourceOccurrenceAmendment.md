# Source receive occurrences and FIFO order

Section 2 of the [specification](../DEADLOCK-FREEDOM-SPEC.md) identifies a
source receive by its occurrence in the choreography. The `RReceive` and
`RHear` rules in [`RoleSteps.v`](../theories/Choreography/RoleSteps.v) use
`take_at_occurrence`: they remove the typed packet at that occurrence and may
pass packets for other occurrences. They consult neither the projection nor
the network queues.

[`PendingDeliveries.v`](../theories/Choreography/PendingDeliveries.v) also
defines `take_first_on_source_channel`, a stronger relation.
`take_pending_at` proves that every removal allowed by this relation is an
occurrence removal; `take_at_split` identifies the removed packet and leaves
the surrounding entries intact. A rejection by the stronger relation alone
does not establish that the source is blocked.

The [independent contracts](Choreography/OccurrenceDelivery.v) distinguish the
two rules on reachable states:

- In a well-formed family, A sends twice while B waits. B can receive the
  first value but cannot execute its second receive before the first.
- In an incoherent family, A's prefix sends to B while B's prefix describes
  A communicating with itself. After both sends, B can receive the second
  occurrence even though the stronger relation rejects it. Well-formedness
  rejects this family.

The [checker](../scripts/frozen_inputs.py) checks the source rules against
[`DeadlockSourceOccurrenceAmendment.sha256`](DeadlockSourceOccurrenceAmendment.sha256)
and their contracts against
[`DeadlockSourceOccurrenceExpect.sha256`](DeadlockSourceOccurrenceExpect.sha256),
using the [namespace mapping](namespace-migration.tsv). Wire FIFO order for
matched runs is a separate [projection result](../theories/Projection/Matching/MatchedReceiveSafety.v);
data and announcements share the same wire queue key.
