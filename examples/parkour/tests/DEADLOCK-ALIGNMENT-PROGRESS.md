# Internal alignment readiness checks

Run `make -C examples/parkour check-required SCRATCH=1` from the repository
root. The build recompiles the source and alignment modules in an isolated
directory with `+all`, then checks each named export's assumptions independently.

`DeadlockAlignmentProgress.delivery_available_at` is a sufficient condition for
endpoint readiness, not an exact receive-correspondence contract. When the source
can remove a typed packet with `take_at`, this condition requires an actual head
at the endpoint's directed session key and some value accepted by that site's
actual decoder. The decoded value need not equal the payload of every raw
`take_at` witness.

This distinction matters because `Pending` packages its payload type
existentially. Recovering payload equality from equality of heterogeneous packs
is not justified by decidable equality of roles. The forward readiness proof
does not need that recovery: any decoded value enables the endpoint receive.
Exact matching, decorated receives, and codec round-trip laws remain separate
and unchanged.

The cases therefore distinguish:

- an absent wire head, which blocks readiness;
- an invalid wire head, which the actual decoder rejects;
- a different but decodable payload, which does not block readiness.

The same-lane cases also check that source readiness uses occurrence-only
`take_at_occurrence` (`take_at` before the `ParkourTheories` migration), while
the stronger `take_first_on_source_channel` (`take_pending`) helper retains its
FIFO rejection. In the migrated layout, `delivery_available_at` lives in
[`../theories/Projection/Matching/RoleReadiness.v`](../theories/Projection/Matching/RoleReadiness.v)
(`ParkourTheories.Projection.Matching.RoleReadiness`), and the cases live in
[`Projection/ProjectedRoleReadiness.v`](Projection/ProjectedRoleReadiness.v)
(`ParkourTheories.Tests.Projection.ProjectedRoleReadiness`).
