# Internal alignment readiness checks

Run `bash examples/parkour/tests/check-deadlock-alignment` from the repository
root. The runner recompiles the source and alignment modules in an isolated
directory with `+all`, then checks each listed export's assumptions independently.

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
`take_at`, while the stronger `take_pending` helper retains its FIFO rejection.
