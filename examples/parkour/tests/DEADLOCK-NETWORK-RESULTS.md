# Network operational slice

Run from the repository root:

```sh
make -C examples/parkour check-required
```

The original focused runner used the repaired production `lib`, `build/run/manual`,
`build/run/transformers`, and `examples/rocq9.0/base`. It copies only the new
theories and expectations into an isolated compilation directory. Every
compilation and single-export assumption query uses Rocq 9.0.1 through
`parkour_rocq.py` (`-q -w +all`), with a 60-second timeout.

Verified result: exit 0, four frozen-input checks, 34 separate
`Closed under the global context` reports, and two semantic mutation controls.
The controls first compile well-typed copies with the left or right App rule
disabled by a False premise. The unchanged frozen `left_send` or `right_send`
assertion must then fail at its own proof, with the False-premise diagnostic.
No production source, acceptance input, warning policy, or upstream file is
changed by these controls. `check-required` now runs the same frozen cases
and disabled-branch controls against its freshly generated libraries, loading
`DeadlockLocal` from its verified local stage. Logs are in `build/run/semantics`.

## Interface

`DeadlockNetwork.load` recursively embeds the actual generated `Network M A`
(`Tree (NetworkSig M) A`). `control` adds a residual `CLocal` node so an `Exec`
can suspend after one ITree event. `returns` accounts for finite pure Bind,
App joins, and local Ret/Tau bookkeeping. It is not a step.

`step model participants role ...` chooses one send, receive, announcement,
or local event. Bind enters its continuation only on a `returns` witness.
Both App context rules thread the same queues and store. `nstep` schedules
any endpoint by a list-context split. `run` records finite action traces.
`initialize` loads a supplied endpoint family; clients supply the actual EPP
family when using it. `nfinal` requires every endpoint to return and every
queue to be empty.

Queues contain only `GHC.Base.String`, keyed by sender, receiver, and the
generated `SessionId`. Receive requires successful decoding of the exact
head. `announce` atomically appends to every other configured role. As in the
specification, callers supply a list of distinct configured roles; duplicate
entries are not silently deduplicated. The shared store can be a whole
role-indexed store; the supplied reply relation controls role permissions.
No progress or local-totality field is assumed.

The cases cover both App directions, two ready sends, two empty receives
(within an App and across endpoints), shared-flag execution in both orders
of the actual generated `Tree.par`, wrong session/sender/receiver, an
undecodable head, FIFO order, atomic multi-peer and singleton announcements,
orphan-message stuckness, finite pure/local bookkeeping, resumable two-event
Exec, infinite Tau-only silence, and completed-network finality.

## Freeze history and limits

The narrative manifest was frozen before implementation proofs. The first
exact expectation draft did not elaborate: it needed explicit List/local
imports and `SetFlag` instead of the reserved keyword `Set`. The historical
draft digest remains, but is intentionally not a passing check.
`deadlock-network-expect-v1.sha256` freezes the elaborated expectations before
their proof bodies. The independently added More and Silent sets were also
compiled and frozen before their proofs. Existing frozen inputs were not
changed to make proofs pass.

This slice does **not** prove source well-formedness, source/network matching,
the generated session-ID correspondence, a full EPP preservation theorem,
or the quorum client's preservation theorem. It does not model HTTP failures.
In the `ParkourTheories` migration ([`namespace-migration.tsv`](namespace-migration.tsv)
and [`../scripts/frozen_inputs.py`](../scripts/frozen_inputs.py)),
`DeadlockNetwork` splits across
[`../theories/Network/Mailboxes.v`](../theories/Network/Mailboxes.v),
[`../theories/Network/Endpoints.v`](../theories/Network/Endpoints.v), and
[`../theories/Network/Execution.v`](../theories/Network/Execution.v) (with
`nstep` and `nfinal` renamed to `network_step` and `network_final`), and the
test modules live under [`Network/`](Network/) (`CommunicationRules.v`,
`SharedStoreScheduling.v`, `SilentEndpoints.v`, and `SchedulingAndDelivery.v`),
compiled via [`../scripts/parkour_rocq.py`](../scripts/parkour_rocq.py).
