# Source ordering slice validation

On 2026-11-22, Rocq 9.0.1 compiled the following files with `-q -w +all`
against the freshly repaired production base, manual modules, transformers,
and generated Parkour library:

- `theories/DeadlockSource.v`
- `theories/DeadlockSourceExpect.v`
- `theories/DeadlockSourceExtraExpect.v`
- `theories/DeadlockSourceCases.v`

Every invocation exited zero without diagnostics. The v2 ordering and v1
extra-expectation digest checks passed. The original prose manifest was
frozen before implementation; the syntax-repair note explains the v2 digest.

Fresh, separate assumption queries reported exactly one
`Closed under the global context` each for:

- `DeadlockSource.off_at_decide`
- `DeadlockSource.silent_waiting`
- `DeadlockSource.empty_queue_barrier`
- `DeadlockSourceCases.fifo`
- `DeadlockSourceCases.independent_action`
- `DeadlockSourceCases.parallel_action`
- `DeadlockSourceCases.sends`
- `DeadlockSourceCases.receive_blocks`
- `DeadlockSourceCases.forward_blocks`
- `DeadlockSourceCases.self_other`
- `DeadlockSourceCases.one_role_announcement`
- `DeadlockSourceCases.multi_role_announcement`
- `DeadlockSourceCases.separate_hear`

`Print All Dependencies` for `cstep`, `cfinal`, and `waiting_code` contains
no `epp`, network operational relation, or readiness definition.

The machine has role-specific typed cursors, live App branches, one shared
store, and typed pending deliveries. Only genuine local events, sends,
receives, announcements, and separate announcement receives are actions.
Finite pure bookkeeping is a distinct relation. Bind enters its actual
continuation only with a returned local argument.

Self-communication returns its original located value at every role.
Non-owner results use the same `decide`/`Disproved` branch and `absurd`
function as generated EPP. `off_at_decide` proves exact equality with that
branch; it does not equate arbitrary functions from an empty domain.
Correspondence proofs must still align the concrete equality decision at
each occurrence. No function-extensionality premise has been added.

This slice does not establish source well-formedness, source/network
matching, the preservation theorem, or the quorum client. `make check-required`
now compiles these files and repeats the single-export and dependency queries
using freshly generated libraries. In the `ParkourTheories` migration
([`namespace-migration.tsv`](namespace-migration.tsv) and
[`../scripts/frozen_inputs.py`](../scripts/frozen_inputs.py)), the source
implementation splits across `theories/Choreography/{Occurrences,PendingDeliveries,RoleSteps,Execution}.v`
and the ordering expectations and cases live under
[`Choreography/`](Choreography/) (`CommunicationOrder.v`,
`ChoiceAndSelfCommunication.v`, and `AsynchronousSteps.v`).
