# Deadlock-freedom proof handoff

The acceptance contract is `DEADLOCK-FREEDOM-SPEC.md`, SHA-256
`688b31eb14f43ccf3b557a3d86aee532eb4aaf2e4e6ce9497c15fc422c326327`.
Verify from the repository root:

```sh
echo '688b31eb14f43ccf3b557a3d86aee532eb4aaf2e4e6ce9497c15fc422c326327  examples/parkour/DEADLOCK-FREEDOM-SPEC.md' | shasum -a 256 -c -
```

The translation baseline on `parkour` is `3e36e5828ce19fe61f9ebd04b1a4a455bd1ff002`.
The first gate is the fatal-warning build with the existing inputs. A
successful check at the baseline's weaker warning setting does not pass it.

## Why the proof stops

[`counterexample/EXPECTED.md`](counterexample/EXPECTED.md) fixes the inputs and
observations (revision `fd292580`, SHA-256
`b6057f6ac2e296987ba3483a934cb0815290cef92548f1427172611f30596e59`).
There are two roles, no local calls, and two different types on one FIFO.
The Boolean announcement must precede the unit send in the source. On the
network, the issue is the *owner* arm of `Cond`, not message loss or an
unlawful codec:

1. [`Choreo2.hs`, lines 103–109](upstream/src/Choreography/Choreo2.hs#L103-L109)
   sequences a discarded broadcast with `>>`, but binds the received choice
   with `>>=`. `Epp` derives `Monad` via `ReaderT`.
2. The pinned transformers `Control/Monad/Trans/Reader.hs` defines
   `ReaderT`'s `(>>) = (*>)`. Its applicative instance delegates `*>` to
   the underlying network tree. This operation has already run when
   the network interpreter sees the tree.
3. [`Tree.hs`, lines 9–20](upstream/src/Control/Monad/Tree.hs#L9-L20)
   uses `App` for `<*>` and `Bind` for `>>=`. Scheduling the right side
   of the owner's `App` first is legal. Both operations already have
   `Root`; the network interpreter cannot assign fresh sessions to them.
4. A sends `"()"` and then broadcasts `"True"`. A has finished. B's
   Boolean receive cannot decode `"()"` and cannot skip it. The source,
   in contrast, admits no stuck execution on these inputs.

This refutes preservation, reflection, and history coverage independently
of any choice of induction invariant. It does not show a deadlock in
`Main.quorumVoting`. A change to the upstream owner's sequencing would
change the pinned object of the theorem and needs a separate decision.

The [upstream Haskell diagnostic](counterexample/UPSTREAM.md) also observes
the unit send before the Boolean broadcast without using the Rocq translation.

## Build evidence

On GHC 9.10.3 and Rocq 9.0.1 with Stdlib 9.0.0, `make clean` in this
example exited 0. The subsequent `make check` passed lint and the checker
controls. The good fixture compiled; the two warning probes failed with
`arguments-assert` and `disj-pattern-notation` respectively. The alias,
mixed-client, and extra-premise controls all passed. Source verification
checked 11 upstream, 2 GHC, and 24 transformers files.

`make check` **exited 2**: the first real `rocq c -q -w +all` compile failed
at `manual/Parkour/Symbol.v:1` with `[disj-pattern-notation,syntax]`.
The separate one-line `From Stdlib Require Import ZArith.ZArith.` probe
exited 1 with `[deprecated-transitive-library-file-since-9.0]` for
`Stdlib.ZArith.ZArith_base`. No warning-clean production build is claimed.
These diagnostics are separate from the counterexample: fixing the
imports does not restore the missing source ordering on the network.

## Kernel evidence for the stop condition

[`Family.v`](counterexample/Family.v) fixes `Id`, the two roles and the
actual `Choreo` family; [`Local.v`](counterexample/Local.v) gives its shared
`Ret` interpretation, empty event type, trivial stores and initial input.
There is no `Exec` in either endpoint. [`Source.v`](counterexample/Source.v)
checks both applicable structural formation rules and proves readiness by
induction on **all** finite source runs. [`Projection.v`](counterexample/Projection.v)
normalizes the two runner terms by conversion and reaches the bad queue
using the generated `App` and `Bind` constructors. Its residual cannot even
take a housekeeping step. [`Refutation.v`](counterexample/Refutation.v)
combines these facts and proves the negations of the two implications on
this instance. These are fragment-specific counterexample proofs, not
implementations of the four requested library exports.

Single-query diagnostic checks on Rocq 9.0.1, using the baseline's
compiled translations, each printed **`Closed under the global context`**:

| File | Checked declarations |
| --- | --- |
| Generated `Choreography.Choreo2` | `epp` |
| `Source` | `program_well_formed`, `source_deadlock_free` |
| `History` | `no_send_first`, `generated_history_has_no_source` |
| `Projection` | `actual_projected_bad_run`, `no_network_step`, `bad_not_final`, `actual_projected_counterexample` |
| `Trace` | `projected_action_history` (two wire actions and seven finite bookkeeping steps) |
| `Refutation` | `two_role_counterexample`, `preservation_fails`, `reflection_fails`, `identity_result`, `other_channels_empty` |
| [`ObservableRefutation`](counterexample/ObservableRefutation.v) | `observable_two_role_counterexample` |

The last theorem checks that no finite sequence of silent bookkeeping at
the bad residual can expose a return or a genuine action. It holds for
**every** labelling of the network rules whose steps erase to network
microsteps: `Projection.no_network_step` rules out even a first microstep.
The concrete history therefore witnesses failure without assuming that a
partial list of observed actions enumerates everything an endpoint could do.

`counterexample/check` is the strict replay command, from this directory,
with the generated library and dependencies on disk. It uses the production
warning policy. The diagnostic kernel checks above use baseline artifacts;
they are evidence for the counterexample, not a green warning gate.
