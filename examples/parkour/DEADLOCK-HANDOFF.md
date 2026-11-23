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

## Active source revision

After the counterexample below, the user requested a local upstream fix.
The active input is now `872bb12fe1698c8a791b8f64df7b8249f7463367` on
`sequence-cond-announcement` in the submodule. The parent remains the
original public pin. The fix changes the owner's discarded-result `>>` to
`>>= \_ ->`, and nothing else in the choreography or network model.
The [setup instructions](README.md) recover the exact commit without a PR.
The frozen spec and the historical negative fixture still describe the
original revision; the requested preservation result now concerns the
repaired `epp` with the same semantics and assumption ceiling.

`make check-cond-haskell` tests both revisions. The generated-Rocq
[OwnerCond assertions](theories/OwnerCond.v) check the repaired tree's
`Bind` root as well as the session IDs inside a parallel continuation.
These regressions distinguish the repair but do not prove preservation.

**Repaired build (2026-11-22):** On GHC 9.10.3, Rocq 9.0.1 and Stdlib
9.0.0, regenerating the shared base and then running `make clean` and
`make check` in this example exited 0. Narrow arithmetic imports in the
base avoid the deprecated transitive library. Explicit template-universe
annotations preserve the declarations that Rocq previously inferred. No
warning category was disabled. The run compiled the repaired projection and
quorum client, obtained a closed report for `epp` and each of the five
`OwnerCond` checks, and passed the 20 local-effect assumption checks.

The local-model review covered `3eb4b03f..27174fcb` only. On the
standards axis, the missing local-effect trigger in `CLAUDE.md` was
corrected in `31f66d00`. On the spec axis, the reviewers found no
discrepancy between the local effect rules and their finite-view
contracts. Neither review covers the choreography/network correspondence.

### Repaired projection: correspondence checkpoint

`DeadlockFrontiers.prefix_ledger` counts occurrence paths on each real wire
key. On every matched prefix the sends are exactly the receives followed by
the still-pending paths, in order. The checked four-action `RepairMatch`
fixture instantiates the actual matching relation; changing the tag, swapping
the FIFO contents, or inventing a choice fails the match.

The ledger alone does not identify the occurrence at a waiting receiver.
`DeadlockCutSafety.covered_residuals` needs two facts about each source
receive site: the head has that site's occurrence, and a queued message at
that occurrence has the original sender's operand and compatible codec.
The second fact requires no witness value when the channel is empty.
`DeadlockPast.matched_has_actual_past` traces queued messages to actual sends;
`DeadlockCoverage.completed_subtree_coverage` finds peer actions in completed
subtrees. The remaining proof must connect those subtree witnesses to the
**same** matched history and establish both facts from `well_formed`.
The four library exports and the quorum preservation corollary remain open.

`DeadlockSameHistory.queued_operand_at_receiver` follows a queued operand
through intervening steps to the sender's current archive and exposes the
receiver site at that same prefix. `DeadlockStaticOrigin.source_originals_static`
proves the original-value and codec obligation whenever the receiver path
uses only `AppFunction`, `AppArgument`, and `BindPrefix` (including the
root). `DeadlockStaticPaths.static_receive_compares_to_queued` compares such a
site with any same-key queued send, even one in a dynamically entered body.
`DeadlockStaticBarrier.static_sender_barrier` shows that a send at a strict
successor requires a prior send at the static site on this same history.
Together with receiver freshness and the FIFO ledger, this proves
`DeadlockStaticHead.source_head_paths_static`. Both receive obligations are
therefore proved at every static site. Sites inside `BindBody` or `ChoiceBody`
still need the actual earlier result or choice. For a path starting with
`ChoiceBody` followed by static edges, `source_originals_choice_static`
discharges the operand obligation from WF and the matched prefix alone.
It uses `root_choice_actor_invariant`: the peer is still waiting or has an
actual suffix history from the branch selected by the owner's announcement.
It does not assume all peers entered together.
`source_head_paths_choice_static` proves the corresponding FIFO-head result:
on a reused key it accounts for the earlier root announcement and receipt
before comparing sends inside the body. `source_originals_pure_bind_static`
also handles an initial `Bind` of `Pure`, using its actual returned value.
These results do not cover general nested value-dependent continuations.

`DeadlockPlayedPrefix.matched_partial_results` handles the value premise of
general `Bind`: for any matched prefix, the roles that have returned satisfy
the source well-formedness certificate's result relation on their actual
values. Other roles need not have returned. `actual_replay_laws` proves
this using the paired steps from that prefix; `entered_choices_agree`
identifies the common argument when at least one role entered a choice.
Neither result alone identifies the FIFO head at an arbitrary nested receive.

## Why the original projection fails

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

## Historical build evidence before the warning fixes

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
