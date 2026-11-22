# Goal: prove that Parkour EPP preserves deadlock freedom

**OpenCode goal:** Prove in Rocq that if a well-formed choreography is deadlock-free, the network of its **generated** `Choreography.Choreo2.epp` endpoints is deadlock-free. Cover every finite network execution, including every legal ordering of endpoints and parallel branches. The library theorem is the deliverable. `Main.quorumVoting` is a client of it.

**TDD goal:** Keep the implemented semantics, theorem statements, and proof assumptions faithful to this specification. A proof of a weaker theorem, or of the right words about different semantics, must not pass. Use kernel-checked propositions, exact type checks, compiler exit statuses, and deterministic scripts. Do not ask an agent or model to judge a result a tool can check. The *semantics* admits many schedules; the *tests* do not sample schedules.

**Done:** A clean `make -C examples/parkour check` regenerates the pinned inputs, compiles with **all Rocq warnings enabled and fatal**, proves the contracts below, and checks each named theorem's assumptions. The implementation agent works the red/green slices below; it does not renegotiate the theorem to finish a slice.

## 1. The public theorem

Use these mathematical contracts for the independent Rocq type checks. Quantify over the local computation type `m : Type -> Type`, its shared local semantics, the initial stores and input state, a finite list `R` of distinct participating roles, `A : Symbol -> Type`, and the **actual** family `c : forall p : Symbol, Choreo m p (A p)`. Require the source well-formedness condition in §2, including role closure and the applicable codec laws. These are the common inputs to all four statements.

`C0` is the initial source state for `c` on `R`, with no pending deliveries. `N0` has the same initial stores, empty FIFOs, and exactly one endpoint at each `p` in `R`:

```coq
Control.Monad.Trans.Reader.runReaderT
  (Choreography.Choreo2.unEpp
     (Choreography.Choreo2.epp (c p) (@Parkour.Symbol.MkSSymbol p)))
  Choreography.Network.Root
```

This is the term the [pinned runner](upstream/src/Choreography2.hs#L43-L46) passes to the backend. Do not substitute a handwritten projector or an arbitrary family of network programs.

```text
run_X(x0, t, x)  := zero or more X-steps from x0 to x, in trace order t
ready_X(x)       := final_X(x) or (there exist a, x' such that x --a-->_X x')
DF_X(x0)         := for every t, x, run_X(x0, t, x) implies ready_X(x)
stuck_X(x)       := not final_X(x) and there are no a, x' with x --a-->_X x'
```

| Qualified export to check | Required claim |
| --- | --- |
| `DeadlockFreedom.epp_preserves_deadlock_freedom` | `DF_C(C0) -> DF_N(N0)`. This is the headline theorem. |
| `DeadlockFreedom.network_run_has_source` | For **every** `tn, n` with `run_N(N0, tn, n)`, there exist `tc, s` with `run_C(C0, tc, s)` and `matches(tc, s, tn, n)`. |
| `DeadlockFreedom.matched_ready` | For **every** reachable pair of runs satisfying `matches(tc, s, tn, n)`, `ready_C(s) -> ready_N(n)`. No global `DF_C` premise on this lemma. |
| `DeadlockFreedom.deadlock_reflection` | For every `run_N(N0, tn, n)` with `stuck_N(n)`, there exist `tc, s` with `run_C(C0, tc, s)`, `matches(tc, s, tn, n)`, and `stuck_C(s)`. |

The last three claims still say something about a choreography that can block on *some* inputs. One unrelated blocked source execution cannot explain a network deadlock. A local call may block or diverge. A blocked branch does not deadlock the whole choreography while a sibling can act. No local totality, fairness, eventual delivery, termination, source determinism, or source/network equivalence premise belongs in these types. This is a theorem about a reliable network model, not a refinement theorem for live HTTP.

## 2. Source: one choreography and its steps

**Basis.** [Shen, chapter 4, §§4.2.2–4.2.3](https://escholarship.org/uc/item/8jg7m051) and the [Parkour manuscript, §§2.2–2.3](https://lastland.github.io/pdfs/Parkour.pdf#page=5) distinguish ordinary out-of-order execution from explicit parallelism at the same role. [Cruz-Filipe and Montesi, §3, Figs. 9–11](https://www.fabriziomontesi.com/files/cm17-ice.pdf#page=7) split a communication into send and receive linked by a fresh source occurrence. Unfolding that split is not an action. Adopt that distinction, not the entire calculus. The role-local rule for higher-order `Bind`, applicative join, blocking local effects, and asynchronous `Cond` below are **our formalization**. The papers do not supply a Parkour progress proof; the [pinned `Choreo2`](upstream/src/Choreography/Choreo2.hs#L53-L109) supplies syntax and projection, not an independent global interpreter.

**Well-formedness condition.** Define a source-only structural relation indexed by `R` and the actual `c`. A common source constructor must account for the participating components, including the same owners, senders, receivers, and communicated type at each occurrence. Cover `Pure`, `Locally`, `Comm`, `Cond`, `App`, and `Bind`. In particular:

- Track related **families of actual values** at hidden intermediate types. At `Bind`, require the continuations on related prefix results to describe one choreography, including among roles that already have their arguments while another role is blocked. A condition quantified only over *complete* result tuples can be vacuous: if A waits for a value of an empty type, B and C can still enter their continuations with their off-role `At` values and must still agree on who sends. At `App`, relate both branches and the application of their results. At `Cond`, cover the continuations for each common announced value. Do not demand equality of arbitrary values of different `A p`, or of functions by extensionality.
- `At X l p` carries `(l = p) -> X`. The owner can obtain the actual `X` using equality evidence. A non-owner can construct its empty representation from `l <> p`, without obtaining an `X`. Apply local code to the correct `unwrap` and real prefix results, including opaque handles returned by local calls.
- Cover every role named in the admitted continuations. Extra configured roles are allowed and participate in announcements. For each value put on the wire require `read_receiver (show_sender x) = Some x` with the **actual dictionaries** at that occurrence. This includes every peer's decoder at `Cond`. Self-communication needs no wire law. A final result need not be serializable or uniform across roles.
- Prove that the two-role family choosing `B -> A` at A and `A -> B` at B **does not** meet the condition: both would receive. Prove positive cases, including a located result and the actual quorum client. Neither the type `forall p, ...` by itself, nor a premise saying that the endpoints match or progress, is the condition.

**`cstep`.** Keep source positions per role and per parallel branch, the results actually available there, local stores, and the sends or announcements still owed a receive. Identify an occurrence from the *source* execution, independently of `Network.SessionId`. A typed source value need not be a wire string. The following rules fix the observable behavior; the private representation may vary.

| Construct | Rule |
| --- | --- |
| `Pure` / `Locally` | Pure results are silent. At the owning role, advance the local computation using §3; non-owners obtain the off-role `At` silently. |
| `Comm A x B`, `A <> B` | A can send its actual `x` without B being ready. A send records a pending delivery at this occurrence. B can receive that value only after this send; its located result at B is then available. Other roles do no communication. For `A = B`, return the original located value locally, with no send or receive. |
| `Bind t k` | A role enters **its own** `k` only after its part of `t` has returned its actual argument at that role. It need not wait for other roles. Never guess an argument of `k`, even if an unrelated role is blocked. Ignoring an argument does not let a role skip its earlier action. |
| `App f x` | Both branches can act, even at the same role. A role joins only when it has both local results, then applies the returned function to the returned argument silently. `par` uses the actual [`Tree.par`](upstream/src/Control/Monad/Tree.hs), not a global barrier between roles. |
| `Cond owner v k` | The owner announces the value it actually holds and may enter `k v` immediately. Each other configured role waits for **its own** receive of that announcement before entering `k` on the same value. Do not require all peers to receive together. |

Without `par`, B can act in `A locally wait; B locally act`. B cannot act before its own receive in `A -> B : x; B locally act`, even if it ignores `x`, and cannot forward `f(x)` before receiving `x`. In `A -> B : x; A -> C : y`, with independent payloads, A's sends stay in order but the second need not wait for B's receive. `cfinal` means every role and branch has finished **and** no intended source receive is outstanding, modulo finite pure bookkeeping.

## 3. Network, local effects, and matching

Use ITrees **for local computations**. Supply an interpretation from `m X` to `itree E X` and a stateful relation for replies, conceptually `reply(p, event : E X, store, x : X, store')`. Both source `Locally` and target `Exec` use this same interpretation, the same initial stores, and the same observed outcomes. At `Vis e k`, an enabled reply advances the computation to `k x` in the updated store. No reply means the event cannot step. Branches at one role share its store. `Exec` is resumable between events; it does not run a whole IO action atomically. The library theorem quantifies over this model; it does not assume laws about all values of [`Runtime.IO`](manual/Parkour/Runtime.v).

Interpret the **generated** [`NetworkSig` and `Tree`](upstream/src/Choreography/Network.hs) as follows:

- `nstep` chooses **one** genuine enabled action from any endpoint or live branch. Keep `App` as a fork/join node: a step of `L` gives a step of `App L R`, and a step of `R` gives a step of `App L R`, threading the updated shared state. Join `Pure f` and `Pure x` silently. Do not implement `App` by binding the left ITree before starting the right. Endpoint `Bind` uses the actual returned value.
- Start with empty reliable FIFOs keyed by `(sender, receiver, generated session ID)`. `Send` enqueues the sender's encoded value without waiting for a receive. `Recv` consumes **only** the head of its exact key and returns the decoded value. An empty queue, wrong key, or undecodable head supplies no successful receive. Use the IDs already present in the generated tree; do not repair them in the interpreter.
- `BCast` is one announcement: atomically enqueue once for **every other configured participant**, never the owner. Peer receives are separate actions. A one-role `Cond` leaves no self-message. The [HTTP implementation](upstream/src/Choreography/Network/Http.hs#L120-L158) includes the sender in its configured list and can log a failed send. It is not the model.
- Look through **finite** bookkeeping on both sides to expose an action or a return. `Pure`, pure function application, `Bind` of a returned value, completed joins, ITree `Ret`, and finite `Tau` sequences do not themselves witness progress. Infinite silent `Tau` alone witnesses neither a return nor an enabled action. Use finite derivations, not a fuel cutoff or an assumption that every ITree normalizes. A scheduler tick, polling an empty FIFO, or retrying unchanged STM is not an action.
- `nfinal` requires all endpoints and branches to have returned **and every FIFO to be empty**. All endpoints returned with an orphaned message is unfinished and stuck. An announcement followed by a blocked quorum branch is not final on either side.

**`matches(tc, s, tn, n)` relates particular histories and their current states.** Match every genuine action in the network's observed order to the source occurrence and role responsible for it. Record the actual local event/reply and store, branch choices and results, and the pending deliveries to each recipient. Relate each typed pending value to its encoded FIFO entry, including its position. The relation must admit a prefix stopped between send and receive. It must not consult `ready`, assume the next step exists, or replace a prefix by an unrelated history.

Prove the connection between source occurrences and **generated** IDs: `App` nests left and right sessions, `par` has its actual nested `App` shape, and `Bind` can reuse the parent ID. Two sequential sends of `true`, then `false`, from A to B can both use `Root`. After both sends the relation owes **two distinct** pending receives, in order; B cannot receive `false` first. A raw network queue carries the actual wire data, not extra source tags that tell the receiver which entry to take.

## 4. Deterministic acceptance gates

Keep the acceptance contracts separate from the implementation. Write expected propositions from §§1–3 and use fixed roles, literal outcomes, and positive **and negative** examples. Compile independent declarations of the form `Definition ... : <agreed quantified type> := @<export>.` Spell out the quantifiers, both run relations, and both sides of readiness in the contract; do not infer the expected type from the export. Fix the agreed definitions used by those types as well: changing `well_formed` to `False` could otherwise leave a type check green. Use the declarative rules directly, or prove that the private machine admits exactly their observable steps and finals on the states in question, in both directions.

Mechanically protect the expectations as proof work proceeds. Pin this spec's SHA-256 in the goal handoff. Before proving each slice, record its independent statements, fixed inputs and expected results separately from proof bodies. Compare the acceptance inputs to the frozen revision or read-only digest manifest on reruns; do not compute the *expected* digest from the current working copy. A newly added test can extend the set. Rewriting an existing expectation or axiom ceiling is a contract change, not a way to pass a test.

Use deterministic dependency checks where applicable (`Print All Dependencies` on Rocq 9.0.1): `cstep` and well-formedness must not call `epp` or the network step relation, even through a helper. `matches` and well-formedness must not depend on readiness or the theorem. Importing the generated module to use its **syntax** is expected. Keep the local model inputs limited to effects, replies, and state; do not hide a simulation or progress premise in a model record.

**Warnings are errors.** Route every Parkour acceptance invocation of the Rocq compiler through `rocq c -q -w +all`, including generated modules, support modules, old and new theories, fixtures, and assumption queries. `-q` skips the rcfile; **do not use `-quiet`**, which implies `-w -all`. Keep the real compiler exit status and diagnostics; fail on any remaining Rocq warning. Do not suppress categories in flags, `.v` files, or imported project configuration. The existing [`build-example.py`](build-example.py) and [`test-checks.sh`](test-checks.sh) promote only `deprecated-dirpath-Coq`; that is not this gate.

Use the production compiler invocation on three isolated controls. `Definition good : nat := 0.` must compile cleanly. `Arguments Nat.add n m.` must fail with `arguments-assert`. `Reserved Notation "( x | y )" (at level 0).` must fail with `disj-pattern-notation`: on 9.0.1 the latter compiles silently with default warnings, so it distinguishes **all warnings** from just the default set. An expected rejection passes only on nonzero exit **and its own diagnostic**.

**Known initial red, not a waiver:** on the checked Rocq 9.0.1 installation, even a file containing `From Stdlib Require Import ZArith.ZArith.` fails under `-w +all`: it transitively imports the deprecated `Stdlib.ZArith.ZArith_base`. `Require GHC.Base.` with the Rocq 9 base on the load path reproduces it; the existing Parkour `Tree`, `Choreo2`, `Main`, and `Behavior` files encounter it too. Resolve the cause at the appropriate source/dependency or report the exact pin conflict. Editing generated files, downgrading the warning, or declaring the old clean check equivalent is not a fix.

**Assumptions are part of TDD.** Run a fresh, single-query `Print Assumptions <qualified export>.` per declaration. Bind model inputs as theorem arguments; a closed theorem can still have a bad extra premise, which is why the independent type checks also run.

| Artifact | Machine-enforced policy |
| --- | --- |
| Generated `Choreography.Choreo2.epp`; all four §1 exports; generic semantic acceptance lemmas | Exactly one `Closed under the global context` report per query. No global axioms, admissions, functional extensionality, or proof-irrelevance axiom. Keep full kernel checking; no `.vos`-only builds or disabled guard, positivity, or universe checks. |
| `DeadlockQuorum.quorum_well_formed` and `DeadlockQuorum.quorum_deadlock_freedom` | Closed, or every reported dependency belongs to the fixed set below. Resolve abbreviated names to their qualified names (e.g. `Locate Runtime.IO.`). No prefix wildcard and no allowlist regenerated from the proof being tested. |
| Audit itself | Reject a same-type transparent alias to a fixture axiom and name that axiom. Reject a client fixture mixing one allowed parameter with an unlisted axiom. Reject an otherwise closed export with an extra premise at the **type** gate. Missing, duplicate, stale, or unrelated reports cannot pass. |

The allowlist ceiling for the client is the following **14 constants in `Parkour.Runtime`**: `IO`, `STM`, `TVar`, `returnIO`, `bindIO`, `returnSTM`, `bindSTM`, `getLine`, `putStrLn`, `newTVarIO`, `readTVar`, `writeTVar`, `retry`, `atomically`. These are the parameters reported by `Print Assumptions Main.quorumVoting` in the existing 9.0.1 build, not logical laws. A proof may use fewer. No HTTP primitive or axiom asserting well-formedness, message agreement, or progress is allowed.

Reuse the existing [single-query checker and axiom-alias control](test-checks.sh#L11-L34). Keep source origins from [`required.tsv`](required.tsv), the edit audit, clean translation, and the preexisting `ReaderTree`, `Required`, `Behavior`, and `Integration` checks. In particular, the fixed-reply observer in [`Behavior.v`](theories/Behavior.v) is a translation regression, not an oracle for concurrent progress.

## 5. Red/green and proof workflow

Use the repository's GHC **9.10.3**, Rocq **9.0.1**, and upstream `8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb`. Follow the [build guide](README.md) for the base, submodules, and translator. Pin local-effect dependencies to immutable revisions: [Interaction Trees `a2bc2c38ad998dccadb932559c922139dd957c4f`](https://github.com/DeepSpec/InteractionTrees/commit/a2bc2c38ad998dccadb932559c922139dd957c4f), [Paco `d0561bf7f0a96cac486ba3bd8ca0b72ce01fb9cf`](https://github.com/snu-sf/paco/commit/d0561bf7f0a96cac486ba3bd8ca0b72ce01fb9cf), and [ExtLib `dd32f1c56f41d699ed2ffd4193a876c87fc44926`](https://github.com/rocq-community/coq-ext-lib/commit/dd32f1c56f41d699ed2ffd4193a876c87fc44926). The installed sources and resumption interface were checked on 9.0.1; an opam label of `dev` is not a lock. Document and verify a fresh installation from these pins.

The commands below run from the repository root. **K** = `make -C examples/parkour test-checks` (checker controls); **R** = `make -C examples/parkour check-required` (fresh generated inputs). Register each new theory in [`build-example.py`](build-example.py#L99-L123) in dependency order; it does not discover `.v` files automatically. A focused compile may shorten a proof cycle; it does not replace **R**. Keep expected results independent of the implementation: no regenerated golden answers, finite schedule search as a substitute for a universal proof, or agent-scored output.

Work one assertion at a time within these slices. Red means the named behavior, theorem, or trust check fails for the intended reason. A bad load path, syntax error, or different compiler error is not evidence that a behavioral test is sensitive.

| Slice / acceptance artifact | Run | Intended red → green evidence |
| --- | --- | --- |
| 1. Warning, theorem-type and assumption controls (`test-checks.sh`, `tests/`) | **K**, **R** | Demonstrate that the old warning policy misses the default-disabled probe and that a type alone accepts an axiomatic proof. Green rejects those controls for their named reasons, accepts the clean controls, and compiles the real inputs warning-free. |
| 2. Source ordering (`theories/DeadlockSourceCases.v`) | **R** | A global `Bind` barrier prevents B's step past blocked A. Prove that step without `par`; then prove B cannot bypass its own receive or forward its value early. Check the two ordered A-sends with B's receive delayed. |
| 3. Well-formedness (`theories/DeadlockSourceCases.v`) | **R** | A condition accepting every role family admits the two receivers; an empty condition rejects everything. Prove the negative example, positive communicating and located-result examples, and rejection for an absent required role or mismatched wire codec. |
| 4. Scheduling and finality (`theories/DeadlockNetworkCases.v`) | **R** | A left-first scheduler strands an enabled send. Exhibit send-then-receive on an empty channel, both successors for two ready sends, and **no** successor for two empty receives. At one role, show `par (Exec waitForFlag) (Exec setFlag)` can step right and then left using the updated store. Check pure return/join, silent-only looping, and an orphaned FIFO against readiness/finality. |
| 5. Communication and choices (`theories/DeadlockRunCases.v`) | **R** | A wrong tag, swapped FIFO entries, or invented choice must not explain the expected run. Use actual projected `App`/`par` IDs, the two `Root` sends, self-`Comm`, one-role `Cond`, and a multi-peer announcement with one peer still pending. Prove the positive match between send and receive and specific negative matches. |
| 6. Introduced deadlock control (`theories/DeadlockRunCases.v`) | **R** | Use a well-formed, deadlock-free single-message source. In a **fixture only**, omit its send or give it the wrong ID. Exhibit the reachable unfinished, stuck network and the failed matching/progress obligation. The real generated endpoints for the same source must pass. Do not mutate the pinned source or count an ill-typed mutant as a rejection. |
| 7. Library (`theories/DeadlockFreedom.v`, independent `theories/DeadlockContract.v`) | **R** | A single favorable schedule or a theorem conditional on target progress cannot inhabit the required contracts. Prove all four exports, compile the independent types, and pass every theorem-specific assumption query. |
| 8. Client (`theories/DeadlockQuorum.v`, independent client type check) | **R**, then final clean check | Four endpoint type checks do not prove well-formedness. Prove it for `@Main.quorumVoting` on `candidate`, `voter1`, `voter2`, `voter3`; obtain the preservation corollary for the actual four `Root` endpoints under the shared local model. Run both client assumption audits. Do not assume the client's well-formedness or assert unconditional termination/progress of its STM program. |

**Proof order for slice 7:**

1. Establish the initial match from source well-formedness and the generated constructors. Prove the local `epp` equations, `App` path separation, and FIFO ordering for reused sessions. Carry enough source position, local value, and pending-delivery information across a step; do not try to reconstruct erased source code by inverting one endpoint.
2. Prove the step lemma in the **network-to-source** direction: extend the source history that explains the prefix, using the actual next network action and reply, up to finite bookkeeping. Induct on the finite network run to prove `network_run_has_source`. Source nondeterminism does not license choosing a different input. A source-to-network simulation alone does not prove this clause.
3. Separately prove `matched_ready` for every reachable pair admitted by `matches`. Analyze source finality or an enabled source action and exhibit network finality **or an actual enabled network action**. A network-to-source step lemma is vacuous at a stuck network. If a stronger internal invariant is needed, establish it for the pairs to which the public statement applies.
4. For an arbitrary reachable network use its matching source run; apply `DF_C` and then `matched_ready`. For reflection, unfinished and stuck rules out both ways the network could be ready, hence both ways the matching source could be ready. Neither argument requires a fairness or choice axiom.

**Final commands:**

```sh
make -C examples/parkour clean
make -C examples/parkour check
```

Report tool and source pins, exit statuses, warning controls, exact theorem types, and each assumption report. Preserve the [translation baseline](SPEC.md). If a fix touches the translator or shared base, also run `stack test` and the affected shared compiler fixtures in **both** environments (`make -C examples/tests` and `make -C examples/rocq9.0/tests`); for a Rocq 9 base change, rebuild `make -C examples/rocq9.0 base` before clean Parkour validation.

**Return to the user rather than changing the problem.** If a well-formed counterexample falsifies a public claim, record the family and proof of well-formedness, model and initial store, concrete finite history, residual states and queues, and the exact failed obligation. Give a kernel-checked counterexample when expressible; do not admit the false statement. Distinguish that from an insufficient proof invariant. Likewise report a necessary new observable rule, axiom, or incompatible pinned dependency with a minimal reproducer. Do not change this spec, weaken a condition or check, suppress a warning, or bless a new assumption to turn red into green.
