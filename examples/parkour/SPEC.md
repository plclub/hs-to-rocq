# Goal: translate Parkour's Choreo2 to Rocq 9

**Goal for the session:** deliver a working `hs-to-rocq` translation of the pinned Choreo2 library path and its upstream `quorum-voting-choreo2` protocol in `examples/parkour/`. Build the two verification conditions first, then use their failures to drive the translation in the same session. **Done means `make -C examples/parkour check` succeeds from clean example outputs on Rocq 9.0.1**, including the generated projection, behavior checks, and upstream protocol.

## Inputs and scope

- Start from the upstream [`explicit-parallel` source at `8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb`](https://github.com/gshen42/HasChor/tree/8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb). Use `examples/parkour/upstream/` for the pinned source. Verify the source bytes used for translation match the pin; a checkout at the right commit can still have local changes.
- Build a fresh example in `examples/parkour/`. Do not consult, copy, modify, or depend on the `examples/haschor/` draft. The target is `Choreography.Choreo2` and its public `Choreography2` API.
- Use the in-tree `hs-to-rocq` with GHC **9.10.3**, `--strict --target-version 9.0`, **Rocq 9.0.1**, and the [Rocq 9 base](../rocq9.0/base/). Upstream targets GHC 9.6.7; keep any package-compatibility settings local to the example.

## Commands

Expose these Make targets from the repository root:

| Command | Pass condition |
| --- | --- |
| `make -C examples/parkour check-edits` | Every edit input to the real checked build satisfies VC1. |
| `make -C examples/parkour check-required` | A fresh translation of the pinned source satisfies VC2. |
| `make -C examples/parkour test-checks` | The real-tool positive and negative controls below give their specified results, independently of the progress of the port. |
| `make -C examples/parkour clean` | Removes regenerable example outputs and preserves upstream sources, edits, support modules, and tests. |
| `make -C examples/parkour check` | Runs the controls, enforces VC1 before real translation, regenerates and compiles all in-scope modules, enforces VC2, and passes the behavior and integration checks against those fresh outputs. |

Missing evidence or a failed prerequisite means a nonzero exit. A negative control passes only if it fails **for the specified reason**; a missing compiler or a parse error in a supposedly valid fixture does not count.

## Milestone 1: establish the verification conditions

### VC1. Check the edits actually used

1. Have the checker and the build use the same invocation and ordered list of edit files. Parse every `-e`/`--edits` input with [`runParser parseEditList`](../../src/lib/HsToRocq/Edits/Parser.y), before merging edits. Inspect the parsed directives recursively under `in` and `except in`. Reject an unlisted input or parse error; report the file, directive, and enclosing scope on a policy violation.
2. **Reject every `RedefinitionEdit`.** This applies even to an unused target, a scoped directive, or a replacement identical to the Haskell implementation. A comment containing the word `redefine` is not an edit.
3. Keep an explicit allowlist for example-owned edits. Start with structural directives such as `order`, `data type arguments`, and `equations`; record external-library name mappings as exact source/target pairs. Reject other directives by default. In particular, `rewrite`, `set type`/`no type`, `axiomatize`, `add`, skips that remove bindings or branches, and deferred termination are not general permissions. A new edit constructor must not be silently accepted.
4. Pin the shared [`base/edits`](../../base/edits) input, which already contains library rewrites and skips. Its **resolved contents** at repository revision `5e6a7bdd` have SHA-256 `ad3e975926fed9abc752ef614ca34f43b056d49f4f612831764602f293845d68`; do not derive the expected digest from the file under test. The unconditional `redefine` ban still applies. The complete [`examples/transformers/edits`](../transformers/edits) contains unrelated redefinitions; select only the rules needed for the Rocq 9 `ReaderT` dependencies.
5. Run the checked translator directly. Keep any external model in a named support module. Permit only explicitly listed import text if a preamble is needed. A manual Parkour `.v`, an injected body in a preamble or midamble, or post-processing of a protected output cannot supply a required function.

This policy covers the inputs to the example's translation commands. The existing Rocq 9 base is a dependency; rebuilding and auditing the entire base is outside this milestone.

### VC2. Require source-derived definitions

Keep a checked-in list of **original, fully qualified Haskell bindings**, their expected Rocq names, and an independent Rocq type contract. Protect the four library bindings below and apply the same check to the actual protocol entry point in the integration build. The types use upstream Haskell notation.

| Required source binding | Expected type |
| --- | --- |
| `Choreography.Choreo2.epp` | `forall m p a. Choreo m p a -> SSymbol p -> Epp m a` |
| `Control.Monad.Tree.interp` | `(Applicative m, Monad m) => (forall x. f x -> m x) -> Tree f a -> m a` |
| `Control.Monad.Tree.par` | `Tree f a -> Tree f b -> Tree f ()` |
| `Choreography2.runChoreography` | `(Backend config, KnownSymbol p) => config -> Choreo IO p a -> SSymbol p -> IO a` |
| `Main.quorumVoting` in upstream `examples/explicit-parallel/quorum-voting-choreo2/Main.hs` | `Choreo IO p ()` |

- **Origin:** add a small opt-in translator check that associates the original GHC binding, before edit renaming, with its emitted Rocq name. Count it only when a source-derived `ConvertedDefinitionBinding` produces a definition and output succeeds. The [binding alternatives](../../src/lib/HsToRocq/ConvertHaskell/Definitions.hs) and [emission cases](../../src/lib/HsToRocq/ConvertHaskell/Module.hs) already distinguish conversion, skipping, axiomatization, and redefinition. An intended `TranslateIt` decision alone is too early. Report each missing, substituted, or ambiguous binding by qualified name.
- **Fresh output:** regenerate into an empty directory. Load Parkour modules only from that run, with separate load paths for dependencies. A `.v` or `.h2ci` file, a matching identifier in a comment, or a `.vo` from a previous build is not evidence of origin.
- **Rocq contract:** compile the generated modules and a separate contract with `rocq c -w +deprecated-dirpath-Coq`. Check the exact type of each required definition. Run `Print Assumptions Choreography.Choreo2.epp.` and require its own `Closed under the global context` report; missing output, an axiom, or an admitted dependency fails. This closure requirement is for the pure projection, not the I/O runner. The [traversal check](../../test/identity-traversal.sh) shows how the repository checks compiler status and assumption reports. A type-correct handwritten body may be closed, so this contract complements the origin check.

### Acceptance controls

Use a tiny standalone Haskell module with a function whose result Rocq can compute. Exercise the public checker or translator interface with real tools. For origin failures also exercise VC2 independently, so an earlier VC1 rejection cannot accidentally pass the test.

| Input or change | Required result |
| --- | --- |
| Translate the fixture with an allowed structural edit and a comment mentioning `redefine`. | Both checks pass; Rocq computes the expected result. |
| Supply a valid direct, `in`, or `except in` redefinition, including through a second edit file. | VC1 rejects each input. An unlisted extra edit file also fails. |
| Omit, skip, axiomatize, or identically redefine the required fixture binding. | VC2 does not credit the binding as translated. |
| Supply a same-type handwritten replacement, or translate another module's function with the same short name. | Neither satisfies the required source identity. |
| Use a transparent alias to a same-type axiom in the Rocq contract fixture. | The type check succeeds; the assumption check fails. |
| First pass with a real definition; then remove the required binding and rerun with the old artifacts still available. | The second run fails with the missing binding. |

**Continue when the controls pass.** Run the real check and use its first failing input, binding, or Rocq obligation as the next implementation task. Preserve the edit policy and required bindings. If the translator needs a fix, reduce the failing construct to a regression and fix it in `hs-to-rocq`. If a fix requires changing the agreed semantics or trust boundary, present the reproducer and the decision needed; the goal is still incomplete.

## Milestone 2: complete the Choreo2 translation

The VC2 list protects key entry points; the deliverable includes the implementations they use. Generate and compile each row from the named sources.

| Source | Required result |
| --- | --- |
| `Control.Monad.Tree` | The indexed `Perf`, `Pure`, `App`, and `Bind` syntax, its instances, `par`, and the rank-2 `interp`. |
| `Choreography.Location`, `Choreography.Network` | The `LocTm` dependency, `SessionId` and its equality, `NetworkSig`/`Network`, and `exec`, `send`, `recv`, and `broadcast`. |
| `transformers` dependencies | `Control.Monad.Signatures`, `Control.Monad.Trans.Class`, and `Control.Monad.Trans.Reader` built against the same Rocq 9 base. |
| `Choreography.Choreo2` | `At`, `unAt`, `unwrap`, `ChoreoSig`, `Choreo`, the `Epp` reader and its operations, `locally`, `(~>)`, `(~~>)`, `cond`, `toLocTm`, and the recursive `epp` for `Locally`, `Comm`, and `Cond`. |
| `Choreography2` | The public typed API works for a consumer. `runChoreography` projects at the requested location, runs the reader from `Root`, and passes that network tree to `Backend.runNetwork`. |
| Upstream [quorum-voting-choreo2/Main.hs](https://github.com/gshen42/HasChor/blob/8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb/examples/explicit-parallel/quorum-voting-choreo2/Main.hs) | Translate and compile `Main.quorumVoting` itself, including its parallel composition and local continuations. Let GHC expand the upstream `mkLoc` splices. |

Preserve `At a l p` as a value accessed with evidence that `l = p`. Singleton comparison must produce an equality proof or a refutation; `unwrap` needs no `Default a`. Exercise `epp`'s recursive `Cond` continuation early. The execution boundary is the backend, including HTTP, and the program's primitive I/O and STM operations. These may be modeled externally; the choreography, projection, session-ID assignment, and quorum-voting body must come from Haskell.

## Milestone 3: exercise the generated code and finish

Compile independent Rocq assertions against the generated `epp`, with concrete expected results and no admitted or assumed projection equations:

- Project one communication at its sender and receiver. Check that the `Send` and `Recv` identify each other and carry the same session ID.
- Project an `App` under a known session ID. Check the left and right child IDs against the corresponding `Nest` constructors. Exercise the public `par` combinator too. In a separate `Bind` example, check that sequential actions retain the parent ID.
- Project a `Cond` at its owner and at a peer. Check that the owner broadcasts, the peer receives, and projection continues with the chosen value.
- Instantiate the **generated `Main.quorumVoting`** at `candidate`, `voter1`, `voter2`, and `voter3`. Have Rocq typecheck all four projected `Network IO ()` terms starting at `Root`. This checks the real consumer without requiring live HTTP servers or an STM scheduler.

Document dependency setup, the pin, the runtime boundary, and the reproduction commands in `examples/parkour/README.md`; link the example from the repository README. If the translator changed, run its Haskell suites and the affected shared compiler regressions.

**Final acceptance:** from the repository root in the documented toolchain, run:

```sh
make -C examples/parkour clean
make -C examples/parkour check
```

Report the upstream SHA, tool versions, exit status, and `epp` assumption result. Success requires the clean end-to-end check above; passing only the checker fixtures, generating `.v` files, or reporting the next blocker is an intermediate state.
