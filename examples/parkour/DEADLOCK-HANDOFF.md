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
