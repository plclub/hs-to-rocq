# Check the choice owner's send order

## Haskell regression

With the [Parkour build dependencies](../README.md) installed, run the
Haskell regression from the repository root (also included in `make check`):

```sh
make -C examples/parkour check-cond-haskell
```

The runner [`scripts/check-counterexample-haskell`](../scripts/check-counterexample-haskell)
extracts the original HasChor sources at
`8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb` from Git into a temporary directory,
then runs the same program and observer ([`scripts/ObserveUpstream.hs`](../scripts/ObserveUpstream.hs))
against the repaired local checkout. On the original endpoint, the owner has
an `App`: the right branch can send `"()"` before the left branch broadcasts
`"True"` on the same `Root` FIFO. On the repaired endpoint, a `Bind` puts the
broadcast first. The observer stops at B's receive; it does not decide
whether the network can step.

## Rocq counterexample

[`scripts/check-counterexample`](../scripts/check-counterexample) checks the
[expected bad run](EXPECTED.md) and the proof that its residual network cannot
step. Run it in a separate copy of the example with these inputs already
compiled by the same Rocq switch:

- `lib/` containing the **original** `Choreography.Choreo2` from HasChor
  `8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb` and its dependencies;
- `build/run/base`, `build/run/manual`, and `build/run/transformers` on their
  usual load paths.

Only `src/Choreography/Choreo2.hs` differs between the two pins. You can reuse
the compiled dependencies in the separate copy: regenerate `Choreography.Choreo2`
from the original `src/` tree with the [Parkour translation flags](../scripts/build-example.py)
and compile it against those dependencies. Then run `scripts/check-counterexample`
from that example directory. The regular `make check-required` generates the
**repaired** owner `Bind`, which cannot witness the original `App` schedule.
