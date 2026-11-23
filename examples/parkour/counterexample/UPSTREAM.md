# Reproduce the Cond ordering before and after the Haskell repair

With the [Parkour build dependencies](../README.md) installed, run the
Haskell regression from the repository root (also included in `make check`):

```sh
make -C examples/parkour check-cond-haskell
```

The runner [`scripts/check-counterexample-haskell`](../scripts/check-counterexample-haskell)
extracts the original HasChor sources at
`8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb` from Git into a temporary directory,
then runs the same program and observer ([`scripts/ObserveUpstream.hs`](../scripts/ObserveUpstream.hs))
against the repaired local checkout.
Observed with GHC 9.10.3:

```text
A: App { left = [Broadcast "True"], right = [SendTo "B" "()"] }
([SendTo "B" "()",Broadcast "True"],[ReceiveFrom "A"])
A: Bind { before = [Broadcast "True"], continuation = [SendTo "B" "()"] }
([Broadcast "True",SendTo "B" "()"],[ReceiveFrom "A"])
```

The first line comes from matching the owner's projected tree against
`App left right` and inspecting each branch separately. The second line
visits the right branch first. The repaired endpoint instead has a root `Bind`.
The observer checks its broadcast, passes the result to the continuation, and
checks the send there. The diagnostic requires `Root` on every
observed network action, checks that A returned, and checks that the unit
payload is not a Boolean. B's receive suspends the observer. The Rocq
counterexample separately proves that no enabled action exists in the
resulting configuration; merely observing a suspended receive would not
establish deadlock.
