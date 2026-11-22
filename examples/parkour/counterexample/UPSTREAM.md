# Reproduce the ordering in Haskell

The owner already has a parallel `App` in the original Haskell endpoint.
With the [Parkour build dependencies](../README.md) installed, run this
diagnostic from the repository root:

```sh
make -C examples/parkour verify-source
stack exec -- runghc -XGHC2021 -XDataKinds -iexamples/parkour/upstream/src \
  examples/parkour/counterexample/ObserveUpstream.hs
```

Observed on GHC 9.10.3 at HasChor `8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb`:

```text
A: App { left = [Broadcast "True"], right = [SendTo "B" "()"] }
([SendTo "B" "()",Broadcast "True"],[ReceiveFrom "A"])
```

The first line comes from matching the owner's projected tree against
`App left right` and inspecting each branch separately. The second line
visits the right branch first. The diagnostic requires `Root` on every
observed network action, checks that A returned, and checks that the unit
payload is not a Boolean. B's receive suspends the observer. The Rocq
counterexample separately proves that no enabled action exists in the
resulting configuration; merely observing a suspended receive would not
establish deadlock.
