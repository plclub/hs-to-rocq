# Generated library

The example Makefile generates `.v` and `.h2ci` files here from the pinned source
with `--target-version 9.0`. Compile them with Rocq 9.2 and the isolated
`examples/rocq9.2/` foundations. Do not edit generated files.

The user-approved `minViewWithKey` redefinition supplies that one algorithm body
through module edits to restore the source's empty-guard order. See the example
README and `ASSUMPTIONS.md` for the exception and regression evidence.
