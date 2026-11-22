# Install the Parkour ITree dependencies

[`install-itree-pins`](install-itree-pins) builds all three libraries from
fresh Git checkouts into a new directory. Run it from the repository root
with Git, Bash, GNU Make and Rocq 9.0.1 on `PATH`. For example, with a
prepared `rocq9` opam switch:

```sh
dest="$PWD/parkour-itree-prefix"  # must not already exist
opam exec --switch rocq9 -- examples/parkour/install-itree-pins "$dest"
```

The build uses up to four jobs; set `JOBS` to override. The script checks the
compiler version and reuses its core theories, Stdlib, Ltac2 and plugins.
It creates a private `ROCQLIB`, clears ambient Rocq load-path overrides,
and checks that imports of ExtLib, Paco and ITree all fail before installing
anything. It does not install into or select an opam switch.

| Logical root | Source revision |
| --- | --- |
| `ExtLib` | [`dd32f1c56f41d699ed2ffd4193a876c87fc44926`](https://github.com/rocq-community/coq-ext-lib/commit/dd32f1c56f41d699ed2ffd4193a876c87fc44926) |
| `Paco` | [`d0561bf7f0a96cac486ba3bd8ca0b72ce01fb9cf`](https://github.com/snu-sf/paco/commit/d0561bf7f0a96cac486ba3bd8ca0b72ce01fb9cf) |
| `ITree` | [`a2bc2c38ad998dccadb932559c922139dd957c4f`](https://github.com/DeepSpec/InteractionTrees/commit/a2bc2c38ad998dccadb932559c922139dd957c4f) |

The script verifies each checkout's `HEAD`, compiles the upstream library
targets to `.vo`, and installs them under `lib/user-contrib`. It uses the
upstream library build settings; upstream sources emit deprecation warnings.
The separate Parkour smoke test compiles `Resume.v` with `rocq c -q -w +all`.
It observes a visible event with a Boolean reply and proves that replying
`true` resumes its continuation at `Ret 1`.

To repeat that check using only the staged libraries and the same compiler:

```sh
opam exec --switch rocq9 -- bash -c '
  cd "$1"
  unset COQPATH ROCQPATH COQLIB ROCQLIB COQCORELIB ROCQRUNTIMELIB
  runtime=$(rocq c -config | sed -n "s/^COQCORELIB=//p")
  ROCQLIB="$PWD/lib" ROCQRUNTIMELIB="$runtime" rocq c -q -w +all Resume.v
' _ "$dest"
```

**Validation (2026-11-22).** A fresh private root on macOS with Rocq 9.0.1,
Stdlib 9.0.0 and OCaml 4.14.2 passed the initial missing-import checks and
the final resumption check. The installation contained 117 ExtLib, 41 Paco
and 68 ITree `.vo` files. The repeat command exited 0 without diagnostics;
a separate `Print Assumptions Resume.reply_resumes.` reported
`Closed under the global context`.
