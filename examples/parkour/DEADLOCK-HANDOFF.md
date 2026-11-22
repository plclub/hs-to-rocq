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
