# Proofs with opaque or axiomatized dependencies

Prove the requested theorem from approved contracts while preserving its
statement and the task's assumption budget. An opaque or axiomatized dependency
may prevent computation without preventing a proof through its contracts.

## Workflow

1. **Establish the theorem contract and assumption budget.** Read the task and
   the example's proof and assumption policy. Identify the target's input domain,
   premises, conclusion, and the definitions that give them meaning. Identify
   which transitive global assumptions the task permits for this result.

2. **Inspect the dependency and its contracts.** Read its declaration and
   relevant proof interfaces. An `Axiom` or `Parameter` has no body to unfold;
   an opaque definition or theorem may have a checked body. Find existing
   equations, specifications, and invariant or termination lemmas. Inspect their
   full types and `Print Assumptions` reports before relying on them: a contract's
   presence in the repository does not establish permission to use it here.

3. **Prove with authorized evidence.** Use approved contracts or explicitly stated
   premises already authorized for the target theorem. Discharge helper side
   conditions from those premises or proved lemmas. Keep the target's contract
   and the meanings of its predicates unchanged. Adding a premise, strengthening
   a validity predicate, or restricting the input domain can weaken the theorem
   without adding a global axiom.

4. **Report an insufficient contract.** If the available contracts and authorized
   premises do not discharge an obligation, report the exact remaining goal,
   available hypotheses, dependency, and missing contract or side condition.
   Request a user decision when the applicable policy requires one, before
   changing the theorem contract or assumption budget. Keep the proof blocked
   rather than inventing an axiom or adding an unauthorized admission.

5. **Check the result and its dependencies.** Compile with the example's required
   toolchain and load paths. Inspect the completed theorem's full type, including
   generalized section hypotheses, and its `Print Assumptions` report. Run the
   existing contract and assumption checks against the approved manifest or
   baseline, and run any required kernel checks. Report every mismatch. Record
   the checks actually run and the remaining dependencies.

`Print Assumptions` exposes transitive global dependencies; a report of
"Closed under the global context" leaves quantified premises intact. A `Qed`
marker or successful kernel check alone establishes neither axiom-freedom nor
consistency of the assumed contracts. Historical admissions in legacy examples
retain their documented status; their use must fit the current task's assumption
budget.

If the investigation establishes that the theorem is false, follow the existing
[counterexample and `Abort` convention](../CLAUDE.md#false-theorems).

## Existing contracts and audits

- **Finger-tree proofs:** read the [authorized assumptions](../examples/fingertree/ASSUMPTIONS.md#authorized-scope)
  and [theorem premises](../examples/fingertree/COVERAGE.md#how-to-read-the-contracts).
  The [guarded-recursion proofs](../examples/fingertree/ASSUMPTIONS.md#deferred-recursion-proved-guards-retained-axioms)
  discharge well-foundedness, `recurses_on`, and valid-input obligations before
  applying `deferredFix_eq_on`; the approved deferred axioms remain dependencies.
  Use the existing [build and audit commands](../examples/fingertree/README.md#build-and-check),
  which enforce exact transitive assumption sets, rather than inferring proof
  status from a manifest alone.
- **GHC proofs:** [WF contract recovery](../examples/ghc/README.md#wf-contract-recovery)
  shows how helper invariants are discharged without adding program-level
  premises to the final Exitify theorem.
  [RecoveryChecks.v](../examples/ghc/theories/RecoveryChecks.v) checks theorem
  types, rejects removed blanket contracts, and prints final theorem assumptions.
  The [validation record](../examples/ghc/README.md#post-rebase-validation)
  identifies the revision checked against the recorded assumption baseline.
- **Audit-tool controls:** the existing [assumption-audit tests](../test/README.md#assumption-audit-checks)
  exercise inventory checks, report parsing, and rejection of unexpected
  dependencies. They test the checkers, not the example proofs, and supplement
  rather than replace the example's audits.
