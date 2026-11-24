(* Match the priority checker's qualified, marker-free report format. *)
Require AssumptionFixture.

Check @AssumptionFixture.witness.
Print Assumptions AssumptionFixture.witness.

Check @AssumptionFixture.dependent_witness.
Print Assumptions AssumptionFixture.dependent_witness.

Check @AssumptionFixture.closed_control.
Print Assumptions AssumptionFixture.closed_control.
