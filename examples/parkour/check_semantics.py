"""Validate the semantic slices against one freshly generated Parkour tree."""

import argparse
import hashlib
import re
import shutil
import subprocess
import sys
from pathlib import Path

from itree_pins import PARKOUR

# Amendment reviewed in d3da6461. The historical manifest and every public
# proposition in it retain their original bytes.
REVIEWED_SOURCE = "224836b4f55e3c45dbca506c31965ff293d280c2db26806a74f701bf295e14eb"

MANIFESTS = {
    "DeadlockConcreteContract.sha256": "8996f8d5c8167285255418f402fadddccf50ae0f82e44ab913bbbec1a072977d",
    "DeadlockSourceOccurrenceExpect.sha256": "d2231dd81efc5f5f06ef43ce596f98f637220adc9a247e51c7aaf2d63e64dcff",
    "DeadlockSourceOccurrenceAmendment.sha256": "9971b74303f3e5e9937067d3a2358e487174396cc8318db603516991ea5a6dd9",
    "DeadlockProjectionExpect.sha256": "06588db992d1e953fcc2fc578b7ca5edf496e1a28ce465cdf171fb5a164c96ae",
    "DeadlockLibraryExpect.sha256": "c91b31607d06c104e763fe3feb574bca467911b2ebd4b1a4981c721f44d68b66",
    "DeadlockMutationExpect.sha256": "2dfd6665bfa0a76917c3a7c409c5c95aa13ff1810ffc48ae684c68e08773e3de",
    "DeadlockRunsExpect.sha256": "9874357e3c0422a9192628130303e1000cd0fa30e7f8639d21e1af3ae5526ad7",
    "deadlock-source-ordering-v2.sha256": "f11384df42257135cff135685de88bda7b53dbdbe2af780fda2383feb1398c9a",
    "deadlock-source-extra-v1.sha256": "e2c4a5922bf748964f8ec6575ca30a4a8ccb6b86c3ea731679f211dbb168a128",
    "DeadlockOrderExpect.sha256": "37162926b6b33b04eb1c3fee0edde9a1d3f93870d67f4935bdcf704fd4ad913c",
    "DeadlockWellFormedExpect.sha256": "2fb66452ddf3189e8ba70c5d553d3f04d630238b1a86f4fcee52a1ca3e28a5f2",
    "DeadlockWellFormedPartialExpect.sha256": "4f8922b22f3403d58383714569d5cb878063ff3df7e65c9f589e43d3fc7acfb6",
    "deadlock-network.sha256": "1f552cc30287fd1ae364039ff3d65f0dad329dde1484d626cda78be059a506d4",
    "deadlock-network-expect-v1.sha256": "1414d09949cc46ff4e8a5bd9b4a64b48bf80cf1fa9784e43814a987443fcbbf4",
    "deadlock-network-more-v1.sha256": "4c33d108db7b7f771a662a70e55172b017e9169925a5094f596c1f96f740c1cd",
    "deadlock-network-silent-v1.sha256": "f0199afa57d067ecba09418b9d50b8def0f3b15991bf7372fba430f8961a8bfa",
    "DeadlockQuorumExpect.sha256": "2c2099a22e44e6231bddb7a214b05b965dad8b5e7e0286a82fffc7c8631ec6ec",
}

NETWORK = ("theories/DeadlockNetwork", "tests/DeadlockNetworkExpect",
           "tests/DeadlockNetworkMoreExpect", "tests/DeadlockNetworkSilentExpect",
           "theories/DeadlockNetworkCases")
MODULES = ("theories/DeadlockRuns", "tests/DeadlockRunsExpect", "tests/DeadlockRunsCases",
           "theories/DeadlockState", "tests/DeadlockStateExpect", "tests/DeadlockStateCases",
           "theories/DeadlockSource", "theories/DeadlockSourceExpect",
           "theories/DeadlockSourceExtraExpect",
           "theories/DeadlockOrder", "tests/DeadlockOrderExpect", "theories/DeadlockChronology",
           "theories/DeadlockWellFormed", "tests/DeadlockWellFormedExpect",
           "tests/DeadlockWellFormedPartialExpect", "tests/DeadlockWellFormedCases",
           "tests/DeadlockSourceOccurrenceExpect", "theories/DeadlockSourceCases",
           *NETWORK, "theories/DeadlockProjectionExpect", "theories/DeadlockProjection",
           "tests/DeadlockEnabledExpect", "theories/DeadlockEnabled", "tests/DeadlockEnabledCases",
           "theories/DeadlockStepView", "theories/DeadlockMessages", "tests/DeadlockMessagesExpect",
           "theories/DeadlockPartialValues", "theories/DeadlockRoster",
           "theories/DeadlockAlignment", "theories/DeadlockSourceView", "theories/DeadlockAlignmentProgress",
           "tests/DeadlockAlignmentProgressCases", "theories/DeadlockMatch",
           "theories/DeadlockMatchStep", "tests/DeadlockMatchStepExpect", "theories/DeadlockHead",
            "theories/DeadlockFrontiers", "tests/DeadlockRepairMatchCases", "theories/DeadlockFreedom",
            "theories/DeadlockCoherence", "theories/DeadlockReplay", "theories/DeadlockPlayedValues",
            "theories/DeadlockPlayedFamily", "theories/DeadlockPast",
            "theories/DeadlockCoverage", "theories/DeadlockCutSafety",
            "theories/DeadlockSameHistory", "theories/DeadlockRootOrigin", "theories/DeadlockFrontierCoverage",
           "tests/DeadlockLibraryExpect", "tests/DeadlockMatchExpect",
           "tests/DeadlockQuorumFreedomExpect", "tests/DeadlockContractParametric",
           "tests/DeadlockMutationExpect", "theories/DeadlockMutationCases",
           "theories/DeadlockRepairCases", "tests/DeadlockQuorumExpect",
           "theories/DeadlockQuorum", "tests/DeadlockQuorumCases")
CLOSED = {
    "DeadlockFrontiers": "decorated_ledger prefix_ledger reachable_head_from_coverage",
    "DeadlockCoherence": "initial_actor_history history_bind_receive run_completed_partial_histories",
    "DeadlockReplay": "code_history_has_syntax_cut syntax_cut_role_step",
    "DeadlockPlayedValues": "received_original_value owner_locally_actual_result",
    "DeadlockPlayedFamily": "structural_played_family",
    "DeadlockPast": "matched_has_actual_past production_recorded_in_replay",
    "DeadlockSameHistory": "production_at_current_sender queued_operand_at_receiver",
    "DeadlockRootOrigin": "packet_from_root_program root_queued_operand source_originals_root",
    "DeadlockFrontierCoverage": "matched_received_safe matched_future_unreceived",
    "DeadlockCoverage": "shared_node_paths returned_cut_completed completed_subtree_coverage",
    "DeadlockCutSafety": "replay_receive_site aligned_cut_receive_safety aligned_cut_delivery_available covered_residuals",
    "DeadlockHead": """nonempty_channel_first removal_has_key queued_key_nonempty head_bytes exact_receive_at
        source_removal_exposes_wire""",
    "DeadlockChronology": """role_history_chronology code_history_chronology history_scoped scoped_fork_disjoint
        code_history_fork_disjoint""",
    "DeadlockSourceView": """silent_result silent_live source_returns_result result_source_returns cursor_result_exact
        source_step_live live_source_step cursor_live_exact silent_returns_iff silent_actions_iff""",
    "DeadlockAlignment": "initial_alignment aligned_returns network_action_reflects",
    "DeadlockAlignmentProgress": """aligned_result source_return_is_network_return empty_delivery_available
        aligned_live source_action_is_network_enabled source_action_exposes_network_action aligned_role_ready
        generated_source_action_exposes_network_action""",
    "DeadlockAlignmentProgressCases": """left_first_alignment right_first_source_return opposite_bookkeeping_return
        generated_parallel_exposes_real_action generated_off_role_prefix_exposes_real_action
        resumed_local_exposes_real_action typed_receive_is_source_enabled empty_wire_receive_is_not_network_enabled
        occurrence_receive_skips_same_lane strong_fifo_still_rejects_second_delivery
        occurrence_availability_rejects_bad_wire_head occurrence_availability_accepts_other_decodable_payload""",
    "DeadlockRoster": "roster_step schedule_role all_returns",
    "DeadlockPartialValues": "add_value_valid select_returned roster_member_unique",
    "DeadlockMatchStep": """receive_delivery delivery_represents aligned_decorated_step endpoint_decorated_step
        state_step matched_prefix_step initial_safe_residuals initial_prefix_step""",
    "DeadlockMatchStepExpect": "generated_sender_action nonempty_actual_prefix safety_does_not_require_readiness",
    "DeadlockFreedom": """empty_network_run_has_source matched_network_final matched_source_final
        initial_inputs_available matched_ready_from_inputs network_run_snoc_view schedule_from_safe_receives
        preservation_from_frontiers reflection_from_frontiers""",
    "Choreography.Choreo2": "epp",
    "DeadlockProjection": """symbol_uip runner_pure runner_bind runner_app runner_locally_owner
        runner_locally_other runner_comm_self runner_comm_sender runner_comm_receiver runner_comm_other
        runner_cond_owner runner_cond_peer runner_par runner_root""",
    "DeadlockEnabled": """terminal_view_unique local_return_unique local_return_no_event
        returns_result return_result_unique return_unique return_no_possible return_no_action
        possible_step endpoint_witness network_enabled_exact""",
    "DeadlockEnabledCases": "role_enabled_exact network_exact unique_value returned_is_silent",
    "DeadlockStepView": "view_of_step step_of_view",
    "DeadlockMatch": """initial_matches unequal_lengths_do_not_match delivery_empty_impossible
        delivery_fifo prefix_state prefix_action_order prefix_source_run prefix_network_run terminal_queues""",
    "DeadlockMatchExpect": """actual_interface literal_initial inserted_target_event_rejected
        concrete_delivery no_fabricated_delivery opposite_kind_cannot_jump app_branch_cannot_alias""",
    "DeadlockMessages": """represents_empty represents_frame represents_snoc represents_send
        announcement_pending represents_announcement announcement_owner_queue announcement_other_keys
        send_other_key represents_consume consume_other_key same_channel_key frontier_from_history
        take_pending_split source_take_exact_head source_take_different_keys network_receive_at_occurrence""",
    "DeadlockMessagesExpect": """literal_empty literal_app_session repeated_root_keys repeated_root_queue
        repeated_root_invariant swapped_wire_entries_rejected swapped_occurrences_rejected_even_equal_wire
        data_choice_share_queue data_choice_invariant same_kind_source_fifo_cannot_skip
        source_can_skip_same_key_opposite_kind same_key_skip_has_no_wire_frontier different_app_key_skip
        literal_announcement_owner_excluded literal_atomic_announcement literal_exact_first_consume
        literal_matching_decode other_key_framed actual_sender_codec""",
    "DeadlockRuns": """run_nil run_snoc_iff run_singleton run_append run_append_iff run_cons_iff
        stuck_iff_not_ready DF_ready DF_after_run DF_no_stuck ready_stuck_reflection""",
    "DeadlockRunsCases": "ready_exact stuck_exact DF_exact run_empty_exact run_extension_exact run_composition_exact",
    "DeadlockStateCases": "shared_model_exact",
    "DeadlockSource": """off_at_decide silent_waiting empty_queue_barrier take_pending_at take_at_split
        role_step_actor silent_waiting_at waiting_action_at""",
    "DeadlockSourceCases": """fifo independent_action parallel_action sends receive_blocks forward_blocks
        self_other one_role_announcement multi_role_announcement separate_hear occurrence_exact
        old_take_inclusion delayed_run discrepancy_run delayed_second_negative delayed_first_positive
        discrepancy_receive discrepancy_old_rejects discrepancy_not_wf delayed_wf""",
    "DeadlockOrder": """session_at_child same_session_iff source_before_irreflexive same_session_order
        same_session_sequence fifo_relative_order fifo_frontier_head""",
    "DeadlockOrderExpect": "reused_nested_app cond_bind_overlap choice_ancestor opposite_app_sessions",
    "DeadlockWellFormed": "structural_head structural_head_roles structural_wire",
    "DeadlockWellFormedCases": """participants_distinct local_prefix_results opposed_bind_heads
        empty_bind_rejected bool_wire communicating_accepted located_accepted two_receivers_rejected
        absent_receiver_rejected wrong_codec_rejected self_accepted empty_complete_impossible
        empty_partial_related empty_partial_continuations_disagree empty_bind_partial_obligation_rejected
        other_constructors_accepted""",
    "DeadlockNetwork": """replace_same replace_other enqueue_same orphan_not_final
        returns_shape step_possible nstep_possible""",
    "DeadlockNetworkCases": """send_first receive_exact left_send right_send two_receive fifo
        pure_join pure_no_action shared_right shared_left both_sends wrong_session wrong_sender
        wrong_receiver bad_head announcement singleton_announcement orphan_stuck two_roles_ready
        spin_silent local_return_silent one_event_only bookkeeping after_bookkeeping wait_blocked
        empty_endpoints all_finished""",
    "DeadlockQuorum": "bool_wire",
}
CLIENT = ("Main.quorumVoting", "DeadlockQuorum.quorum_well_formed",
          "DeadlockQuorumCases.quorum_has_frozen_type",
          "DeadlockQuorumFreedomExpect.quorum_deadlock_freedom_expected")
NESTED = {
    ("DeadlockRepairMatchCases", "RepairMatch"): """complete_repaired_match actual_machine_four_actions
        source_final positive_between_sends_and_receives positive_after_choice_receive
        wrong_tag_prefix_rejected invented_choice_prefix_rejected swapped_fifo_prefix_rejected
        swapped_head_cannot_explain_choice wrong_tag_does_not_enable_generated_receive invented_branch_is_not_a_receive""",
    ("DeadlockRepairCases", "Repair"): "repaired_exact_family repaired_exact_run decode_truth decode_unit",
    ("DeadlockMutationCases", "Mutation"): """frozen_wf frozen_source_df frozen_correct frozen_wrong
        frozen_omitted frozen_no_explanation frozen_wrong_progress frozen_omitted_progress""",
    # Closure of proposition definitions, not inhabitants of these types.
    ("DeadlockLibraryExpect", "DeadlockContract"): """epp_preserves_deadlock_freedom network_run_has_source
        matched_ready deadlock_reflection""",
}


def digest(path: Path, expected: str) -> None:
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit(f"changed frozen input: {path}")


def run(directory: Path, *command: str, log: str, reject: bool = False) -> str:
    result = subprocess.run(command, cwd=directory, check=False, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=120)
    (directory / log).write_text(result.stdout)
    if (result.returncode != 0) != reject:
        raise SystemExit(f"{directory / log}: unexpected status {result.returncode}\n{result.stdout}")
    return result.stdout


def compile_v(directory: Path, loads: list[str], source: Path, *, reject: bool = False) -> str:
    return run(directory, sys.executable, str(PARKOUR / "parkour_rocq.py"),
               *loads, "-Q", str(directory), "", source.name, log=source.stem + ".log", reject=reject)


def mutants(output: Path, loads: list[str]) -> None:
    for side, premise in (("left", "    step p (A -> B) f q s a f' q' s' ->\n"),
                          ("right", "    step p A x q s a x' q' s' ->\n")):
        directory = output / ("no-" + side)
        directory.mkdir()
        for module in NETWORK:
            source = directory / (Path(module).name + ".v")
            text = (PARKOUR / (module + ".v")).read_text()
            if module == NETWORK[0]:
                if text.count(premise) != 1:
                    raise SystemExit("mutation target changed")
                text = text.replace(premise, "    False ->\n" + premise)
            source.write_text(text)
            last = module == NETWORK[-1]
            diagnostics = compile_v(directory, loads, source, reject=last)
            if last:
                lines = text.splitlines()
                start = next(i for i, line in enumerate(lines, 1) if line.startswith(f"Lemma {side}_send :"))
                end = next(i for i, line in enumerate(lines, 1) if i >= start and "Qed." in line)
                location = re.search(r'File "(?:\./)?DeadlockNetworkCases\.v", line (\d+),', diagnostics)
                if not (location and start <= int(location[1]) <= end
                        and "Unable to unify" in diagnostics and 'with "False"' in diagnostics):
                    raise SystemExit("wrong mutation rejection:\n" + diagnostics)
        print(f"PASS: {side}_send rejected disabled {side} rule", flush=True)


def dependencies(output: Path, loads: list[str]) -> None:
    # No imports: Rocq prints minimally qualified names, e.g. Choreo2.epp.
    requires = "Require DeadlockSource DeadlockWellFormed DeadlockNetwork DeadlockRuns Choreography.Choreo2.\n"
    forbidden = {
        "Choreography.Choreo2.epp": r"\bChoreo2\.epp\b",
        "DeadlockNetwork.nstep": r"\bDeadlockNetwork\.\w+",
        "DeadlockRuns.ready": r"\bDeadlockRuns\.(?:ready|stuck|DF)\b",
    }
    # The report describes constants, not a list of all inductive names:
    # nstep exposes its supporting DeadlockNetwork constants transitively.
    for target, pattern in forbidden.items():
        source = output / ("Control_" + target.replace(".", "_") + ".v")
        source.write_text(requires + f"Definition dependency_control := @{target}.\n"
                          "Print All Dependencies dependency_control.\n")
        if not re.search(pattern, compile_v(output, loads, source)):
            raise SystemExit(f"{source.stem}: forbidden dependency was not detected")
    source = output / "Control_DeadlockSource_take_pending.v"
    source.write_text(requires + "Print All Dependencies DeadlockSource.take_pending.\n")
    fifo_support = r"\bDeadlockSource\.(?:source_lane|same_channel|take_pending)\b"
    if "DeadlockSource.source_lane :" not in compile_v(output, loads, source).splitlines():
        raise SystemExit("historical FIFO relation did not expose its lane dependency")
    for export, witness in (("DeadlockSource.cstep", "DeadlockLocal.reply_local"),
                            ("DeadlockSource.cfinal", "DeadlockSource.positions"),
                            ("DeadlockSource.waiting_code", "Choreo2.Choreo"),
                            ("DeadlockWellFormed.well_formed", "DeadlockWellFormed.wire_law")):
        source = output / ("Deps_" + export.replace(".", "_") + ".v")
        source.write_text(requires + f"Print All Dependencies {export}.\n")
        report = compile_v(output, loads, source)
        if (witness not in report or any(re.search(p, report) for p in forbidden.values())
                or (export == "DeadlockSource.cstep" and re.search(fifo_support, report))
                or (export.startswith("DeadlockWellFormed.") and "DeadlockSource." in report)):
            raise SystemExit(f"{source.stem}: missing witness or forbidden operational dependency")
    # Matching uses both machines and the generated projection, but cannot
    # obtain progress by consulting readiness or the public theorem.
    source = output / "Deps_DeadlockMatch_matches.v"
    source.write_text("Require DeadlockMatch DeadlockRuns.\nPrint All Dependencies DeadlockMatch.matches.\n")
    report = compile_v(output, loads, source)
    witnesses = ("DeadlockMatch.state_match", "DeadlockMatch.residuals", "DeadlockMessages.represents",
                 "DeadlockMatch.source_initial", "DeadlockMatch.network_initial", "Choreo2.epp")
    headers = set(report.splitlines())
    if (any(f"{name} :" not in headers for name in witnesses)
            or re.search(forbidden["DeadlockRuns.ready"], report)
            or re.search(r"\bDeadlockNetwork\.(?:endpoints_possible|endpoint_possible|possible)\b"
                         r"|\bDeadlockFreedom\.", report)):
        raise SystemExit("matches: missing state/history dependency or forbidden readiness/theorem dependency")


def check(output: Path, loads: list[str], generated: Path, *, final: bool = False) -> None:
    output.mkdir(parents=True, exist_ok=False)
    for name, anchor in MANIFESTS.items():
        manifest = PARKOUR / "tests" / name
        digest(manifest, anchor)
        for line in manifest.read_text().splitlines():
            expected, filename = line.split("  ", 1)
            if (name == "DeadlockLibraryExpect.sha256" and
                    filename == "examples/parkour/theories/DeadlockSource.v"):
                old = subprocess.check_output(["git", "cat-file", "blob",
                                               "d97eeb4607c670944977fe0417addbc2fb3464c3"], cwd=PARKOUR)
                if hashlib.sha256(old).hexdigest() != expected:
                    raise SystemExit("historical source does not match the frozen library manifest")
                continue
            elif filename.startswith("examples/parkour/lib/"):
                path = generated / filename.removeprefix("examples/parkour/lib/")
            elif name in {"DeadlockProjectionExpect.sha256", "DeadlockMutationExpect.sha256"}:
                path = PARKOUR / filename
            else:
                path = PARKOUR.parents[1] / filename
            digest(path, expected)
    # Direct fixture anchors: State and Enabled were committed separately
    # from their witnesses; Messages and Match use their independently
    # compiled literal fixtures. The latter are not pre-proof freezes.
    for fixture, anchor in {
        "DeadlockStateExpect": "405818a74c3f68f1c3e2e0e015482a5d41f1edd0e81db2f2fc1b8b54f52d98dc",
        "DeadlockEnabledExpect": "39702217b967299a2c40eed0252acc6f0019b28b7a2acebcf1e352ddf06e378f",
        "DeadlockMessagesExpect": "fbc4c4f8c71f830d29c1924344f0d3cc19ca4adb6b4f4dfdc534329db7b2266a",
        "DeadlockMatchExpect": "7ae72daa2a26b15539226f7c86c4432961f40d0a4e33329a791bc8f88b53ec37",
        "DeadlockMatchStepExpect": "b845b79ebb8939b5c622cb5a750a401f94eb2321235eba8ed08d5ca00c21c0e2",
    }.items():
        digest(PARKOUR / "tests" / (fixture + ".v"), anchor)
    for module in MODULES:
        target = output / (Path(module).name + ".v")
        shutil.copyfile(PARKOUR / (module + ".v"), target)
        if module == "theories/DeadlockSource":
            digest(target, REVIEWED_SOURCE)
        report = compile_v(output, loads, target)
        if module == "tests/DeadlockQuorumCases" and "Constant Main.quorumVoting" not in report.splitlines():
            raise SystemExit("generated quorum origin not confirmed")
    dependencies(output, loads)
    for (library, inner), names in NESTED.items():
        for name in names.split():
            export = f"{library}.{inner}.{name}"
            run(output, sys.executable, str(PARKOUR / "check-assumptions.py"), "closed",
                str(output), export, "--library", library, *loads, log="assumptions-" + export + ".log")
    for policy, exports in (("closed", [f"{module}.{name}" for module, entries in CLOSED.items()
                                        for name in entries.split()]),
                            ("client", list(CLIENT))):
        for export in exports:
            run(output, sys.executable, str(PARKOUR / "check-assumptions.py"), policy,
                str(output), export, *loads, log="assumptions-" + export + ".log")
    mutants(output, loads)
    print("PASS: semantic contracts, dependency queries, mutants and quorum well-formedness")
    if final:
        check_final(output.parent / "final", [*loads, "-Q", str(output), ""])


def check_final(output: Path, loads: list[str]) -> None:
    output.mkdir(exist_ok=False)
    target = output / "DeadlockContract.v"
    shutil.copyfile(PARKOUR / "theories" / target.name, target)
    digest(target, "25f2563b945a3a02b4831902396ef3751206a34e2b988e21aa39a61991e24d06")
    compile_v(output, loads, target)
    for policy, library, names in (
        ("closed", "DeadlockFreedom", ("epp_preserves_deadlock_freedom", "network_run_has_source",
                                       "matched_ready", "deadlock_reflection")),
        ("client", "DeadlockQuorum", ("quorum_deadlock_freedom",)),
    ):
        for name in names:
            export = f"{library}.{name}"
            run(output, sys.executable, str(PARKOUR / "check-assumptions.py"), policy,
                str(output), export, *loads, log="assumptions-" + export + ".log")
    print("PASS: public theorem witnesses and assumption reports")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="fresh evidence directory")
    parser.add_argument("--generated", type=Path, required=True, help="freshly translated Parkour library")
    parser.add_argument("--final", action="store_true", help="require all public proofs and their exact types")
    parser.add_argument("libraries", type=Path, nargs="+", help="compiled load roots, including pinned DeadlockLocal")
    args = parser.parse_args()
    generated = args.generated.resolve()
    check(args.output.resolve(), [arg for path in [*args.libraries, generated]
                                  for arg in ("-Q", str(path.resolve()), "")], generated, final=args.final)
