"""Validate the semantic slices of a freshly compiled canonical Parkour project."""

import argparse
import re
import shutil
from pathlib import Path

from audit_project import assumptions, compile_v, project_loads
from frozen_inputs import verify_frozen_inputs

CLOSED = {
    "ParkourTheories.Projection.FIFO.ChannelLedger": "decorated_ledger prefix_ledger reachable_head_from_coverage",
    "ParkourTheories.Choreography.Histories.CursorHistories": "initial_actor_history history_bind_receive run_completed_partial_histories",
    "ParkourTheories.Choreography.Histories.TransitionArchive": "code_history_has_syntax_cut syntax_cut_role_step",
    "ParkourTheories.Choreography.Results.OperandObservations": "received_original_value owner_locally_actual_result",
    "ParkourTheories.Choreography.Results.CutFamilySoundness": "structural_cut_family_results",
    "ParkourTheories.Projection.Matching.PayloadHistory": "matched_has_actual_past production_recorded_in_replay",
    "ParkourTheories.Projection.Payloads.SenderProvenance": "production_at_current_sender queued_operand_at_receiver",
    "ParkourTheories.Projection.Payloads.RootPackets": "packet_from_root_program root_queued_operand source_originals_root",
    "ParkourTheories.Projection.FIFO.ConsumedOccurrences": "matched_received_safe matched_future_unreceived",
    "ParkourTheories.Projection.Payloads.StaticPackets": "syntactic_packet source_originals_static",
    "ParkourTheories.Projection.Occurrences.PossiblePaths": "sampled_send_site static_receive_compares_to_queued",
    "ParkourTheories.Projection.FIFO.FirstEmission": "static_no_predecessor head_key_path first_send_prefix head_from_first_send",
    "ParkourTheories.Projection.FIFO.Heads.RootOccurrence": "source_head_paths_root",
    "ParkourTheories.Projection.Occurrences.SenderBarrier": "static_sender_barrier",
    "ParkourTheories.Projection.FIFO.Heads.StaticPath": "first_send_at_or_after source_head_paths_static",
    "ParkourTheories.Choreography.Histories.PureBindDescent": "pure_cut_returned pure_bind_actual_descent",
    "ParkourTheories.Projection.Payloads.ChoiceSelection": "root_choice_delivery_selected observed_root_choice_selected root_choice_actor_invariant",
    "ParkourTheories.Projection.Occurrences.EnteredCode": "entered_history_origin entered_focus_original before_choice_no_child",
    "ParkourTheories.Projection.Payloads.SelectedBranch": "choice_body_originals source_originals_choice_static",
    "ParkourTheories.Projection.Matching.ObservationArchive": """matched_has_observed_cuts observed_subarchive_receive observed_subarchive_same_trace
        past_receive_sender_entry past_receive_sender_present observed_region_roles_nodup""",
    "ParkourTheories.Projection.Occurrences.SubtreeGuards": "subtree_predecessor_history subtree_predecessor_cstep subtree_predecessor_poised",
    "ParkourTheories.Projection.FIFO.Heads.ChoiceBranch": "root_choice_balance source_head_paths_choice_static",
    "ParkourTheories.Projection.Payloads.PureBind": "source_originals_pure_bind_static",
    "ParkourTheories.Projection.RoleLogs.ArchiveOrder": "archive_role_log",
    "ParkourTheories.Choreography.Histories.LogDecomposition": "local_log_app_cases local_log_bind_cases log_shuffle_member",
    "ParkourTheories.Projection.RoleLogs.ChoiceExecution": "actor_log_cond_replay",
    "ParkourTheories.Projection.RoleLogs.Families.RegionOwnership": "root_log_family owns_sender_present expose_logged_receivers",
    "ParkourTheories.Projection.RoleLogs.OccurrenceScope": "actor_log_scope actor_log_produced_here",
    "ParkourTheories.Projection.Payloads.OwnedPackets": "owned_original_operand owned_outgoing_packet owned_node_codec",
    "ParkourTheories.Projection.RoleLogs.PrimitiveObservations": "comm_log_observed pure_log_returned",
    "ParkourTheories.Projection.FIFO.SendChronology": "matched_sent_nodup matched_sent_sorted matched_head_identity",
    "ParkourTheories.Projection.RoleLogs.Families.ChoicePartition": "replay_cond_logged_strong replay_cond_logged",
    "ParkourTheories.Projection.RoleLogs.Families.BranchPartition": "logged_replay_app logged_replay_bind",
    "ParkourTheories.Projection.Matching.ReturnedValues": "actual_replay_laws matched_partial_results",
    "ParkourTheories.Projection.FIFO.PayloadAccounting": "sent_has_production receive_has_consumption",
    "ParkourTheories.Tests.FIFO.InvalidQueueOrder": "reject_lost_pending reject_swapped_fifo",
    "ParkourTheories.Tests.FIFO.PartialDelivery": "partial_delivery",
    "ParkourTheories.Tests.FIFO.ParallelExchanges": "app_self_completed app_reject_root_tag",
    "ParkourTheories.Tests.FIFO.InvalidSourceTraces": "reject_invented_bytes reject_wrong_occurrence invented_value_transport_obstruction",
    "ParkourTheories.Projection.CommunicationTree.ObservationCoverage": "realized_receive_site realized_past_sites realized_returned_trace",
    "ParkourTheories.Projection.CommunicationTree.PredecessorCoverage": "tracked_parallel tracked_sequence tracked_choice tracked_predecessor_trace",
    "ParkourTheories.Projection.FIFO.Heads.PredecessorCriterion": "layout_head",
    "ParkourTheories.Projection.FIFO.Heads.LoggedPrefix": "source_head_paths_matched_from_tracked",
    "ParkourTheories.Projection.Payloads.ReceiverCodec": "structural_logged_readers matched_receiver_packet_codec matched_source_originals_from_head",
    "ParkourTheories.Projection.CommunicationTree.AtomicNodes": "tracked_atomic_node",
    "ParkourTheories.Projection.CommunicationTree.ForkAndBind": "app_layout_children bind_layout_children",
    "ParkourTheories.Projection.CommunicationTree.ChoiceNodes": "coherent_choice_layout",
    "ParkourTheories.Projection.CommunicationTree.Construction": "structural_tracked_layout structural_root_layout",
    "ParkourTheories.Projection.Matching.MatchedReceiveSafety": "matched_receive_frontiers matched_prefix_frontiers",
    "ParkourTheories.Choreography.Histories.SyntaxDecomposition": "replay_app_actual replay_bind_actual replay_cond_actual archived_cut_actual_syntax",
    "ParkourTheories.Projection.CommunicationTree.CompletedSubtrees": "shared_node_paths returned_cut_completed completed_subtree_coverage",
    "ParkourTheories.Choreography.ReceiveSites": "replay_receive_site",
    "ParkourTheories.Projection.Matching.ReceiveConditions": "aligned_cut_receive_safety aligned_cut_delivery_available covered_residuals",
    "ParkourTheories.Projection.FIFO.HeadDecoding": """nonempty_channel_first removal_has_key queued_key_nonempty head_bytes exact_receive_at
        source_removal_exposes_wire""",
    "ParkourTheories.Choreography.Histories.RoleChronology": "role_history_chronology code_history_chronology history_scoped",
    "ParkourTheories.Choreography.Observations": """silent_result silent_live source_returns_result result_source_returns cursor_result_exact
        source_step_live live_source_step cursor_live_exact silent_returns_iff silent_actions_iff""",
    "ParkourTheories.Projection.Matching.CursorAlignment": "initial_alignment aligned_returns network_action_reflects",
    "ParkourTheories.Projection.Matching.RoleReadiness": """aligned_result source_return_is_network_return empty_delivery_available
        aligned_live source_action_is_network_enabled source_action_exposes_network_action aligned_role_ready
        generated_source_action_exposes_network_action""",
    "ParkourTheories.Tests.Projection.ProjectedRoleReadiness": """left_first_alignment right_first_source_return opposite_bookkeeping_return
        generated_parallel_exposes_real_action generated_off_role_prefix_exposes_real_action
        resumed_local_exposes_real_action typed_receive_is_source_enabled empty_wire_receive_is_not_network_enabled
        occurrence_receive_skips_same_lane strong_fifo_still_rejects_second_delivery
        occurrence_availability_rejects_bad_wire_head occurrence_availability_accepts_other_decodable_payload""",
    "ParkourTheories.Network.Scheduling": "roster_step schedule_role all_returns",
    "ParkourTheories.Choreography.Results.FiniteSelection": "add_value_valid select_returned roster_member_unique",
    "ParkourTheories.Projection.Matching.ActionReflection": """receive_delivery delivery_represents aligned_decorated_step endpoint_decorated_step
        state_step matched_prefix_step initial_safe_residuals initial_prefix_step""",
    "ParkourTheories.Tests.Projection.PrefixExtensionContracts": "generated_sender_action nonempty_actual_prefix safety_does_not_require_readiness",
    "ParkourTheories.Projection.RunCorrespondence": "empty_network_run_has_source network_run_snoc_view schedule_from_safe_receives",
    "ParkourTheories.Projection.Progress": """matched_network_final matched_source_final
        initial_inputs_available matched_ready_from_inputs
        preservation_from_frontiers reflection_from_frontiers""",
    "Choreography.Choreo2": "epp",
    "ParkourTheories.Semantics.Roles": "symbol_uip",
    "ParkourTheories.Projection.ConstructorEquations": """runner_pure runner_bind runner_app runner_locally_owner
        runner_locally_other runner_comm_self runner_comm_sender runner_comm_receiver runner_comm_other
        runner_cond_owner runner_cond_peer runner_par runner_root""",
    "ParkourTheories.Semantics.LocalEffects": "terminal_view_unique local_return_unique local_return_no_event",
    "ParkourTheories.Network.Enabledness": """returns_result return_result_unique return_unique return_no_possible return_no_action
        possible_step endpoint_witness network_enabled_exact""",
    "ParkourTheories.Tests.Network.EnablednessWitnesses": "role_enabled_exact network_exact unique_value returned_is_silent",
    "ParkourTheories.Network.StepInversion": "view_of_step step_of_view",
    "ParkourTheories.Projection.Matching.PrefixRelation": """initial_matches unequal_lengths_do_not_match delivery_empty_impossible
        delivery_fifo prefix_state prefix_action_order prefix_source_run prefix_network_run terminal_queues""",
    "ParkourTheories.Tests.Projection.PrefixRelationContracts": """actual_interface literal_initial inserted_target_event_rejected
        concrete_delivery no_fabricated_delivery opposite_kind_cannot_jump app_branch_cannot_alias""",
    "ParkourTheories.Projection.FIFO.MessageRepresentation": """represents_empty represents_frame represents_snoc represents_send
        announcement_pending represents_announcement announcement_owner_queue announcement_other_keys
        send_other_key represents_consume consume_other_key same_channel_key frontier_from_history
        take_pending_split source_take_exact_head source_take_different_keys network_receive_at_occurrence""",
    "ParkourTheories.Tests.FIFO.QueueRepresentation": """literal_empty literal_app_session repeated_root_keys repeated_root_queue
        repeated_root_invariant swapped_wire_entries_rejected swapped_occurrences_rejected_even_equal_wire
        data_choice_share_queue data_choice_invariant same_kind_source_fifo_cannot_skip
        source_can_skip_same_key_opposite_kind same_key_skip_has_no_wire_frontier different_app_key_skip
        literal_announcement_owner_excluded literal_atomic_announcement literal_exact_first_consume
        literal_matching_decode other_key_framed actual_sender_codec""",
    "ParkourTheories.Semantics.Runs": """run_nil run_snoc_iff run_singleton run_append run_append_iff run_cons_iff
        stuck_iff_not_ready deadlock_free_implies_ready deadlock_free_after_run deadlock_free_excludes_stuck ready_stuck_reflection""",
    "ParkourTheories.Tests.Semantics.FiniteRunWitnesses": "ready_exact stuck_exact DF_exact run_empty_exact run_extension_exact run_composition_exact",
    "ParkourTheories.Tests.Semantics.StoreUpdateWitnesses": "shared_model_exact",
    "ParkourTheories.Choreography.PendingDeliveries": "take_pending_at take_at_split",
    "ParkourTheories.Choreography.RoleSteps": """off_at_decide silent_waiting empty_queue_barrier
        role_step_actor silent_waiting_at waiting_action_at""",
    "ParkourTheories.Tests.Choreography.AsynchronousSteps": """fifo independent_action parallel_action sends receive_blocks forward_blocks
        self_other one_role_announcement multi_role_announcement separate_hear occurrence_exact
        old_take_inclusion delayed_run discrepancy_run delayed_second_negative delayed_first_positive
        discrepancy_receive discrepancy_old_rejects discrepancy_not_wf delayed_wf""",
    "ParkourTheories.Choreography.Precedence": "source_before_irreflexive",
    "ParkourTheories.Projection.SessionPaths": """session_at_child same_session_iff same_session_order
        same_session_sequence fifo_relative_order fifo_frontier_head scoped_fork_disjoint code_history_fork_disjoint""",
    "ParkourTheories.Tests.FIFO.SessionPrecedence": "reused_nested_app cond_bind_overlap choice_ancestor opposite_app_sessions",
    "ParkourTheories.Choreography.WellFormedness": "structural_head structural_head_roles structural_wire",
    "ParkourTheories.Tests.Choreography.StructuralWitnesses": """participants_distinct local_prefix_results opposed_bind_heads
        empty_bind_rejected bool_wire communicating_accepted located_accepted two_receivers_rejected
        absent_receiver_rejected wrong_codec_rejected self_accepted empty_complete_impossible
        empty_partial_related empty_partial_continuations_disagree empty_bind_partial_obligation_rejected
        other_constructors_accepted""",
    "ParkourTheories.Network.Mailboxes": "replace_same replace_other enqueue_same",
    "ParkourTheories.Network.Endpoints": "returns_shape step_possible",
    "ParkourTheories.Network.Execution": "orphan_not_final nstep_possible",
    "ParkourTheories.Tests.Network.SchedulingAndDelivery": """send_first receive_exact left_send right_send two_receive fifo
        pure_join pure_no_action shared_right shared_left both_sends wrong_session wrong_sender
        wrong_receiver bad_head announcement singleton_announcement orphan_stuck two_roles_ready
        spin_silent local_return_silent one_event_only bookkeeping after_bookkeeping wait_blocked
        empty_endpoints all_finished""",
    "ParkourTheories.Protocols.QuorumVoting": "bool_wire",
}
CLIENT = ("Main.quorumVoting", "ParkourTheories.Protocols.QuorumVoting.quorum_well_formed",
          "ParkourTheories.Tests.Protocols.QuorumWitnesses.quorum_has_frozen_type",
          "ParkourTheories.Tests.Protocols.QuorumProgress.quorum_deadlock_freedom_expected")
NESTED = {
    ("ParkourTheories.Tests.Projection.ParallelAndChoiceMatches", "ExtraMatch"): """Parallel.left_branch_actual_match
        Parallel.right_branch_actual_match Parallel.cross_branch_match_rejected Parallel.wrong_branch_packet
        SelfComm.actual_empty_match SelfComm.generated_exact_return SelfComm.generated_final
        SelfComm.fabricated_self_send_rejected Choice.multi_peer_pending_match
        Choice.invented_peer_value_rejected Choice.singleton_actual_match""",
    ("ParkourTheories.Tests.Projection.ChoicePayloadMatching", "RepairMatch"): """complete_repaired_match actual_machine_four_actions
        source_final positive_between_sends_and_receives positive_after_choice_receive
        wrong_tag_prefix_rejected invented_choice_prefix_rejected swapped_fifo_prefix_rejected
        swapped_head_cannot_explain_choice wrong_tag_does_not_enable_generated_receive invented_branch_is_not_a_receive""",
    ("ParkourTheories.Tests.Projection.AnnouncementBeforePayload", "Repair"): "repaired_exact_family repaired_exact_run decode_truth decode_unit",
    ("ParkourTheories.Tests.Projection.WrongSessionAndMissingSend", "Mutation"): """frozen_wf frozen_source_df frozen_correct frozen_wrong
        frozen_omitted frozen_no_explanation frozen_wrong_progress frozen_omitted_progress""",
    # Closure of proposition definitions, not inhabitants of these types.
    ("ParkourTheories.Tests.Projection.RunCorrespondenceTypes", "RunAndProgressTypes"): """epp_preserves_deadlock_freedom network_run_has_source
        matched_ready deadlock_reflection""",
}


def mutants(output: Path, external: list[str], root: Path) -> None:
    # Give each mutant its own canonical roots. Only unchanged prerequisites
    # come from the successful build; neither positive step relation is visible.
    inputs = ("theories/Network/Endpoints.v", "theories/Network/Execution.v", "tests/Network/CommunicationRules.v",
              "tests/Network/SharedStoreScheduling.v", "tests/Network/SilentEndpoints.v",
              "tests/Network/SchedulingAndDelivery.v")
    for side, premise in (("left", "    step p (A -> B) f q s a f' q' s' ->\n"),
                          ("right", "    step p A x q s a x' q' s' ->\n")):
        directory = output / ("no-" + side)
        for obj in ("theories/Semantics/LocalEffects.vo", "theories/Network/Mailboxes.vo"):
            (directory / obj).parent.mkdir(parents=True)
            shutil.copyfile(root / obj, directory / obj)
        for relative in inputs:
            source = directory / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_bytes((root / relative).read_bytes())
        loads = [*external, *project_loads(directory)]
        for relative in inputs:
            source = directory / relative
            text = source.read_text()
            if relative == inputs[0]:
                if text.count(premise) != 1:
                    raise SystemExit("mutation target changed")
                source.write_text(text.replace(premise, "    False ->\n" + premise))
            last = relative == inputs[-1]
            report = compile_v(directory, loads, source, reject=last)
            if last:
                lines = text.splitlines()
                start = next(i for i, line in enumerate(lines, 1) if line.startswith(f"Lemma {side}_send :"))
                end = next(i for i, line in enumerate(lines, 1) if i >= start and "Qed." in line)
                location = re.search(r'File "(?:[^"]*/)?SchedulingAndDelivery\.v", line (\d+),', report)
                if not (location and start <= int(location[1]) <= end
                        and "Unable to unify" in report and 'with "False"' in report):
                    raise SystemExit("wrong mutation rejection:\n" + report)
        print(f"PASS: {side}_send rejected disabled {side} rule", flush=True)


def dependencies(output: Path, loads: list[str]) -> None:
    source = "ParkourTheories.Choreography.Execution"
    network = "ParkourTheories.Network.Execution"
    wf = "ParkourTheories.Choreography.WellFormedness"
    pending = "ParkourTheories.Choreography.PendingDeliveries"
    occurrences = "ParkourTheories.Choreography.Occurrences"
    role_steps = "ParkourTheories.Choreography.RoleSteps"
    endpoints = "ParkourTheories.Network.Endpoints"
    mailboxes = "ParkourTheories.Network.Mailboxes"
    runs = "ParkourTheories.Semantics.Runs"
    local = "ParkourTheories.Semantics.LocalEffects"
    match = "ParkourTheories.Projection.Matching.PrefixRelation"
    messages = "ParkourTheories.Projection.FIFO.MessageRepresentation"
    progress = "ParkourTheories.Projection.Progress"
    correspondence = "ParkourTheories.Projection.RunCorrespondence"
    epp = "Choreography.Choreo2.epp"
    requires = f"Require {source} {wf} {pending} {role_steps} {network} {runs} Choreography.Choreo2.\n"
    word = r"[A-Za-z_][A-Za-z_0-9']*"
    dotted = rf"\b{word}(?:\.{word})+\b"
    leaves = {name.rsplit(".", 1)[-1] for name in
              (source, role_steps, pending, occurrences, network, endpoints, mailboxes, wf, runs, local,
               match, messages, progress, correspondence, "Choreography.Choreo2")}

    def report_for(prefix: str, name: str, *, control: bool = False) -> str:
        path = output / (("Control_" if control else "Deps_") + name.replace(".", "_") + ".v")
        command = (f"Definition dependency_control := @{name}.\nPrint All Dependencies dependency_control."
                   if control else f"Print All Dependencies {name}.")
        path.write_text(prefix + command + "\n")
        report = compile_v(output, loads, path)
        # Dependency output uses shortest names, and two libraries are named
        # Execution. Resolve references in exactly the query's environment.
        names = sorted({ref for ref in re.findall(dotted, report) if ref.split(".")[-2] in leaves})
        if not names:
            raise SystemExit(f"{path.stem}: empty dependency report")
        about = output / ("Resolve_" + path.name)
        about.write_text(prefix + "".join(f"About {ref}.\n" for ref in names))
        expanded = re.findall(rf"^Expands to:\s+(?:Constant|Inductive|Constructor)\s+({dotted})$",
                              compile_v(output, loads, about), re.MULTILINE)
        if len(expanded) != len(names):
            raise SystemExit(f"{about.stem}: could not resolve every dependency name")
        resolved = dict(zip(names, expanded, strict=True))
        return re.sub(dotted, lambda m: resolved.get(m[0], m[0]), report)

    forbidden = {
        epp: re.escape(epp) + r"\b",
        network + ".step": "(?:" + "|".join(map(re.escape, (network, endpoints, mailboxes))) + r")\.\w+",
        runs + ".ready": re.escape(runs) + r"\.(?:ready|stuck|deadlock_free)\b",
    }
    for target, pattern in forbidden.items():
        if not re.search(pattern, report_for(requires, target, control=True)):
            raise SystemExit(f"{target}: forbidden dependency was not detected")
    fifo = pending + ".take_first_on_source_channel"
    if occurrences + ".source_lane :" not in report_for(requires, fifo).splitlines():
        raise SystemExit("historical FIFO relation did not expose its lane dependency")
    fifo_pattern = "|".join(re.escape(name) + r"\b" for name in
                           (occurrences + ".source_lane", pending + ".same_channel", fifo))
    for export, witness in ((source + ".step", local + ".reply_local"),
                            (source + ".final", source + ".positions"),
                            (role_steps + ".waiting_code", "Choreography.Choreo2.Choreo"),
                            (wf + ".well_formed", wf + ".wire_law")):
        report = report_for(requires, export)
        if (witness not in report or any(re.search(p, report) for p in forbidden.values())
                or (export == source + ".step" and re.search(fifo_pattern, report))
                or (export.startswith(wf + ".") and any(mod + "." in report
                    for mod in (source, role_steps, pending, occurrences)))):
            raise SystemExit(f"{export}: missing witness or forbidden operational dependency")
    report = report_for(f"Require {match} {runs}.\n", match + ".matches")
    witnesses = (match + ".state_match", match + ".residuals", messages + ".represents",
                 match + ".source_initial", match + ".network_initial", epp)
    headers = set(report.splitlines())
    if (any(f"{name} :" not in headers for name in witnesses)
            or re.search(forbidden[runs + ".ready"], report)
            or re.search(re.escape(endpoints) + r"\.(?:endpoints_possible|endpoint_possible|possible)\b", report)
            or progress + "." in report or correspondence + "." in report):
        raise SystemExit("matches: missing state/history dependency or forbidden readiness/theorem dependency")


def check(output: Path, external: list[str], root: Path, generated: Path, *, final: bool) -> None:
    output.mkdir(parents=True, exist_ok=False)
    verify_frozen_inputs(root, generated)
    loads = [*external, *project_loads(root)]
    quorum = output / "QuorumOrigin.v"
    quorum.write_text("Require ParkourTheories.Tests.Protocols.QuorumWitnesses.\nLocate Main.quorumVoting.\n")
    if "Constant Main.quorumVoting" not in compile_v(output, loads, quorum).splitlines():
        raise SystemExit("generated quorum origin not confirmed")
    dependencies(output, loads)
    for (library, inner), names in NESTED.items():
        for name in names.split():
            assumptions(output, loads, "closed", f"{library}.{inner}.{name}", library=library)
    for module, entries in CLOSED.items():
        for name in entries.split():
            assumptions(output, loads, "closed", f"{module}.{name}")
    for export in CLIENT:
        assumptions(output, loads, "client", export)
    mutants(output, external, root)
    print("PASS: semantic contracts, dependency queries, mutants and quorum well-formedness")
    if final:
        evidence = output.parent / "final"
        evidence.mkdir()
        contract = evidence / "PublicContract.v"
        contract.write_text("Require ParkourTheories.Tests.Projection.RunAndProgressTypes.\n")
        compile_v(evidence, loads, contract)
        for policy, library, exports in (
            ("closed", "ParkourTheories.Projection.Progress", ("epp_preserves_deadlock_freedom",
              "matched_ready", "deadlock_reflection")),
            ("closed", "ParkourTheories.Projection.RunCorrespondence", ("network_run_has_source",)),
            ("client", "ParkourTheories.Protocols.QuorumVoting", ("quorum_deadlock_freedom",)),
        ):
            for name in exports:
                assumptions(evidence, loads, policy, f"{library}.{name}")
        print("PASS: public theorem witnesses and assumption reports")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="fresh evidence directory")
    parser.add_argument("--generated", type=Path, required=True, help="freshly translated Parkour library")
    parser.add_argument("--project-root", type=Path, required=True, help="compiled theories/ and tests/ tree")
    parser.add_argument("--final", action="store_true", help="require public proofs and their exact types")
    parser.add_argument("libraries", type=Path, nargs="+", help="compiled base, transformer and support roots")
    args = parser.parse_intermixed_args()
    generated = args.generated.resolve()
    check(args.output.resolve(), [arg for path in [*args.libraries, generated]
                                  for arg in ("-Q", str(path.resolve()), "")],
          args.project_root.resolve(), generated, final=args.final)
