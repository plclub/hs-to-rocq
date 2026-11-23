Require DeadlockWireRunsExpect DeadlockWireValueExpect DeadlockWirePartial DeadlockWireParallel
  DeadlockWireQueueReject DeadlockWireSourceReject.

Definition partial_delivery : DeadlockWireRunsExpect.wire_partial_delivery :=
  DeadlockWirePartial.partial_delivery.
Definition no_invented_bytes : DeadlockWireValueExpect.wire_reject_invented_bytes :=
  DeadlockWireSourceReject.reject_invented_bytes.
Definition hidden_value_limit :
  forall e : bool = bool, eq_rect bool (fun T => T) true bool e = false ->
    DeadlockWireRunsExpect.wire_partial_delivery ->
    ~ DeadlockWireRunsExpect.wire_reject_invented_value :=
  DeadlockWireSourceReject.invented_value_transport_obstruction.
Definition no_wrong_occurrence : DeadlockWireRunsExpect.wire_reject_wrong_occurrence :=
  DeadlockWireSourceReject.reject_wrong_occurrence.
Definition no_lost_pending : DeadlockWireRunsExpect.wire_reject_lost_pending :=
  DeadlockWireQueueReject.reject_lost_pending.
Definition no_swapped_fifo : DeadlockWireRunsExpect.wire_reject_swapped_fifo :=
  DeadlockWireQueueReject.reject_swapped_fifo.
Definition app_self_completed : DeadlockWireRunsExpect.wire_app_self_completed :=
  DeadlockWireParallel.app_self_completed.
Definition no_root_tag : DeadlockWireRunsExpect.wire_app_reject_root_tag :=
  DeadlockWireParallel.app_reject_root_tag.
