From ParkourTheories.Tests.FIFO Require ScheduledTraceContracts
  WrongAnnouncementValue PartialDelivery ParallelExchanges InvalidQueueOrder
  InvalidSourceTraces.

Definition partial_delivery : ScheduledTraceContracts.wire_partial_delivery :=
  PartialDelivery.partial_delivery.
Definition no_invented_bytes : WrongAnnouncementValue.wire_reject_invented_bytes
  :=
  InvalidSourceTraces.reject_invented_bytes.
Definition hidden_value_limit :
  forall e : bool = bool, eq_rect bool (fun T => T) true bool e = false ->
    ScheduledTraceContracts.wire_partial_delivery ->
    ~ ScheduledTraceContracts.wire_reject_invented_value :=
  InvalidSourceTraces.invented_value_transport_obstruction.
Definition no_wrong_occurrence :
  ScheduledTraceContracts.wire_reject_wrong_occurrence :=
  InvalidSourceTraces.reject_wrong_occurrence.
Definition no_lost_pending : ScheduledTraceContracts.wire_reject_lost_pending :=
  InvalidQueueOrder.reject_lost_pending.
Definition no_swapped_fifo : ScheduledTraceContracts.wire_reject_swapped_fifo :=
  InvalidQueueOrder.reject_swapped_fifo.
Definition app_self_completed : ScheduledTraceContracts.wire_app_self_completed
  :=
  ParallelExchanges.app_self_completed.
Definition no_root_tag : ScheduledTraceContracts.wire_app_reject_root_tag :=
  ParallelExchanges.app_reject_root_tag.
