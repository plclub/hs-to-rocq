Require Probe.

Check @Probe.keep : forall a : Type, a -> a.
Example computed : Probe.keep true = true /\ Probe.keep false = false.
Proof. split; reflexivity. Qed.
