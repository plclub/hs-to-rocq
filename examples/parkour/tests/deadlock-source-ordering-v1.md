# Frozen source ordering slice, v1

This manifest is an acceptance input, not a report of proofs.
The source is the actual generated ChoreoSig and Tree syntax.
Occurrence identities are lists of source edges (bind prefix, bind body,
app function, app argument, conditional body); they are not session IDs.

Fixed roles are A = [] and B = [1]. Local effects return bool. Wait has
no reply; Act replies true without changing the nat store.

Required affirmative propositions:

1. At B, `Bind (Locally A Wait) (fun _ => Locally B Act)` admits B's
   Act event at store 0, with no event or result required from A.
2. An explicit App with Wait on the left and Act on the right admits
   the right event at the same role and shared store.
3. A sends true and then false at two different Bind source paths;
   both deliveries may remain pending, in that order, before B receives.

Required negative propositions:

4. At B, `Bind (Comm A true B) (fun _ => Locally B Act)` with an
   empty pending queue has no action, even though the continuation
   ignores its argument.
5. At B, `Bind (Comm A true B) (fun x => Comm B x A)` with an
   empty pending queue has no action: no invented forwarding value.
6. A receive of false cannot consume the head true in the two-message
   queue. Distinct source paths do not authorize skipping an earlier
   outstanding delivery on the same source channel.

Scope: this slice does not claim a well-formedness theorem, simulation,
or deadlock preservation. Those require separate frozen contracts.
