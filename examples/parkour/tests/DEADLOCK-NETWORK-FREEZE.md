# Network acceptance inputs (frozen before proof bodies)

The operational core must use generated `Tree` and `NetworkSig`, not the old
counterexample interpreter. Queues contain only wire strings, keyed by the exact
sender, receiver, and generated session. Broadcast is atomic to all other roles.
Steps contain one send, receive, announcement, or enabled local event; finite
pure/ITree bookkeeping is not a step.

Independent fixed cases:

1. Roles A = [] and B = [1]. Empty queue. A sends the literal Boolean true
   at Root; B receives at Root. A can send before B receives.
2. At one role App has an empty receive on the left and a send on the right:
   the right can act. Mirror this input to exercise left context.
3. Two ready sends under App admit both branch successors.
4. Two empty receives admit no action. Wrong session, wrong sender, and
   wrong receiver cannot enable a receive; an undecodable head is not skipped.
5. Root enqueue of true then false yields these two wire strings in order.
6. Broadcast on [A; B; C] writes B and C atomically and never A.
   Broadcast on [A] leaves every queue empty.
7. Pure application/join and Bind of Pure return without an action.
   Returned endpoints plus a nonempty queue are not final.
8. Local request Wait requires the shared Boolean flag true; Set changes it
   from false to true. At one role an App with Wait on the left and Set on
   the right steps right, then left with the updated flag. Mirror it.
9. Two local events in sequence require two steps; a returned local tree
   is silent; an infinite Tau-only local tree cannot act or return.

This records inputs and expected results independently of implementation
proof bodies. The digest manifest freezes this document before those bodies.
It is not an assertion that all listed cases have already been proved.
