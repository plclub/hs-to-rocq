From Stdlib Require Import Lists.List.
Require Import Behavior.
Require Import Control.Monad.Tree Choreography.Network Choreography.Choreo2.
Require Control.Monad.Trans.Reader.
Import ListNotations.

(* The Cond broadcast and its continuation are sequential. Only an App
   inside that continuation splits the current session into child sessions.
   These assertions compute the generated epp, not a replacement projection. *)
Definition parallelBranch {p} : Choreo Id p unit :=
  App (Bind (@action p) (fun _ => Pure (fun x : unit => x))) action.

Definition ownerChoice {p} (choice : bool) : Choreo Id p unit :=
  cond (Mk_At (l := sender) (fun _ => choice))
       (fun chosen => if chosen then parallelBranch else action).

(* A flattened trace cannot distinguish App from Bind. Inspect the generated
   network root as well: the owner must not fork its broadcast and branch. *)
Example owner_cond_sequential :
  match Control.Monad.Trans.Reader.runReaderT
          (unEpp (epp (@ownerChoice sender true) (@Parkour.Symbol.MkSSymbol
            sender))) here with
  | Bind _ _ => true
  | _ => false
  end = true.
Proof. reflexivity. Qed.

Example owner_cond_app :
  project (@ownerChoice sender true) here =
  ([Broadcast here payload;
    Sent (leftChild here) peer payload;
    Sent (rightChild here) peer payload], Some tt).
Proof. reflexivity. Qed.

Example owner_cond_false :
  project (@ownerChoice sender false) here =
  ([Broadcast here reply; Sent here peer payload], Some tt).
Proof. reflexivity. Qed.

(* The observer supplies False to Recv, so the peer chooses the single-action
   branch. The receipt and branch action both retain the Cond's session. *)
Example peer_cond_false :
  project (@ownerChoice peer true) here =
  ([Received here sender; Received here sender], Some tt).
Proof. reflexivity. Qed.

Example owner_cond_then_action :
  project (Bind (@ownerChoice sender true) (fun _ => action)) here =
  ([Broadcast here payload;
    Sent (leftChild here) peer payload;
    Sent (rightChild here) peer payload;
    Sent here peer payload], Some tt).
Proof. reflexivity. Qed.
