From Stdlib Require Import Lists.List Strings.String.
Require Import Parkour.Symbol Parkour.Codec.
Require Import Control.Monad.Tree Choreography.Network Choreography.Choreo2.
Require Control.Monad.Trans.Reader.
Import ListNotations.

(* Interpret only the resulting network syntax. Exec is pure in these
   examples. A receive consumes the literal False, while a send records the
   actual payload, session ID and destination from the generated tree. *)
Definition Id (A : Type) := A.
Inductive Event :=
| Sent (sid : SessionId) (dest payload : Symbol)
| Received (sid : SessionId) (src : Symbol)
| Broadcast (sid : SessionId) (payload : Symbol).
Definition Trace (A : Type) := (list Event * option A)%type.
Definition reply := GHC.Base.hs_string__ "False".

Definition observeOp {A} (op : NetworkSig Id A) : Trace A :=
  match op with
  | Exec a => ([], Some a)
  | @Send _ a sh sid x dest => ([Sent sid dest (@show a sh x)], Some tt)
  | @Recv _ a rd sid src => ([Received sid src], @read a rd reply)
  | @BCast _ a sh sid x => ([Broadcast sid (@show a sh x)], Some tt)
  end.

Fixpoint observe {A} (t : Network Id A) : Trace A :=
  match t with
  | Perf op => observeOp op
  | Pure x => ([], Some x)
  | App f x =>
      let '(l, vf) := observe f in
      let '(r, vx) := observe x in
      (List.app l r, match vf, vx with Some g, Some a => Some (g a) | _, _ => None end)
  | Bind t k =>
      let '(l, vx) := observe t in
      match vx with
      | Some x => let '(r, v) := observe (k x) in (List.app l r, v)
      | None => (l, None)
      end
  end.

Definition project {p A} (c : Choreo Id p A) sid :=
  observe (Control.Monad.Trans.Reader.runReaderT
             (unEpp (epp c (@MkSSymbol p))) sid).
Definition sender := GHC.Base.hs_string__ "sender".
Definition peer := GHC.Base.hs_string__ "peer".
Definition payload := GHC.Base.hs_string__ "True".
Definition here := Nest (Data.Either.Left tt) Root.
Definition leftChild := Nest (Data.Either.Left tt).
Definition rightChild := Nest (Data.Either.Right tt).

Example session_id_equality :
  (GHC.Base.op_zeze__ (leftChild here) (leftChild here),
   GHC.Base.op_zeze__ (leftChild here) (leftChild (rightChild Root))) =
  (true, false).
Proof. reflexivity. Qed.

Definition message {p} : Choreo Id p (At bool peer p) :=
  Choreography.Choreo2.op_z7eUzg__
    (Mk_At (l := sender) (fun _ => true)) (@MkSSymbol peer).

Example sender_trace :
  fst (project (@message sender) here) = [Sent here peer payload].
Proof. reflexivity. Qed.
Example receiver_trace :
  fst (project (@message peer) here) = [Received here sender].
Proof. reflexivity. Qed.

Definition action {p} : Choreo Id p unit :=
  Bind (@message p) (fun _ => Pure tt).
Definition application : Choreo Id sender unit :=
  App (Bind action (fun _ => Pure (fun x : unit => x))) action.

Example app_ids :
  fst (project application here) =
  [Sent (leftChild here) peer payload; Sent (rightChild here) peer payload].
Proof. reflexivity. Qed.
Example par_ids :
  fst (project (Control.Monad.Tree.par (@action sender) action) here) =
  [Sent (rightChild (leftChild here)) peer payload; Sent (rightChild here) peer payload].
Proof. reflexivity. Qed.
Example bind_ids :
  fst (project (Bind (@action sender) (fun _ => action)) here) =
  [Sent here peer payload; Sent here peer payload].
Proof. reflexivity. Qed.

Definition branch {p} : Choreo Id p bool :=
  cond (Mk_At (l := sender) (fun _ => true)) (fun chosen => Pure chosen).

Example owner_continues :
  project (@branch sender) here = ([Broadcast here payload], Some true).
Proof. reflexivity. Qed.
Example peer_continues :
  project (@branch peer) here = ([Received here sender], Some false).
Proof. reflexivity. Qed.
