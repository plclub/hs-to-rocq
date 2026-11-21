(* Standalone reduction of Tree.interp and the recursive Cond branch of epp.
   Compile with Rocq 9.0.1: rocq c Projection.v

   The outer inductive is Sig: its Cond constructor nests Sig under Tree.
   Tree's Perf constructor merely stores an element of its parameter F.
   This asymmetry matters to the guard checker even after F is set to Sig.
   Neither tree-recursive definition below passes its structural check.

   To preserve the source equations, keep project = interp handler and put the
   outer fixpoint on handler. Unfold the call project (k x) in the source
   handler by one equation to get interp handler (k x); the location argument
   is unchanged. Capture the invariant handler outside interp's inner fixpoint
   so unfolding interp exposes a specialized nested structural recursion. *)
Inductive Tree (F : Type -> Type) : Type -> Type :=
| Perf {A} : F A -> Tree F A
| Pure {A} : A -> Tree F A
| App {A B} : Tree F (A -> B) -> Tree F A -> Tree F B
| Bind {A B} : Tree F A -> (A -> Tree F B) -> Tree F B.
Arguments Perf {F A}.
Arguments Pure {F A}.
Arguments App {F A B}.
Arguments Bind {F A B}.

Definition interp {F} (handle : forall X, F X -> X) :=
  fix go {A} (t : Tree F A) : A :=
  match t with
  | Perf e => handle _ e
  | Pure x => x
  | App f x => go f (go x)
  | Bind x k => go (k (go x))
  end.

Inductive Sig : Type -> Type :=
| Cond {A B} : A -> (A -> Tree Sig B) -> Sig B.

Fail Fixpoint direct {A} (t : Tree Sig A) {struct t} : A :=
  interp (fun X (e : Sig X) =>
    match e with Cond x k => direct (k x) end) t.

Fail Fixpoint specialized {A} (t : Tree Sig A) {struct t} : A :=
  match t with
  | Perf e => match e with Cond x k => specialized (k x) end
  | Pure x => x
  | App f x => specialized f (specialized x)
  | Bind x k => specialized (k (specialized x))
  end.

Fixpoint handler {A} (e : Sig A) {struct e} : A :=
  match e with
  | Cond x k => interp (fun X e' => @handler X e') (k x)
  end.

Definition project {A} (t : Tree Sig A) : A :=
  interp (fun X e => @handler X e) t.

Example project_cond {A B} (x : A) (k : A -> Tree Sig B) :
  project (Perf (Cond x k)) = project (k x).
Proof. reflexivity. Qed.

Section Monadic.
  Variable M : Type -> Type.
  Variable pureM : forall {A}, A -> M A.
  Variable appM : forall {A B}, M (A -> B) -> M A -> M B.
  Variable bindM : forall {A B}, M A -> (A -> M B) -> M B.
  Variable broadcast : bool -> M unit.
  Variable receive : M bool.

  Definition interpM {F} (handle : forall X, F X -> M X) :=
    fix go {A} (t : Tree F A) : M A :=
    match t with
    | Perf e => handle _ e
    | Pure x => pureM x
    | App f x => appM (go f) (go x)
    | Bind x k => bindM (go x) (fun a => go (k a))
    end.

  Inductive Op : Type -> Type :=
  | Branch {B} : bool -> (bool -> Tree Op B) -> Op B.

  Fixpoint handleM (owner : bool) {A} (e : Op A) {struct e} : M A :=
    match e with
    | Branch v k =>
        let fold := interpM (fun X e' => @handleM owner X e') in
        if owner then bindM (broadcast v) (fun _ => fold (k v))
        else bindM receive (fun x => fold (k x))
    end.

  Definition eppM (owner : bool) {A} (t : Tree Op A) : M A :=
    interpM (fun X e => @handleM owner X e) t.

  Example owner_equation {B} v (k : bool -> Tree Op B) :
    eppM true (Perf (Branch v k)) =
    bindM (broadcast v) (fun _ => eppM true (k v)).
  Proof. reflexivity. Qed.

  Example peer_equation {B} v (k : bool -> Tree Op B) :
    eppM false (Perf (Branch v k)) =
    bindM receive (fun x => eppM false (k x)).
  Proof. reflexivity. Qed.
End Monadic.
Print Assumptions owner_equation.
Print Assumptions peer_equation.
