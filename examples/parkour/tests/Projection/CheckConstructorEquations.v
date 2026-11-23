From ParkourTheories.Tests.Projection Require Import ConstructorEquationTypes.
From ParkourTheories.Projection Require ConstructorEquations.

(* Keep the expected types independent of the implementation. Each check
   instantiates a proved library equation at its independently stated type. *)
Check ConstructorEquations.runner_pure : pure_equation.
Check ConstructorEquations.runner_bind : bind_equation.
Check ConstructorEquations.runner_app : app_equation.
Check ConstructorEquations.runner_locally_owner : locally_owner_equation.
Check ConstructorEquations.runner_locally_other : locally_other_equation.
Check ConstructorEquations.runner_comm_self : comm_self_equation.
Check ConstructorEquations.runner_comm_sender : comm_sender_equation.
Check ConstructorEquations.runner_comm_receiver : comm_receiver_equation.
Check ConstructorEquations.runner_comm_other : comm_other_equation.
Check ConstructorEquations.runner_cond_owner : cond_owner_equation.
Check ConstructorEquations.runner_cond_peer : cond_peer_equation.
Check ConstructorEquations.runner_par : par_equation.
Check ConstructorEquations.runner_root : root_equation.
