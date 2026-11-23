From Stdlib Require Import Lists.List.
Import ListNotations.

(* Source edges, deliberately independent of transport session identifiers. *)
Inductive source_edge := BindPrefix | BindBody | AppFunction | AppArgument |
  ChoiceBody.
Definition occurrence := list source_edge.
Definition child (o : occurrence) e := o ++ [e].

Definition source_lane (o : occurrence) :=
  filter (fun e => match e with AppFunction | AppArgument => true | _ => false
    end) o.
