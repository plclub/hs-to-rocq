(* GHC 9.10: derived Eq instance uses GHC.Classes.Eq which hs-to-rocq
   can't resolve. Provide the instance manually. *)
#[local] Definition Eq__Test_op_zeze__ : Test -> Test -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | A, A => true
    | B, B => true
    | _, _ => false
    end.

#[local] Definition Eq__Test_op_zsze__ : Test -> Test -> bool :=
  fun a b => negb (Eq__Test_op_zeze__ a b).

#[global]
Program Instance Eq__Test : GHC.Base.Eq_ Test :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq__Test_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq__Test_op_zsze__ |}.
