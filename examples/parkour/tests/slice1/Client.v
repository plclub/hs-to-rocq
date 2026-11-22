Require Parkour.Runtime.
Parameter IO : Type -> Type.
Definition allowed := Runtime.IO nat.
Definition mixed := (Runtime.IO nat * IO nat)%type.
