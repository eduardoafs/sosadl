Require Import AbstractSoSADL.

Inductive subtype: AST.datatype -> AST.datatype -> Prop :=

where "t1 < t2" := (subtype t1 t2)
.
