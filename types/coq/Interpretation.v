Require Import AbstractSoSADL.

Inductive expression_le: AST.expression -> AST.expression -> Prop :=

where "e1 <= e2" := (expression_le e1 e2)
.
