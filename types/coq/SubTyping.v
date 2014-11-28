Require SosADL.

Module AST := SosADL.

(**
%
\def\todo#1{{\color{red}TODO: #1}}
\def\note#1{{\color{blue}NOTE: #1}}
%
*)

(** * Subtyping relation *)

Inductive subtype: AST.t_DataType -> AST.t_DataType -> Prop :=
| subtype_refl: forall t, t < t

(** %\todo{%TBD%}% *)

where "t1 < t2" := (subtype t1 t2)
.
