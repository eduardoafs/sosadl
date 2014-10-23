Require Import AbstractSoSADL.

(**
%
\def\todo#1{{\color{red}TODO: #1}}
\def\note#1{{\color{blue}NOTE: #1}}
%
*)

(** * Subtyping relation *)

Inductive subtype: AST.datatype -> AST.datatype -> Prop :=
| subtype_refl: forall t, t < t

(** %\todo{%TBD%}% *)

where "t1 < t2" := (subtype t1 t2)
.
