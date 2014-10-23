Require Import AbstractSoSADL.
Require Import BinInt.
Require Import String.

(** * General interpretation outcome *)

Inductive interpretation {A: Set}: Set :=
| Interpreted: A -> interpretation
| Failed: AST.expression -> AST.expression -> interpretation.

(** * An interpretation function in [Z] *)

(** Currently, this interpretation function recognizes solely literal
interger values and arithmetic operations. *)

Local Open Scope string_scope.

Fixpoint interp_in_Z (e: AST.expression) {struct e} :=
  match e with
    | AST.IntegerValue x => Interpreted x
    | AST.UnaryExpression op x =>
      match match op with
              | "-" => Some Z.opp
              | "+" => Some id
              | _ => None
            end with
        | Some f =>
          match interp_in_Z x with
            | Interpreted y => Interpreted (f y)
            | Failed _ f => Failed e f
          end
        | None => Failed e e
      end
    | AST.BinaryExpression l op r =>
      match match op with
              | "+" => Some Z.add
              | "-" => Some Z.sub
              | "*" => Some Z.mul
              | "/" => Some Z.div
              | "mod" => Some Z.modulo
              | _ => None
            end with
        | Some f =>
          match interp_in_Z l with
            | Interpreted ll =>
              match interp_in_Z r with
                | Interpreted rr => Interpreted (f ll rr)
                | Failed _ f => Failed e f
              end
            | Failed _ f => Failed e f
          end
        | None => Failed e e
      end
    | _ => Failed e e
  end.

(** * Comparison of expressions *)

(** Currently, the sole way to prove comparison consists in
translating the SoSADL expression to [Z], then use the evaluation and
decision tools of this Coq library. *)

Inductive expression_le: AST.expression -> AST.expression -> Prop :=
| In_Z: forall l zl r zr,
          interp_in_Z l = Interpreted zl
          -> interp_in_Z r = Interpreted zr
          -> (zl <= zr)%Z
          -> l <= r

where "e1 <= e2" := (expression_le e1 e2)
.
