Require SosADL.SosADL.
Require Import BinInt.
Require Import String.

(** * General interpretation outcome *)

Inductive interpretation {A: Set}: Set :=
| Interpreted: A -> interpretation
| Failed: SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> interpretation.

(** * An interpretation function in [Z] *)

(** Currently, this interpretation function recognizes solely literal
interger values and arithmetic operations. *)

Local Open Scope string_scope.

Fixpoint interp_in_Z (e: SosADL.SosADL.t_Expression) {struct e} :=
  match e with
    | SosADL.SosADL.IntegerValue (Some x) => Interpreted x
    | SosADL.SosADL.UnaryExpression (Some op) (Some x) =>
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
    | SosADL.SosADL.BinaryExpression (Some l) (Some op) (Some r) =>
      match match op with
              | "+" => Some Z.add
              | "-" => Some Z.sub
              | "*" => Some Z.mul
              | "/" => Some Z.quot
              | "mod" => Some Z.rem
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

Inductive expression_le: SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> Prop :=
| In_Z: forall
    (l: SosADL.SosADL.t_Expression)
    (zl: BinInt.Z)
    (r: SosADL.SosADL.t_Expression)
    (zr: BinInt.Z)
    (p1: interp_in_Z l = Interpreted zl)
    (p2: interp_in_Z r = Interpreted zr)
    (p3: (zl <=? zr = true)%Z)
  ,
    l <= r

where "e1 <= e2" := (expression_le e1 e2)
.

Ltac decide_in_Z :=
  match goal with
    | |- Interpretation.expression_le ?l ?r =>
      eapply Interpretation.In_Z;
        [ reflexivity | reflexivity | discriminate ]
  end.
