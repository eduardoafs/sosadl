Require Import AbstractSoSADL.
Require Import BinInt.

Inductive interpretation {A: Set}: Set :=
| Interpreted: A -> interpretation
| Failed: AST.expression -> AST.expression -> interpretation.

Fixpoint interp_in_Z (e: AST.expression) {struct e} :=
  match e with
    | AST.IntegerValue x => Interpreted x
    | AST.UnaryExpression "-" x =>
      (match interp_in_Z x with
         | Interpreted y => Interpreted (- y)%Z
         | Failed _ f => Failed e f
       end)
    | AST.BinaryExpression l "+" r =>
      (match interp_in_Z l with
         | Interpreted ll =>
           (match interp_in_Z r with
              | Interpreted rr => Interpreted (ll + rr)%Z
              | Failed _ f => Failed e f
            end)
         | Failed _ f => Failed e f
       end)
    | AST.BinaryExpression l "-" r =>
      (match interp_in_Z l with
         | Interpreted ll =>
           (match interp_in_Z r with
              | Interpreted rr => Interpreted (ll - rr)%Z
              | Failed _ f => Failed e f
            end)
         | Failed _ f => Failed e f
       end)
    | AST.BinaryExpression l "*" r =>
      (match interp_in_Z l with
         | Interpreted ll =>
           (match interp_in_Z r with
              | Interpreted rr => Interpreted (ll * rr)%Z
              | Failed _ f => Failed e f
            end)
         | Failed _ f => Failed e f
       end)
    | AST.BinaryExpression l "/" r =>
      (match interp_in_Z l with
         | Interpreted ll =>
           (match interp_in_Z r with
              | Interpreted rr => Interpreted (ll / rr)%Z
              | Failed _ f => Failed e f
            end)
         | Failed _ f => Failed e f
       end)
    | AST.BinaryExpression l "mod" r =>
      (match interp_in_Z l with
         | Interpreted ll =>
           (match interp_in_Z r with
              | Interpreted rr => Interpreted (ll mod rr)%Z
              | Failed _ f => Failed e f
            end)
         | Failed _ f => Failed e f
       end)
    | _ => Failed e e
  end.

Inductive expression_le: AST.expression -> AST.expression -> Prop :=
| In_Z: forall l zl r zr,
          interp_in_Z l = Interpreted zl
          -> interp_in_Z r = Interpreted zr
          -> (zl <= zr)%Z
          -> l <= r

where "e1 <= e2" := (expression_le e1 e2)
.
