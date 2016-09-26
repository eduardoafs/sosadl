Require Import SosADL.SosADL.
Require Import List.
Require Import String.
Require Import BinInt.

Delimit Scope sosadl_scope with sosadl.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.


Notation "- x" := (SosADL.SosADL.UnaryExpression (Some "-") (Some x)) : sosadl_scope.
Notation "+ x" := (SosADL.SosADL.UnaryExpression (Some "+") (Some x)) (at level 35, x at level 35) : sosadl_scope.

Notation "l * r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "*") (Some r)) : sosadl_scope.
Notation "l / r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "/") (Some r)) : sosadl_scope.
Notation "l 'mod' r" :=
  (SosADL.SosADL.BinaryExpression (Some l) (Some "mod") (Some r)) : sosadl_scope.

Notation "l + r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "+") (Some r)) : sosadl_scope.
Notation "l - r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "-") (Some r)) : sosadl_scope.

Notation "l < r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "<") (Some r)) : sosadl_scope.
Notation "l <= r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "<=") (Some r)) : sosadl_scope.
Notation "l > r" := (SosADL.SosADL.BinaryExpression (Some l) (Some ">") (Some r)) : sosadl_scope.
Notation "l >= r" := (SosADL.SosADL.BinaryExpression (Some l) (Some ">=") (Some r)) : sosadl_scope.
Notation "l = r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "=") (Some r)) : sosadl_scope.
Notation "l <> r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "<>") (Some r)) : sosadl_scope.

Notation "l '->' r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "implies") (Some r)) : sosadl_scope.
Notation "l '&&' r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "and") (Some r)) : sosadl_scope.
Notation "l '||' r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "or") (Some r)) : sosadl_scope.
Notation "l '^^' r" := (SosADL.SosADL.BinaryExpression (Some l) (Some "xor") (Some r)) (at level 50, left associativity) : sosadl_scope.
Notation "! x" := (SosADL.SosADL.UnaryExpression (Some "not") (Some x)) (at level 35, x at level 35) : sosadl_scope.

Notation "[ l , r ]" := (SosADL.SosADL.RangeType (Some l) (Some r)) (at level 0, l at level 200, r at level 200) : sosadl_scope.

Notation "s :: { x -> e }" := (SosADL.SosADL.Map (Some s) (Some x) (Some e)) (at level 59, x at level 1, e at level 200, left associativity) : sosadl_scope.
Notation "s :: { x | e }" := (SosADL.SosADL.Select (Some s) (Some x) (Some e)) (at level 59, x at level 1, e at level 200, left associativity) : sosadl_scope.

Notation "s ::: f" := (SosADL.SosADL.Field (Some s) (Some f)) (at level 59, f at level 1, left associativity) : sosadl_scope.

Notation "'valuing' x = e" := (SosADL.SosADL.Valuing (Some x) None (Some e)) (at level 200, x at level 1) : sosadl_scope.
Notation "'valuing' x 'is' t = e" := (SosADL.SosADL.Valuing (Some x) (Some t) (Some e)) (at level 200, x at level 1, t at level 1) : sosadl_scope.

Notation "# a" := (IntegerValue (Some a)) (at level 0) : sosadl_scope.