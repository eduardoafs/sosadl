Require Import SosADL.SosADL.
Require Import String.

Delimit Scope sosadl_scope with SosADL.

Local Open Scope string_scope.

Notation "a + b" := (BinaryExpression (Some a) (Some "+") (Some b)) : sosadl_scope.
Notation "a - b" := (BinaryExpression (Some a) (Some "-") (Some b)) : sosadl_scope.
Notation "a * b" := (BinaryExpression (Some a) (Some "*") (Some b)) : sosadl_scope.
Notation "a / b" := (BinaryExpression (Some a) (Some "/") (Some b)) : sosadl_scope.
Notation "a 'mod' b" := (BinaryExpression (Some a) (Some "mod") (Some b)) (at level 40, no associativity) : sosadl_scope.

Notation "- a" := (UnaryExpression (Some "-") (Some a)) : sosadl_scope.

Notation "# a" := (IntegerValue (Some a)) (at level 0) : sosadl_scope.