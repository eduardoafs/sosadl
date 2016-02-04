Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testDoExpr11") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") (Some IntegerType) [(FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type1"))))) (Some "add") [(FormalParameter (Some "right") (Some (NamedType (Some "type1"))))] (Some (NamedType (Some "type1"))) [] (Some (BinaryExpression (Some (IdentExpression (Some "left"))) (Some "+") (Some (IdentExpression (Some "right"))))))])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "x") (Some (NamedType (Some "type1"))) (Some (IntegerValue (Some 0)))); (ProtocolStatement_DoExpr (Some (MethodCall (Some (IdentExpression (Some "x"))) (Some "add") [(IntegerValue (Some 1))])))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "x") (Some (NamedType (Some "type1"))) (Some (IntegerValue (Some 1)))); (BehaviorStatement_DoExpr (Some (MethodCall (Some (IdentExpression (Some "x"))) (Some "add") [(IntegerValue (Some 1))])))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
