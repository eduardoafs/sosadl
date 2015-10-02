Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testFunction3") (Some (EntityBlock [(DataTypeDecl (Some "type1") (Some (RangeType (Some (IntegerValue (Some 0))) (Some (IntegerValue (Some 1))))) [(FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type1"))))) (Some "add") [(FormalParameter (Some "right") (Some (NamedType (Some "type1"))))] (Some (NamedType (Some "type1"))) [] (Some (BinaryExpression (Some (IdentExpression (Some "left"))) (Some "+") (Some (IdentExpression (Some "right")))))); (FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type1"))))) (Some "mult") [(FormalParameter (Some "right") (Some (NamedType (Some "type1"))))] (Some (NamedType (Some "type1"))) [] (Some (BinaryExpression (Some (IdentExpression (Some "left"))) (Some "*") (Some (IdentExpression (Some "right"))))))])] [(FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type1"))))) (Some "divide") [(FormalParameter (Some "right") (Some (NamedType (Some "type1"))))] (Some (NamedType (Some "type1"))) [] (Some (BinaryExpression (Some (IdentExpression (Some "left"))) (Some "div") (Some (IdentExpression (Some "right"))))))] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type2") (Some (RangeType (Some (IntegerValue (Some 1))) (Some (IntegerValue (Some 2))))) [(FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type2"))))) (Some "add") [(FormalParameter (Some "right") (Some (NamedType (Some "type2"))))] (Some (NamedType (Some "type2"))) [] (Some (BinaryExpression (Some (IdentExpression (Some "left"))) (Some "+") (Some (IdentExpression (Some "right")))))); (FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type2"))))) (Some "mult") [(FormalParameter (Some "right") (Some (NamedType (Some "type2"))))] (Some (NamedType (Some "type2"))) [] (Some (BinaryExpression (Some (IdentExpression (Some "left"))) (Some "*") (Some (IdentExpression (Some "right"))))))])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeOut) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [ProtocolStatement_Done])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [BehaviorStatement_Done])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
