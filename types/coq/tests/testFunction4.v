Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testFunction4") (Some (EntityBlock [(DataTypeDecl (Some "type1") (Some (TupleType [(FieldDecl (Some "x") (Some IntegerType)); (FieldDecl (Some "y") (Some IntegerType))])) [(FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type1"))))) (Some "addx") [(FormalParameter (Some "right") (Some (NamedType (Some "type1"))))] (Some (NamedType (Some "type1"))) [] (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "left"))) (Some "x"))) (Some "+") (Some (Field (Some (IdentExpression (Some "right"))) (Some "x")))))); (FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type1"))))) (Some "addy") [(FormalParameter (Some "right") (Some (NamedType (Some "type1"))))] (Some (NamedType (Some "type1"))) [] (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "left"))) (Some "y"))) (Some "+") (Some (Field (Some (IdentExpression (Some "right"))) (Some "y"))))))])] [(FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type1"))))) (Some "multx") [(FormalParameter (Some "right") (Some (NamedType (Some "type1"))))] (Some (NamedType (Some "type1"))) [] (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "left"))) (Some "x"))) (Some "*") (Some (Field (Some (IdentExpression (Some "right"))) (Some "x")))))); (FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type1"))))) (Some "multy") [(FormalParameter (Some "right") (Some (NamedType (Some "type1"))))] (Some (NamedType (Some "type1"))) [] (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "left"))) (Some "y"))) (Some "*") (Some (Field (Some (IdentExpression (Some "right"))) (Some "y"))))))] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type2") (Some (RangeType (Some (IntegerValue (Some 1))) (Some (IntegerValue (Some 2))))) [(FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type2"))))) (Some "addx") [(FormalParameter (Some "right") (Some (NamedType (Some "type2"))))] (Some (NamedType (Some "type2"))) [] (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "left"))) (Some "x"))) (Some "+") (Some (Field (Some (IdentExpression (Some "right"))) (Some "x")))))); (FunctionDecl (Some (FormalParameter (Some "left") (Some (NamedType (Some "type2"))))) (Some "addy") [(FormalParameter (Some "right") (Some (NamedType (Some "type2"))))] (Some (NamedType (Some "type2"))) [] (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "left"))) (Some "y"))) (Some "+") (Some (Field (Some (IdentExpression (Some "right"))) (Some "y"))))))])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeOut) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [ProtocolStatement_Done])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [BehaviorStatement_Done])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
