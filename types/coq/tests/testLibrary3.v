Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [(Import (Some "Base"))] (Some (Library (Some "testLibrary3") (Some (EntityBlock [(DataTypeDecl (Some "Abscissa") None []); (DataTypeDecl (Some "Ordinate") None []); (DataTypeDecl (Some "Distance") None []); (DataTypeDecl (Some "Coordinate") (Some (TupleType [(FieldDecl (Some "x") (Some (NamedType (Some "Abscissa")))); (FieldDecl (Some "y") (Some (NamedType (Some "Ordinate"))))])) [(FunctionDecl (Some "onecoordinate") (Some "Coordinate") (Some "distance") [(FormalParameter (Some "othercoordinate") (Some (NamedType (Some "Coordinate"))))] (Some (NamedType (Some "Distance"))) [] (Some (CallExpression (Some "sqrt") [(BinaryExpression (Some (CallExpression (Some "sqr") [(BinaryExpression (Some (Field (Some (IdentExpression (Some "onecoordinate"))) (Some "x"))) (Some "-") (Some (Field (Some (IdentExpression (Some "othercoordinate"))) (Some "x"))))])) (Some "+") (Some (CallExpression (Some "sqr") [(BinaryExpression (Some (Field (Some (IdentExpression (Some "onecoordinate"))) (Some "y"))) (Some "-") (Some (Field (Some (IdentExpression (Some "othercoordinate"))) (Some "y"))))])))])))]); (DataTypeDecl (Some "Depth") None []); (DataTypeDecl (Some "MeasureData") (Some (TupleType [(FieldDecl (Some "coordinate") (Some (NamedType (Some "Coordinate")))); (FieldDecl (Some "depth") (Some (NamedType (Some "Depth"))))])) []); (DataTypeDecl (Some "MeasureDataBase") (Some (SequenceType (Some (NamedType (Some "MeasureData"))))) [])] [] [] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
