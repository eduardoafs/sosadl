Require Import List.
Require Import String.

(**
* Abstract syntax tree
*)

Inductive sosADL: Set :=
| SosADL: list import -> unit -> sosADL
with import: Set :=
| Import: string -> import
with unit: Set :=
| SoS: string -> entityBlock -> unit
| Library: string -> entityBlock -> unit
with entityBlock: Set :=
| EntityBlock: list datatypeDecl -> list functionDecl -> list systemDecl -> list mediatorDecl -> list architectureDecl -> entityBlock
with datatypeDecl: Set :=
| DataTypeDecl: datatype -> list functionDecl -> datatypeDecl
with datatype: Set :=
| NamedType: string -> datatype
| TupleType: list fieldDecl -> datatype
| SequenceType: datatype -> datatype
| RangeType: expression -> expression -> datatype
with fieldDecl: Set :=
| FieldDecl: string -> datatype -> fieldDecl
with functionDecl: Set :=
with systemDecl: Set :=
with mediatorDecl: Set :=
with architectureDecl: Set :=
with expression: Set :=
.

Definition name_of_fieldDecl f :=
  match f with
    | FieldDecl n _ => n
  end.

Definition type_of_fieldDecl f :=
  match f with
    | FieldDecl _ t => t
  end.
