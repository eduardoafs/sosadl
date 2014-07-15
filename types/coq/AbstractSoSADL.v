Require Import List.
Require Import String.

Module AST.

(**
* Abstract syntax tree
*)

Inductive connKind: Set :=
| RegularConnection: connKind
| EnvironmentConnection: connKind.

Inductive modeType: Set :=
| In: modeType
| Out: modeType
| InOut: modeType.

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
| DataTypeDecl: string -> datatype -> list functionDecl -> datatypeDecl
with datatype: Set :=
| NamedType: string -> datatype
| TupleType: list fieldDecl -> datatype
| SequenceType: datatype -> datatype
| RangeType: expression -> expression -> datatype
with fieldDecl: Set :=
| FieldDecl: string -> datatype -> fieldDecl
with functionDecl: Set :=
| FunctionDecl: string -> string -> string -> list formalParameter -> datatype -> list valuing -> expression -> functionDecl
with formalParameter: Set :=
| FormalParameter: string -> datatype -> formalParameter
with valuing: Set :=
| Valuing: string -> option datatype -> expression -> valuing
with systemDecl: Set :=
| SystemDecl: string -> list formalParameter -> list datatypeDecl -> list gateDecl -> behaviorDecl -> option assertionDecl -> systemDecl
with mediatorDecl: Set :=
| MediatorDecl: string -> list formalParameter -> list datatypeDecl -> list dutyDecl -> behaviorDecl -> mediatorDecl
with architectureDecl: Set :=
| ArchitectureDecl: string -> list formalParameter -> list datatypeDecl -> list gateDecl -> archBehaviorDecl -> assertionDecl -> architectureDecl
with gateDecl: Set :=
| GateDecl: string -> list connection -> protocolDecl -> gateDecl
with dutyDecl: Set :=
| DutyDecl: string -> list connection -> assertionDecl -> protocolDecl -> dutyDecl
with connection:Set :=
| Connection: string -> connKind -> modeType -> datatype -> connection
with behaviorDecl: Set :=
with archBehaviorDecl: Set :=
with expression: Set :=
with assertionDecl: Set :=
with protocolDecl: Set :=
.

Definition name_of_datatypeDecl d :=
  match d with
    | DataTypeDecl n _ _ => n
  end.

Definition datatype_of_datatypeDecl d :=
  match d with
    | DataTypeDecl _ t _ => t
  end.

Definition functions_of_datatypeDecl d :=
  match d with
    | DataTypeDecl _ _ f => f
  end.

Definition name_of_fieldDecl f :=
  match f with
    | FieldDecl n _ => n
  end.

Definition type_of_fieldDecl f :=
  match f with
    | FieldDecl _ t => t
  end.

Definition name_of_functionDecl f :=
  match f with
    | FunctionDecl n _ _ _ _ _ _ => n
  end.

Definition dataName_of_functionDecl f :=
  match f with
    | FunctionDecl _ n _ _ _ _ _ => n
  end.

Definition dataTypeName_of_functionDecl f :=
  match f with
    | FunctionDecl _ _ n _ _ _ _ => n
  end.

Definition parameters_of_functionDecl f :=
  match f with
    | FunctionDecl _ _ _ p _ _ _ => p
  end.

Definition type_of_functionDecl f :=
  match f with
    | FunctionDecl _ _ _ _ t _ _ => t
  end.

Definition valuing_of_functionDecl f :=
  match f with
    | FunctionDecl _ _ _ _ _ v _ => v
  end.

Definition expression_of_functionDecl f :=
  match f with
    | FunctionDecl _ _ _ _ _ _ e => e
  end.

Definition name_of_formalParameter p :=
  match p with
    | FormalParameter n _ => n
  end.

Definition type_of_formalParameter p :=
  match p with
    | FormalParameter _ t => t
  end.

Definition variable_of_valuing v :=
  match v with
    | Valuing n _ _ => n
  end.

Definition type_of_valuing v :=
  match v with
    | Valuing _ t _ => t
  end.

Definition expression_of_valuing v :=
  match v with
    | Valuing _ _ e => e
  end.

End AST.
