Require Import List.
Require Import String.
Require Import BinInt.

(**
%
\def\todo#1{{\color{red}TODO: #1}}
\def\note#1{{\color{blue}NOTE: #1}}
%
*)

Module AST.

(** * Abstract syntax tree *)

(** %\note{%The following type for the abstract syntax tree is
(smartly) extracted from the Xtext grammar / Ecore meta-model,
by-hand.%}% *)

Definition complexName := list string.

Inductive connKind: Set :=
| RegularConnection: connKind
| EnvironmentConnection: connKind.

Inductive modeType: Set :=
| In: modeType
| Out: modeType
| InOut: modeType.

Inductive quantifier: Set :=
| QuantifierForall: quantifier
| QuantifierExists: quantifier.

Inductive multiplicity: Set :=
| MultiplicityOne: multiplicity
| MultiplicityNone: multiplicity
| MultiplicityLone: multiplicity
| MultiplicityAny: multiplicity
| MultiplicitySome: multiplicity
| MultiplicityAll: multiplicity.

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
| DataTypeDecl: string -> option datatype -> list functionDecl -> datatypeDecl

(** %\note{%[IntegerType] and [ConnectionType] are volountarily
omitted: the former can be represented by [RangeType]; the latter is
in fact not used. A new [BooleanType] is added for the purpose of
typing rules.%}% *)

with datatype: Set :=
| NamedType: string -> datatype
| TupleType: list fieldDecl -> datatype
| SequenceType: datatype -> datatype
| RangeType: expression -> expression -> datatype
| BooleanType: datatype

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
| BehaviorDecl: string -> list formalParameter -> behavior -> behaviorDecl

with archBehaviorDecl: Set :=
| ArchBehaviorDecl: string -> list formalParameter -> list constituent -> expression -> archBehaviorDecl

with constituent: Set :=
| Constituent: string -> expression -> constituent

with expression: Set :=
| IntegerValue: Z -> expression
| Quantify: quantifier -> list elementInConstituent -> expression -> expression
| Relay: complexName -> complexName -> expression
| Unify: multiplicity -> complexName -> multiplicity -> complexName -> expression
| Any: expression
| UnaryExpression: string -> expression -> expression
| BinaryExpression: expression -> string -> expression -> expression
| IdentExpression: string -> expression
| UnobservableValue: expression
| MethodCall: expression -> string -> list expression -> expression
| Tuple: list tupleElement -> expression
| Sequence: list expression -> expression
| CallExpression: string -> list expression -> expression
| Map: expression -> string -> expression -> expression
| Select: expression -> string -> expression -> expression
| Field: expression -> string -> expression

with tupleElement: Set :=
| TupleElement: string -> expression -> tupleElement

with elementInConstituent: Set :=
| ElementInConstituent: string -> string -> elementInConstituent

with assertionDecl: Set := (** %\todo{%TBD%}% *)

with protocolDecl: Set := (** %\todo{%TBD%}% *)

with behavior: Set :=
| Behavior: list statement -> behavior

with statement: Set :=
| ValuingStatement: valuing -> statement
| AssertStatement: assert -> statement
| ActionStatement: action -> statement
| RepeatBehavior: behavior -> statement
| IfThenElseBehavior: expression -> behavior -> option behavior -> statement
| ChooseBehavior: list behavior -> statement
| ForEachBehavior: string -> expression -> behavior -> statement
| DoExpr: expression -> statement
| Done: statement
| RecursiveCall: list expression -> statement

with assert: Set :=
| Tell: string -> expression -> assert
| Ask: string -> expression -> assert

with action: Set :=
| Action: complexName -> actionSuite -> action

with actionSuite: Set :=
| SendAction: expression -> actionSuite
| ReceiveAction: string -> actionSuite
.

(** * Some utility functions *)

(** %\note{%Most of these functions would have been automatically
generated if [Record] were used. But Coq does not support mutually
recursive [Record] definition.%}% *)

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

Definition body_of_behavior b :=
  match b with
    | Behavior l => l
  end.

Definition name_of_gateDecl g :=
  match g with
    | GateDecl n _ _ => n
  end.

Definition name_of_dutyDecl d :=
  match d with
    | DutyDecl n _ _ _ => n
  end.

Definition name_of_systemDecl s :=
  match s with
    | SystemDecl name _ _ _ _ _ => name
  end.

Definition name_of_mediatorDecl s :=
  match s with
    | MediatorDecl name _ _ _ _ => name
  end.

Definition name_of_architectureDecl s :=
  match s with
    | ArchitectureDecl name _ _ _ _ _ => name
  end.

Definition name_of_connection c :=
  match c with
    | Connection name _ _ _ => name
  end.

Definition mode_of_connection c :=
  match c with
    | Connection _ _ mode _ => mode
  end.

Definition datatype_of_connection c :=
  match c with
    | Connection _ _ _ t => t
  end.

Definition name_of_tupleElement t :=
  match t with
    | TupleElement n _ => n
  end.

Definition expression_of_tupleElement t :=
  match t with
    | TupleElement _ e => e
  end.

Fixpoint names_of_expression (x: expression) {struct x} :=
  match x with
    | IntegerValue _ => nil
    | Quantify _ _ _ => (** %\todo{%TBD%}% *) nil
    | Relay _ _ => (** %\todo{%TBD%}% *) nil
    | Unify _ _ _ _ => (** %\todo{%TBD%}% *) nil
    | Any => nil
    | UnaryExpression _ e => names_of_expression e
    | BinaryExpression e _ f => (names_of_expression) e ++ (names_of_expression) f
    | IdentExpression a => a :: nil
    | UnobservableValue => nil
    | MethodCall t _ l => (names_of_expression t)
                           ++ (List.flat_map names_of_expression l)
    | Tuple l => List.flat_map
                  (fun a => names_of_expression (expression_of_tupleElement a)) l
    | Sequence l => List.flat_map names_of_expression l
    | CallExpression _ l => List.flat_map names_of_expression l
    | Map c n e => (names_of_expression c)
                    ++ (List.remove string_dec n (names_of_expression e))
    | Select c n e => (names_of_expression c)
                       ++ (List.remove string_dec n (names_of_expression e))
    | Field e _ => names_of_expression e
  end.

End AST.
