Require Import List.
Require Import String.
Require Import AbstractSoSADL.
Require Import Environment.
Require Import Utils.
Require Import SubTyping.
Require Import Interpretation.

(** printing Delta $\Delta$ #&Delta;# *)
(** printing Phi $\Phi$ #&Phi;# *)
(** printing Gamma $\Gamma$ #&Gamma;# *)
(** printing tau $\tau$ #&tau;# *)
(** printing Pi $\Pi$ #&Pi;# *)
(** printing empty $\emptyset$ #&empty;# *)

(**
%
\def\todo#1{{\color{red}TODO: #1}}
\def\note#1{{\color{blue}NOTE: #1}}
%
*)

(**
%\todo{Must consider the task of merging environment such that different objects of different kinds (e.g., a variable, a system, a type, etc) cannot share the same name.}%
*)

(**
 * Kinds of environments
 *)
Inductive gd_env_content: Set :=
| GDConnection: AST.modeType -> AST.datatype -> gd_env_content.

Inductive env_content: Set :=
| EType: AST.datatypeDecl -> env_content
| EFunction: AST.functionDecl -> env_content
| ESystem: env_content
| EMediator: env_content
| EArchitecture: env_content
| EGateOrDuty: environment gd_env_content -> env_content
| EVariable: AST.datatype -> env_content.

Definition env := environment env_content.

(**
 * Notations used for type judgments
 *)

Reserved Notation "'SoSADL' a 'well' 'typed'" (at level 200, no associativity).
Reserved Notation "'unit' u 'well' 'typed'" (at level 200, no associativity).
Reserved Notation "'entity' u 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'typedecl' t 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'functions' 'of' 'typedecl' t 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'function' f 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'type' t 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'system' s 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'systemblock' s 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'mediator' m 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'mediatorblock' m 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'architecture' a 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'architectureblock' a 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'expression' e 'has' 'type' t 'in' Gamma" (at level 200, no associativity, Gamma at level 1).
Reserved Notation "'expression' e 'under' v 'has' 'type' t 'in' Gamma" (at level 200, no associativity, Gamma at level 1).
Reserved Notation "'gate' g 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'duty' d 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'archbehavior' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'behavior' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'assertion' a 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'protocol' p 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'connection' c 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'body' b 'well' 'typed' 'in' Gamma Pi" (at level 200, Gamma at level 1, Pi at level 1, no associativity).


(**
 * Functions building environments
 *)

Definition env_add_params  :=
  List.fold_left (fun e f => e[AST.name_of_formalParameter f <- EVariable (AST.type_of_formalParameter f)]).

Definition env_of_params p := env_add_params p empty.

Definition env_add_types :=
  List.fold_left (fun e d => e[AST.name_of_datatypeDecl d <- EType d]).

Definition build_type_env p := env_add_types p empty.

Definition conns_environment l :=
  List.fold_left (fun e c => e[AST.name_of_connection c <- GDConnection (AST.mode_of_connection c) (AST.datatype_of_connection c)]) l empty.

Definition build_gate_env g :=
  match g with
    | AST.GateDecl _ l _ => conns_environment l
  end.

Definition build_duty_env d :=
  match d with
    | AST.DutyDecl _ l _ _ => conns_environment l
  end.

(**
 * Few additional utilities
 *)

Notation "'method' m 'defined' 'in' d 'with' 'parameters' f 'returns' r" :=
  (List.Exists (fun fd => AST.name_of_functionDecl fd = m
                         /\ AST.parameters_of_functionDecl fd = f
                         /\ AST.type_of_functionDecl fd = r)
               (AST.functions_of_datatypeDecl d))
    (at level 200, no associativity).

Inductive field_has_type: list AST.fieldDecl -> string -> AST.datatype -> Prop :=
| First_Field: forall n t r, field_has_type (AST.FieldDecl n t :: r) n t
| Next_Field: forall n t h r, field_has_type r n t -> field_has_type (h :: r) n t.

(**
 * The type system
 *)

Local Open Scope list_scope.

(**
In the below rules, each inductive type gathers the rules for a single
form of judgment. Rules are built of the following:
- a rule name, here used as the name of the constructor in the inductive type;
- universal quantification of the free names of the rules;
- premises of the rule appear above the [->] operator, connected by the conjunction [/\] operator; and
- conclusion of the rule appear below the [->] operator.
 *)

(**
 ** SoS architecture

%\todo{The import list is currently ignored.}%
 *)

Inductive type_sosADL: AST.sosADL -> Prop :=
| type_SosADL:
    forall i d,
      unit d well typed
      ->
      SoSADL (AST.SosADL i d) well typed

(**
 ** Compilation unit

%\note{These rules are missing in the Word document. The Word document is made as if the compilation unit and the architecture were the same.}%
 *)

with type_unit: AST.unit -> Prop :=
| type_SoS:
    forall n e,
      entity e well typed in empty
      ->
      unit (AST.SoS n e) well typed

| type_Library:
    forall n e,
      entity e well typed in empty
      ->
      unit (AST.Library n e) well typed

(** ** Entity *)

(**
%\note{Choice: the order of appearance is significant for the typing, i.e., a name can only be used after its declaration.}%
*)

with type_entityBlock: env -> AST.entityBlock -> Prop :=
| type_EntityBlock_datatype:
    forall Gamma d l funs systems mediators architectures,
      (typedecl d well typed in Gamma)
      /\ (entity (AST.EntityBlock l funs systems mediators architectures) well typed in Gamma[AST.name_of_datatypeDecl d <- EType d])
      ->
      entity (AST.EntityBlock (d::l) funs systems mediators architectures) well typed in Gamma

| type_EntityBlock_function:
    forall Gamma f l systems mediators architectures,
      (function f well typed in Gamma)
      /\ (entity (AST.EntityBlock nil l systems mediators architectures) well typed in Gamma[AST.name_of_functionDecl f <- EFunction f])
      ->
      entity (AST.EntityBlock nil (f::l) systems mediators architectures) well typed in Gamma

| type_EntityBlock_system:
    forall Gamma s l mediators architectures,
      (system s well typed in Gamma)
      /\ (entity (AST.EntityBlock nil nil l mediators architectures) well typed in Gamma[AST.name_of_systemDecl s <- ESystem])
      ->
      entity (AST.EntityBlock nil nil (s::l) mediators architectures) well typed in Gamma

| type_EntityBlock_mediator:
    forall Gamma m l architectures,
      (mediator m well typed in Gamma)
      /\ (entity (AST.EntityBlock nil nil nil l architectures) well typed in Gamma[AST.name_of_mediatorDecl m <- EMediator])
      ->
      entity (AST.EntityBlock nil nil nil (m::l) architectures) well typed in Gamma

| type_EntityBlock_architecture:
    forall Gamma a l,
      (architecture a well typed in Gamma)
      /\ (entity (AST.EntityBlock nil nil nil nil l) well typed in Gamma[AST.name_of_architectureDecl a <- EArchitecture])
      ->
      entity (AST.EntityBlock nil nil nil nil (a::l)) well typed in Gamma

(** ** Data type declaration *)
with type_datatypeDecl: env -> AST.datatypeDecl -> Prop :=
| type_DataTypeDecl:
    forall Gamma name t funs,
      (type t well typed in Gamma)
      /\ (functions of typedecl funs well typed in Gamma[name <- EType (AST.DataTypeDecl name t funs)])
      ->
      typedecl (AST.DataTypeDecl name t funs) well typed in Gamma

with type_datatypeDecl_functions: env -> list AST.functionDecl -> Prop :=
| type_datatypeDecl_empty:
    forall Gamma, functions of typedecl nil well typed in Gamma

| type_datatypeDecl_f:
    forall Gamma f l,
      (function f well typed in Gamma)
      /\ (functions of typedecl l well typed in Gamma)
      ->
      functions of typedecl (f::l) well typed in Gamma
                                 
(**
 ** Function declaration

%\note{In the Word document, the \coqdocconstr{FunctionDecl} constructor is erroneously considered being parametered by the type declaration. In fact, the type is referred to by its name. Hence the \ensuremath{\Delta} environment shall be used to retrieve the named type, and this type need not be checked (again).}%
 *)

with type_function: env -> AST.functionDecl -> Prop :=
| type_FunctionDecl:
    forall Gamma name dataName dataTypeName params t vals e tau dataType,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Gamma)
      /\ (expression e under vals has type tau in (env_add_params params Gamma))
      /\  contains Gamma dataTypeName (EType dataType)
      /\ tau < AST.datatype_of_datatypeDecl dataType
      ->
      function (AST.FunctionDecl name dataName dataTypeName params t vals e) well typed in Gamma

(**
 ** System

%\note{The types of formal parameters are independant of preceding parameters. For instance, {\tt system S(x: integer, y: integer\{x-1 .. x+1\})} is not allowed.}%

%\note{Unlike the Word document, the rule applies in the context of environments $\Delta$ $\Phi$.}%

%\note{Choice: the elements declared within a system are typed in order, and the environment is enriched incrementally. Cons: prevents no mutually recursive definition.}%
 *)

with type_system: env -> AST.systemDecl -> Prop :=
| type_SystemDecl:
    forall Gamma name params datatypes gates bhv assrt,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Gamma)
      /\ (systemblock (AST.SystemDecl name nil datatypes gates bhv assrt) well typed in (env_add_params params Gamma))
      ->
      system (AST.SystemDecl name params datatypes gates bhv assrt) well typed in Gamma

with type_systemblock: env -> AST.systemDecl -> Prop :=
| type_SystemDecl_datatype:
    forall Gamma name d l gates bhv assrt,
      (typedecl d well typed in Gamma)
      /\ (systemblock (AST.SystemDecl name nil l gates bhv assrt) well typed in Gamma[AST.name_of_datatypeDecl d <- EType d])
      ->
      systemblock (AST.SystemDecl name nil (d::l) gates bhv assrt) well typed in Gamma

| type_SystemDecl_gate:
    forall Gamma name g l bhv assrt,
      (gate g well typed in Gamma)
      /\ (systemblock (AST.SystemDecl name nil nil l bhv assrt) well typed in Gamma[AST.name_of_gateDecl g <- EGateOrDuty (build_gate_env g)])
      ->
      systemblock (AST.SystemDecl name nil nil (g::l) bhv assrt) well typed in Gamma

| type_SystemDecl_Some_Assertion:
    forall Gamma name bhv assrt,
      (behavior bhv well typed in Gamma)
      /\ (assertion assrt well typed in Gamma)
      ->
      systemblock (AST.SystemDecl name nil nil nil bhv (Some assrt)) well typed in Gamma

(**
%\note{The Word document lacks the case where no assertion is provided.}%
*)

| type_SystemDecl_None:
    forall Gamma name bhv,
      (behavior bhv well typed in Gamma)
      ->
      systemblock (AST.SystemDecl name nil nil nil bhv None) well typed in Gamma


(**
 ** Mediator
 *)

with type_mediator: env -> AST.mediatorDecl -> Prop :=
| type_MediatorDecl:
    forall Gamma name params datatypes duties b,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Gamma)
        /\ (mediatorblock (AST.MediatorDecl name nil datatypes duties b) well typed in (env_add_params params Gamma))
      ->
      mediator (AST.MediatorDecl name params datatypes duties b) well typed in Gamma

with type_mediatorblock: env -> AST.mediatorDecl -> Prop :=
| type_MediatorDecl_datatype:
    forall Gamma name d l duties bhv,
      (typedecl d well typed in Gamma)
      /\ (mediatorblock (AST.MediatorDecl name nil l duties bhv) well typed in Gamma[AST.name_of_datatypeDecl d <- EType d])
      ->
      mediatorblock (AST.MediatorDecl name nil (d::l) duties bhv) well typed in Gamma

| type_MediatorDecl_duty:
    forall Gamma name d l bhv,
      (duty d well typed in Gamma)
      /\ (mediatorblock (AST.MediatorDecl name nil nil l bhv) well typed in Gamma[AST.name_of_dutyDecl d <- EGateOrDuty (build_duty_env d)])
      ->
      mediatorblock (AST.MediatorDecl name nil nil (d::l) bhv) well typed in Gamma

| type_MediatorDecl_Behavior:
    forall Gamma name bhv,
      (behavior bhv well typed in Gamma)
      ->
      mediatorblock (AST.MediatorDecl name nil nil nil bhv) well typed in Gamma

(**
 ** Architecture

 *)

with type_architecture: env -> AST.architectureDecl -> Prop :=
| type_ArchitectureDecl:
    forall Gamma name params datatypes gates b a,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Gamma)
      /\ (architectureblock (AST.ArchitectureDecl name nil datatypes gates b a) well typed in (env_add_params params Gamma))
      ->
      architecture (AST.ArchitectureDecl name params datatypes gates b a) well typed in Gamma

with type_architectureblock: env -> AST.architectureDecl -> Prop :=
| type_ArchitectureDecl_datatype:
    forall Gamma name d l gates bhv a,
      (typedecl d well typed in Gamma)
      /\ (architectureblock (AST.ArchitectureDecl name nil l gates bhv a) well typed in Gamma[AST.name_of_datatypeDecl d <- EType d])
      ->
      architectureblock (AST.ArchitectureDecl name nil (d::l) gates bhv a) well typed in Gamma

| type_ArchitectureDecl_gate:
    forall Gamma name g l bhv a,
      (gate g well typed in Gamma)
      /\ (architectureblock (AST.ArchitectureDecl name nil nil l bhv a) well typed in Gamma[AST.name_of_gateDecl g <- EGateOrDuty (build_gate_env g)])
      ->
      architectureblock (AST.ArchitectureDecl name nil nil (g::l) bhv a) well typed in Gamma

| type_ArchitectureDecl_behavior:
    forall Gamma name bhv a,
      (archbehavior bhv well typed in Gamma)
      /\ (assertion a well typed in Gamma)
      ->
      architectureblock (AST.ArchitectureDecl name nil nil nil bhv a) well typed in Gamma



(**
 ** Data types

%\note{\coqdocconstr{IntegerType} and \coqdocconstr{ConnectionType} are removed from the abstract language.}%
 *)

with type_datatype: env -> AST.datatype -> Prop :=
| type_NamedType:
    forall Gamma n t,
      contains Gamma n (EType t)
      ->
      type (AST.NamedType n) well typed in Gamma

| type_TupleType:
    forall Gamma fields,
      (values (AST.name_of_fieldDecl f) for f of fields are distinct)
      /\ (for each f of fields,
         type (AST.type_of_fieldDecl f) well typed in Gamma)
      ->
      type (AST.TupleType fields) well typed in Gamma

| type_SequenceType:
    forall Gamma t,
      type t well typed in Gamma
      ->
      type (AST.SequenceType t) well typed in Gamma

(**
%\note{In comparison to the Word document, the order condition on the range boundaries is added, using some interpretation system (to be defined); boundaries are assumed to be \coqdocconstr{RangeType}.}%
 *)

| type_RangeType:
    forall Gamma min max min__min min__max max__min max__max,
      (expression min has type (AST.RangeType min__min min__max) in Gamma)
      /\ (expression max has type (AST.RangeType max__min max__max) in Gamma)
      /\ min <= max
      ->
      type (AST.RangeType min max) well typed in Gamma

(**
 ** Expression
 *)

with type_expression: env -> AST.expression -> AST.datatype -> Prop :=
| type_expression_IntegerValue:
    forall Gamma v,
      expression (AST.IntegerValue v) has type (AST.RangeType (AST.IntegerValue v) (AST.IntegerValue v)) in Gamma

| type_expression_Any:
    forall Gamma tau,
      expression AST.Any has type tau in Gamma

| type_expression_Opposite:
    forall Gamma e v__min v__max,
      (expression e has type (AST.RangeType v__min v__max) in Gamma)
      ->
      expression (AST.UnaryExpression "-" e) has type (AST.RangeType (AST.UnaryExpression "-" v__max) (AST.UnaryExpression "-" v__min)) in Gamma

| type_expression_Same:
    forall Gamma e v__min v__max,
      (expression e has type (AST.RangeType v__min v__max) in Gamma)
      ->
      expression (AST.UnaryExpression "+" e) has type (AST.RangeType v__min v__max) in Gamma

| type_expression_Not:
    forall Gamma e,
      (expression e has type AST.BooleanType in Gamma)
      ->
      expression (AST.UnaryExpression "not" e) has type AST.BooleanType in Gamma

| type_expression_Add:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType l__min l__max) in Gamma)
      /\ (expression r has type (AST.RangeType r__min r__max) in Gamma)
      ->
      expression (AST.BinaryExpression l "+" r) has type (AST.RangeType (AST.BinaryExpression l__min "+" r__min) (AST.BinaryExpression l__max "+" r__max)) in Gamma

| type_expression_Sub:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType l__min l__max) in Gamma)
      /\ (expression r has type (AST.RangeType r__min r__max) in Gamma)
      ->
      expression (AST.BinaryExpression l "-" r) has type (AST.RangeType (AST.BinaryExpression l__min "-" r__max) (AST.BinaryExpression l__max "-" r__min)) in Gamma

(** %\todo{mul, div and mod}% *)

| type_expression_Implies:
   forall Gamma l r,
     (expression l has type AST.BooleanType in Gamma)
     /\ (expression r has type AST.BooleanType in Gamma)
     ->
     expression (AST.BinaryExpression l "implies" r) has type AST.BooleanType in Gamma

| type_expression_Or:
   forall Gamma l r,
     (expression l has type AST.BooleanType in Gamma)
     /\ (expression r has type AST.BooleanType in Gamma)
     ->
     expression (AST.BinaryExpression l "or" r) has type AST.BooleanType in Gamma

| type_expression_Xor:
   forall Gamma l r,
     (expression l has type AST.BooleanType in Gamma)
     /\ (expression r has type AST.BooleanType in Gamma)
     ->
     expression (AST.BinaryExpression l "xor" r) has type AST.BooleanType in Gamma

| type_expression_And:
   forall Gamma l r,
     (expression l has type AST.BooleanType in Gamma)
     /\ (expression r has type AST.BooleanType in Gamma)
     ->
     expression (AST.BinaryExpression l "and" r) has type AST.BooleanType in Gamma

| type_expression_Equal:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType l__min l__max) in Gamma)
      /\ (expression r has type (AST.RangeType r__min r__max) in Gamma)
      ->
      expression (AST.BinaryExpression l "=" r) has type AST.BooleanType in Gamma

| type_expression_Diff:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType l__min l__max) in Gamma)
      /\ (expression r has type (AST.RangeType r__min r__max) in Gamma)
      ->
      expression (AST.BinaryExpression l "<>" r) has type AST.BooleanType in Gamma

| type_expression_Lt:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType l__min l__max) in Gamma)
      /\ (expression r has type (AST.RangeType r__min r__max) in Gamma)
      ->
      expression (AST.BinaryExpression l "<" r) has type AST.BooleanType in Gamma

| type_expression_Le:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType l__min l__max) in Gamma)
      /\ (expression r has type (AST.RangeType r__min r__max) in Gamma)
      ->
      expression (AST.BinaryExpression l "<=" r) has type AST.BooleanType in Gamma

| type_expression_Gt:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType l__min l__max) in Gamma)
      /\ (expression r has type (AST.RangeType r__min r__max) in Gamma)
      ->
      expression (AST.BinaryExpression l ">" r) has type AST.BooleanType in Gamma

| type_expression_Ge:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType l__min l__max) in Gamma)
      /\ (expression r has type (AST.RangeType r__min r__max) in Gamma)
      ->
      expression (AST.BinaryExpression l ">=" r) has type AST.BooleanType in Gamma

| type_expression_Ident:
    forall Gamma x tau,
      (contains Gamma x (EVariable tau))
      ->
      expression (AST.IdentExpression x) has type tau in Gamma

(** %\note{Assume that the type of this is a named type}% *)
| type_expression_MethodCall:
    forall Gamma this tau tauDecl name formalparams params ret,
      (expression this has type (AST.NamedType tau) in Gamma)
      /\ (contains Gamma tau (EType tauDecl))
      /\ (method name defined in tauDecl with parameters formalparams returns ret)
      /\ (for each fp p of formalparams params,
         expression p has type (AST.type_of_formalParameter fp) in Gamma)
      ->
      expression (AST.MethodCall this name params) has type ret in Gamma

| type_expression_Tuple:
    forall Gamma elts typ,
      (values (AST.name_of_tupleElement x) for x of elts are distinct)
      /\ (for each e tau of elts typ, AST.name_of_tupleElement e = AST.name_of_fieldDecl tau)
      /\ (for each e tau of elts typ,
         expression (AST.expression_of_tupleElement e) has type (AST.type_of_fieldDecl tau) in Gamma)
      ->
      expression (AST.Tuple elts) has type (AST.TupleType typ) in Gamma

| type_expression_Sequence:
    forall Gamma elts tau,
      (for each e of elts, expression e has type tau in Gamma)
      ->
      expression (AST.Sequence elts) has type (AST.SequenceType tau) in Gamma

| type_expression_Map:
    forall Gamma coll tau x e tau__e,
      (expression coll has type (AST.SequenceType tau) in Gamma)
      /\ (expression e has type tau__e in Gamma[x <- EVariable tau])
      ->
      expression (AST.Map coll x e) has type (AST.SequenceType tau__e) in Gamma

| type_expression_Select:
    forall Gamma coll tau x e,
      (expression coll has type (AST.SequenceType tau) in Gamma)
      /\ (expression e has type AST.BooleanType in Gamma[x <- EVariable tau])
      ->
      expression (AST.Select coll x e) has type (AST.SequenceType tau) in Gamma

| type_expression_Field:
    forall Gamma this tau name tau__f,
      (expression this has type (AST.TupleType tau) in Gamma)
      /\ field_has_type tau name tau__f
      ->
      expression (AST.Field this name) has type tau__f in Gamma

(** %\todo{CallExpression}% *)

(** %\todo{What is the type of unobservable?}% *)

(** %\todo{Relay, Unify and Quantify}% *)

(** ** Expression in the scope of a list of valuings *)
with type_expression_where: env -> list AST.valuing -> AST.expression -> AST.datatype -> Prop :=
| type_expression_where_empty:
    forall Gamma e tau,
      (expression e has type tau in Gamma)
      ->
      expression e under nil has type tau in Gamma

| type_expression_where_Valuing_None:
    forall Gamma e tau x x__e x__tau v,
      (expression x__e has type x__tau in Gamma)
      /\ (expression e under v has type tau in Gamma[x <- EVariable x__tau])
      ->
      expression e under (AST.Valuing x None x__e :: v) has type tau in Gamma

| type_expression_where_Valuing_Some:
    forall Gamma e tau x x__t x__e x__tau v,
      (expression x__e has type x__tau in Gamma)
      /\ x__tau < x__t
      /\ (expression e under v has type tau in Gamma[x <- EVariable x__t])
      ->
      expression e under (AST.Valuing x (Some x__t) x__e :: v) has type tau in Gamma


(**
 ** Gate
 *)

with type_gate: env -> AST.gateDecl -> Prop :=
| type_GateDecl:
    forall Gamma name conns p,
      (protocol p well typed in Gamma)
      /\ (for each c of conns, connection c well typed in Gamma)
      ->
      gate (AST.GateDecl name conns p) well typed in Gamma


(**
 ** Duty
 *)

with type_duty: env -> AST.dutyDecl -> Prop :=
| type_DutyDecl:
    forall Gamma name conns a p,
      (protocol p well typed in Gamma)
      /\ (for each c of conns, connection c well typed in Gamma)
      /\ (assertion a well typed in Gamma)
      ->
      duty (AST.DutyDecl name conns a p) well typed in Gamma

(**
 ** Architecture behavior

%\todo{}%
 *)

with type_archbehavior: env ->  AST.archBehaviorDecl -> Prop :=

(**
 ** Behavior
 *)

with type_behavior: env -> AST.behaviorDecl -> Prop :=
| type_BehaviorDecl:
    forall Gamma name params b,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Gamma)
      /\ (body b well typed in (env_add_params params Gamma) (List.map AST.type_of_formalParameter params))
      ->
      behavior (AST.BehaviorDecl name params (AST.Behavior b)) well typed in Gamma

(**
 ** Assertion

%\todo{}%
 *)

with type_assertion: env -> AST.assertionDecl -> Prop :=

(**
 ** Protocol

%\todo{}%
 *)

with type_protocol: env -> AST.protocolDecl -> Prop :=

(**
 ** Connection

%\note{The rule is quite different from the one of the Word document, which was actually incorrect. Indeed, the name of the connection must not be added to the environment since connection names are not first class names.}%
 *)

with type_connection: env -> AST.connection -> Prop :=
| type_Connection:
    forall Gamma name k m t,
      (type t well typed in Gamma)
      ->
      connection (AST.Connection name k m t) well typed in Gamma

(**
 ** Body

%\note{According to the Word document, it's not clear whether the type system enforces some rules on the sequence of statements. For instance, {\tt repeat} is enforced as the latest statement of a body; but no check that all the branches terminate with {\tt done} or recursive call.}%

Pi denotes the types of the parameters of the behavior, in order to type recursive calls.

*)
with type_body: env -> list AST.datatype -> list AST.statement -> Prop :=
| type_EmptyBody:
    forall Gamma Pi,
      body nil well typed in Gamma Pi

| type_Repeat:
    forall Gamma Pi b,
      (body b well typed in Gamma Pi)
      ->
      body (AST.RepeatBehavior (AST.Behavior b) :: nil) well typed in Gamma Pi

| type_Choose:
    forall Gamma Pi branches,
      (for each b of branches, body (AST.body_of_behavior b) well typed in Gamma Pi)
      ->
      body (AST.ChooseBehavior branches :: nil) well typed in Gamma Pi

| type_IfThen:
    forall Gamma Pi c t l,
      (expression c has type AST.BooleanType in Gamma)
      /\ (body t well typed in Gamma Pi)
      /\ (body l well typed in Gamma Pi)
      ->
      body (AST.IfThenElseBehavior c (AST.Behavior t) None :: l) well typed in Gamma Pi

(** %\note{unlike the Word document, {\tt IfThenElse} is not enforced as the last statement.}%

 *)
| type_IfThenElse:
    forall Gamma Pi c t e l,
      (expression c has type AST.BooleanType in Gamma)
      /\ (body t well typed in Gamma Pi)
      /\ (body e well typed in Gamma Pi)
      /\ (body l well typed in Gamma Pi)
      ->
      body (AST.IfThenElseBehavior c (AST.Behavior t) (Some (AST.Behavior e)) :: l) well typed in Gamma Pi

| type_ForEach:
    forall Gamma Pi x tau vals b l,
      (expression vals has type (AST.SequenceType tau) in Gamma)
      /\ (body b well typed in Gamma[x <- EVariable tau ] Pi)
      /\ (body l well typed in Gamma Pi)
      ->
      body (AST.ForEachBehavior x vals (AST.Behavior b) :: l) well typed in Gamma Pi

| type_RecursiveCall:
    forall Gamma Pi params,
      (for each tau__pi p of Pi params, exists tau, expression p has type tau in Gamma /\ tau < tau__pi)
      ->
      body (AST.RecursiveCall params :: nil) well typed in Gamma Pi

(** %\note{I guess that in the Word document, the {\tt Behavior(Assert)} rule is in fact {\tt Behavior(Tell)}.}% *)
| type_TellStatement:
    forall Gamma Pi name e l,
      (expression e has type AST.BooleanType in Gamma)
      /\ (body l well typed in Gamma Pi)
      ->
      body (AST.AssertStatement (AST.Tell name e) :: l) well typed in Gamma Pi

(** %\note{The idea here is to assume an environment%[ee]% in which all the (free) names of%[e]% are bound to some type; then to type %[e]% as well as the following statements in %[ee]% merged in %[Gamma]%.}% *)
| type_AskStatement:
    forall Gamma Pi name e ee l,
      (forall x, List.In x (AST.names_of_expression e) <-> exists tau, contains ee x (EType tau))
      /\ (expression e has type AST.BooleanType in (Gamma <++ ee))
      /\ (body l well typed in (Gamma <++ ee) Pi)
      ->
      body (AST.AssertStatement (AST.Ask name e) :: l) well typed in Gamma Pi

(**
%\note{Assume that the complexnames can only be formed like this: {\tt gate::conn} or {\tt duty::conn}. The following assumes this statement.}%
*)

| type_ReceiveStatement_In:
    forall Gamma Pi gd E conn x conn__tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection AST.In conn__tau))
      /\ (body l well typed in Gamma[x <- EVariable conn__tau] Pi)
      ->
      body (AST.ActionStatement (AST.Action (gd :: conn :: nil) (AST.ReceiveAction x)) :: l) well typed in Gamma Pi


| type_ReceiveStatement_InOut:
    forall Gamma Pi gd E conn x conn__tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection AST.InOut conn__tau))
      /\ (body l well typed in Gamma[x <- EVariable conn__tau] Pi)
      ->
      body (AST.ActionStatement (AST.Action (gd :: conn :: nil) (AST.ReceiveAction x)) :: l) well typed in Gamma Pi

| type_SendStatement_Out:
    forall Gamma Pi gd E conn conn__tau e tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection AST.Out conn__tau))
      /\ (expression e has type tau in Gamma)
      /\ (tau < conn__tau)
      /\ (body l well typed in Gamma Pi)
      ->
      body (AST.ActionStatement (AST.Action (gd :: conn :: nil) (AST.SendAction e)) :: l) well typed in Gamma Pi

| type_SendStatement_InOut:
    forall Gamma Pi gd E conn conn__tau e tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection AST.InOut conn__tau))
      /\ (expression e has type tau in Gamma)
      /\ (tau < conn__tau)
      /\ (body l well typed in Gamma Pi)
      ->
      body (AST.ActionStatement (AST.Action (gd :: conn :: nil) (AST.SendAction e)) :: l) well typed in Gamma Pi

| type_DoExpr:
    forall Gamma Pi e tau l,
      (expression e has type tau in Gamma)
      /\ (body l well typed in Gamma Pi)
      ->
      body (AST.DoExpr e :: l) well typed in Gamma Pi

| type_Done:
    forall Gamma Pi,
      body (AST.Done :: nil) well typed in Gamma Pi


(** ** Notations *)
where "'SoSADL' a 'well' 'typed'" := (type_sosADL a)
and "'unit' u 'well' 'typed'" := (type_unit u)
and "'entity' u 'well' 'typed' 'in' Gamma" := (type_entityBlock Gamma u)
and "'typedecl' t 'well' 'typed' 'in' Gamma" := (type_datatypeDecl Gamma t)
and "'functions' 'of' 'typedecl' t 'well' 'typed' 'in' Gamma" := (type_datatypeDecl_functions Gamma t)
and "'function' f 'well' 'typed' 'in' Gamma" := (type_function Gamma f)
and "'type' t 'well' 'typed' 'in' Gamma" := (type_datatype Gamma t)
and "'system' s 'well' 'typed' 'in' Gamma" := (type_system Gamma s)
and "'systemblock' s 'well' 'typed' 'in' Gamma" := (type_systemblock Gamma s)
and "'mediator' m 'well' 'typed' 'in' Gamma" := (type_mediator Gamma m)
and "'mediatorblock' m 'well' 'typed' 'in' Gamma" := (type_mediatorblock Gamma m)
and "'architecture' a 'well' 'typed' 'in' Gamma" := (type_architecture Gamma a)
and "'architectureblock' a 'well' 'typed' 'in' Gamma" := (type_architectureblock Gamma a)
and "'expression' e 'has' 'type' t 'in' Gamma" := (type_expression Gamma e t)
and "'expression' e 'under' v 'has' 'type' t 'in' Gamma" := (type_expression_where Gamma v e t)
and "'gate' g 'well' 'typed' 'in' Gamma" := (type_gate Gamma g)
and "'duty' d 'well' 'typed' 'in' Gamma" := (type_duty Gamma d)
and "'archbehavior' b 'well' 'typed' 'in' Gamma" := (type_archbehavior Gamma b)
and "'behavior' b 'well' 'typed' 'in' Gamma" := (type_behavior Gamma b)
and "'assertion' a 'well' 'typed' 'in' Gamma" := (type_assertion Gamma a)
and "'protocol' p 'well' 'typed' 'in' Gamma" := (type_protocol Gamma p)
and "'connection' c 'well' 'typed' 'in' Gamma" := (type_connection Gamma c)
and "'body' b 'well' 'typed' 'in' Gamma Pi" := (type_body Gamma Pi b)
.
