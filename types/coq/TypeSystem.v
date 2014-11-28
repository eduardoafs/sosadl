Require Import List.
Require Import String.
Require SosADL.
Require Import Environment.
Require Import Utils.
Require Import SubTyping.
Require Import Interpretation.

Module AST := SosADL.

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
 * Environment
 *)

(**
 ** Gates and duties

For gates and duties, a secondary map is stored in the
environment. This map lists the connections of the gate or of the
duty.

%\note{%The kind of connection (normal or environment) is not used.%}%

 *)

Inductive gd_env_content: Set :=
| GDConnection: AST.ModeType -> AST.t_DataType -> gd_env_content.

(**
 ** Objects in [Gamma], the main environment

We choose to have a single environment for all the kinds of objects,
hence to have a single namespace. The following type describes all the
objects that can be stored in the typing environment. The main kinds of objects are:

- [EType]: data type declaration
- [EGateOrDuty]: list of connections for a gate or a duty
- [EVariable]: value-storing variable

 *)

Inductive env_content: Set :=
| EType: AST.t_DataTypeDecl -> env_content
| EFunction: AST.t_FunctionDecl -> env_content
| ESystem: env_content
| EMediator: env_content
| EArchitecture: env_content
| EGateOrDuty: environment gd_env_content -> env_content
| EVariable: AST.t_DataType -> env_content.

Definition env := environment env_content.


(**
 ** Utility functions
 *)

(** [env_add_params] adds a list of formal parameters to an
environment.  *)

Definition env_add_params  :=
  List.fold_left
    (fun e f =>
       match AST.FormalParameter_name f with
         | Some name =>
           match AST.FormalParameter_type f with
             | Some type => e[name <- EVariable type]
             | None => e
           end
         | None => e
       end).

(** [conns_environment] builds an environment containing connections,
from a list of these connections. *)

Definition conns_environment l :=
  List.fold_left
    (fun e c =>
       match AST.Connection_name c with
         | Some name =>
           match AST.Connection_mode c with
             | Some mode =>
               match AST.Connection_valueType c with
                 | Some type => e[name <- GDConnection mode type]
                 | None => e
               end
             | None => e
           end
         | None => e
       end)
    l empty.

(** [build_gate_env] builds the secondary environment for a gate
declaration. *)

Definition build_gate_env g :=
  conns_environment (AST.GateDecl_connections g).

(** [build_duty_env] builds the secondary environment for a duty
declaration. *)

Definition build_duty_env d :=
  conns_environment (AST.DutyDecl_connections d).

(**
 * Utilities
 *)

(** The following notations is a shortcut to look for a method in a
data type declaration.  *)

Notation "'method' m 'defined' 'in' d 'with' 'parameters' f 'returns' r" :=
  (List.Exists (fun fd => AST.FunctionDecl_name fd = Some m
                         /\ AST.FunctionDecl_parameters fd = f
                         /\ AST.FunctionDecl_type fd = Some r)
               (AST.DataTypeDecl_functions d))
    (at level 200, no associativity).

(** [field_has_type] is a predicate to look for a field in a list of
field declarations. *)

Inductive field_has_type: list AST.t_FieldDecl -> string -> AST.t_DataType -> Prop :=
| First_Field: forall n t r, field_has_type (AST.FieldDecl (Some n) (Some t) :: r) n t
| Next_Field: forall n t h r, field_has_type r n t -> field_has_type (h :: r) n t.

Hypothesis names_of_expression: AST.t_Expression -> list string.

(**
 * Notations

The following notations defines all the judgment forms in the type
system. Usually, the typing environment is denoted [Gamma].

The judgement for statements ([body]) has a second environment denoted
[Pi], holding the types of the formal parameters of the enclosing
behavior. This second environment [Pi] is mandatory to type the
recursive call statement.

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
Reserved Notation "'body' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).

(**
 * The type system
 *)

Local Open Scope list_scope.
Local Open Scope string_scope.

(** In the following rules, each inductive type gathers the rules for
a single form of judgment. Rules are built of the following:

- a rule name, here used as the name of the constructor in the inductive type;
- universal quantification of the free names of the rules;
- premises of the rule appear above the [->] operator, connected by the conjunction [/\] operator; and
- conclusion of the rule appear below the [->] operator.
 *)

(**
 ** SoS architecture

%\todo{%The import list is currently ignored.%}%
 *)

Inductive type_sosADL: AST.t_SosADL -> Prop :=
| type_SosADL:
    forall i d,
      unit d well typed
      ->
      SoSADL (AST.SosADL i (Some d)) well typed

(**
 ** Compilation unit

The two forms of compulation unit (SoS or library) are handled in the
same way by the typing rules.  *)

with type_unit: AST.t_Unit -> Prop :=
| type_SoS:
    forall n e,
      entity e well typed in empty
      ->
      unit (AST.SoS (Some n) (Some e)) well typed

| type_Library:
    forall n e,
      entity e well typed in empty
      ->
      unit (AST.Library (Some n) (Some e)) well typed

(** ** Entity *)

(** %\note{%We choose that the order of the declaration is
signification for the typing rules. Namely, the scope of a declaration
starts after this declaration and spans until the end of the enclosing
block. This choice prevents, e.g., (mutually) recursive
declarations. This behavior is implemented by the following rules,
each of which exhausts of list of declarations in order.%}% *)

with type_entityBlock: env -> AST.t_EntityBlock -> Prop :=
| type_EntityBlock_datatype:
    forall Gamma d d_name l funs systems mediators architectures,
      (typedecl d well typed in Gamma)
      /\ (AST.DataTypeDecl_name d = Some d_name)
      /\ (entity (AST.EntityBlock l funs systems mediators architectures)
                well typed in Gamma[d_name <- EType d])
      ->
      entity (AST.EntityBlock (d::l) funs systems mediators architectures)
             well typed in Gamma


(** %\todo{%This rule [type_EntityBlock_function] is clearly
incorrect. If the declaration adds a function (method) to a data type,
then the list of the methods of this data type should be updated,
under the precondition that the new one does not already exist in this
list. If the declaration adds a function, then there is no [this]
parameter in the function declaration, which is not supported by the
abstract syntax nor the concrete syntax.%}% *)

| type_EntityBlock_function:
    forall Gamma f f_name l systems mediators architectures,
      (function f well typed in Gamma)
      /\ (AST.FunctionDecl_name f = Some f_name)
      /\ (entity (AST.EntityBlock nil l systems mediators architectures)
                well typed in Gamma[f_name <- EFunction f])
      ->
      entity (AST.EntityBlock nil (f::l) systems mediators architectures)
             well typed in Gamma

| type_EntityBlock_system:
    forall Gamma s s_name l mediators architectures,
      (system s well typed in Gamma)
      /\ AST.SystemDecl_name s = Some s_name
      /\ (entity (AST.EntityBlock nil nil l mediators architectures)
                well typed in Gamma[s_name <- ESystem])
      ->
      entity (AST.EntityBlock nil nil (s::l) mediators architectures)
             well typed in Gamma

| type_EntityBlock_mediator:
    forall Gamma m m_name l architectures,
      (mediator m well typed in Gamma)
      /\ (AST.MediatorDecl_name m = Some m_name)
      /\ (entity (AST.EntityBlock nil nil nil l architectures)
                well typed in Gamma[m_name <- EMediator])
      ->
      entity (AST.EntityBlock nil nil nil (m::l) architectures)
             well typed in Gamma

| type_EntityBlock_architecture:
    forall Gamma a a_name l,
      (architecture a well typed in Gamma)
      /\ (AST.ArchitectureDecl_name a = Some a_name)
      /\ (entity (AST.EntityBlock nil nil nil nil l)
                well typed in Gamma[a_name <- EArchitecture])
      ->
      entity (AST.EntityBlock nil nil nil nil (a::l))
             well typed in Gamma

| type_EntityBlock:
    forall Gamma,
      entity (AST.EntityBlock nil nil nil nil nil) well typed in Gamma

(** ** Data type declaration *)

(** %\note{%The functions (methods) of the data type declaration can
be mutually recursive. Indeed, they are typed in an environment that
binds the data type declaration, including the list of functions
(methods).%}% *)

with type_datatypeDecl: env -> AST.t_DataTypeDecl -> Prop :=
| type_DataTypeDecl_Some:
    forall Gamma name t funs,
      (type t well typed in Gamma)
      /\ (values (AST.FunctionDecl_name x) for x of funs are distinct)
      /\ (functions of typedecl funs
                   well typed in Gamma[name <- EType (AST.DataTypeDecl (Some name) (Some t) funs)])
      ->
      typedecl (AST.DataTypeDecl (Some name) (Some t) funs) well typed in Gamma

| type_DataTypeDecl_None:
    forall Gamma name,
      typedecl (AST.DataTypeDecl (Some name) None nil) well typed in Gamma

(** %\note{%The functions (methods) of the data type declaration are
typed in order. In fact, this is not mandatory since the environment
remains the same while traversing the list of functions. The rule
might be simplified in this regard, using, e.g., [List.Forall].%}% *)

with type_datatypeDecl_functions: env -> list AST.t_FunctionDecl -> Prop :=
| type_datatypeDecl_empty:
    forall Gamma, functions of typedecl nil well typed in Gamma

| type_datatypeDecl_f:
    forall Gamma f l,
      (function f well typed in Gamma)
      /\ (functions of typedecl l well typed in Gamma)
      ->
      functions of typedecl (f::l) well typed in Gamma
                                 
(** ** Function declaration *)

with type_function: env -> AST.t_FunctionDecl -> Prop :=
| type_FunctionDecl:
    forall Gamma name dataName dataTypeName params t vals e tau dtname dttype dtfuns,
      (for each p of params, (exists t, AST.FormalParameter_type p = Some t /\ type t well typed in Gamma))
      /\ (expression e under vals has type tau in (env_add_params params Gamma))
      /\  contains Gamma dataTypeName (EType (AST.DataTypeDecl (Some dtname) (Some dttype) dtfuns))
      /\ tau < dttype
      ->
      function (AST.FunctionDecl (Some name) (Some dataName) (Some dataTypeName) params (Some t) vals (Some e))
               well typed in Gamma

(** ** System *)

(** %\note{%By choice, the elements declared in the system are typed
in order by the set rules for [type_systemblock].%}% *)

with type_system: env -> AST.t_SystemDecl -> Prop :=
| type_SystemDecl:
    forall Gamma name params datatypes gates bhv assrt,
      (for each p of params, (exists t, AST.FormalParameter_type p = Some t /\ type t well typed in Gamma))
      /\ (systemblock (AST.SystemDecl (Some name) nil datatypes gates (Some bhv) assrt)
                     well typed in (env_add_params params Gamma))
      ->
      system (AST.SystemDecl (Some name) params datatypes gates (Some bhv) assrt) well typed in Gamma

with type_systemblock: env -> AST.t_SystemDecl -> Prop :=
| type_SystemDecl_datatype:
    forall Gamma name d d_name l gates bhv assrt,
      (typedecl d well typed in Gamma)
      /\ (AST.DataTypeDecl_name d = Some d_name)
      /\ (systemblock (AST.SystemDecl (Some name) nil l gates (Some bhv) assrt)
                     well typed in Gamma[d_name <- EType d])
      ->
      systemblock (AST.SystemDecl (Some name) nil (d::l) gates (Some bhv) assrt)
                  well typed in Gamma

| type_SystemDecl_gate:
    forall Gamma name g g_name l bhv assrt,
      (gate g well typed in Gamma)
      /\ (AST.GateDecl_name g = Some g_name)
      /\ (systemblock (AST.SystemDecl (Some name) nil nil l (Some bhv) assrt)
                     well typed in Gamma[g_name <- EGateOrDuty (build_gate_env g)])
      ->
      systemblock (AST.SystemDecl (Some name) nil nil (g::l) (Some bhv) assrt) well typed in Gamma

| type_SystemDecl_Some_Assertion:
    forall Gamma name bhv assrt,
      (behavior bhv well typed in Gamma)
      /\ (assertion assrt well typed in Gamma)
      ->
      systemblock (AST.SystemDecl (Some name) nil nil nil (Some bhv) (Some assrt)) well typed in Gamma

| type_SystemDecl_None:
    forall Gamma name bhv,
      (behavior bhv well typed in Gamma)
      ->
      systemblock (AST.SystemDecl (Some name) nil nil nil (Some bhv) None) well typed in Gamma


(** ** Mediator *)

(** %\note{%By choice, the elements declared in the mediator are typed
in order by the set rules for [type_mediatorblock].%}% *)

with type_mediator: env -> AST.t_MediatorDecl -> Prop :=
| type_MediatorDecl:
    forall Gamma name params datatypes duties b assump assert,
      (for each p of params, (exists t, AST.FormalParameter_type p = Some t /\ type t well typed in Gamma))
        /\ (mediatorblock (AST.MediatorDecl (Some name) nil datatypes duties (Some b) assump assert)
                         well typed in (env_add_params params Gamma))
      ->
      mediator (AST.MediatorDecl (Some name) params datatypes duties (Some b) assump assert) well typed in Gamma

with type_mediatorblock: env -> AST.t_MediatorDecl -> Prop :=
| type_MediatorDecl_datatype:
    forall Gamma name d d_name l duties bhv assump assert,
      (typedecl d well typed in Gamma)
      /\ (AST.DataTypeDecl_name d = Some d_name)
      /\ (mediatorblock (AST.MediatorDecl (Some name) nil l duties (Some bhv) assump assert)
                       well typed in Gamma[d_name <- EType d])
      ->
      mediatorblock (AST.MediatorDecl (Some name) nil (d::l) duties (Some bhv) assump assert) well typed in Gamma

| type_MediatorDecl_duty:
    forall Gamma name d d_name l bhv assump assert,
      (duty d well typed in Gamma)
      /\ (AST.DutyDecl_name d = Some d_name)
      /\ (mediatorblock (AST.MediatorDecl (Some name) nil nil l (Some bhv) assump assert)
                       well typed in Gamma[d_name <- EGateOrDuty (build_duty_env d)])
      ->
      mediatorblock (AST.MediatorDecl (Some name) nil nil (d::l) (Some bhv) assump assert) well typed in Gamma

| type_MediatorDecl_Behavior:
    forall Gamma name bhv assump assert,
      (behavior bhv well typed in Gamma)
      ->
      mediatorblock (AST.MediatorDecl name nil nil nil (Some bhv) assump assert) well typed in Gamma

(** ** Architecture *)

(** %\note{%By choice, the elements declared in the architecture are
typed in order by the set rules for [type_architectureblock].%}% *)

with type_architecture: env -> AST.t_ArchitectureDecl -> Prop :=
| type_ArchitectureDecl:
    forall Gamma name params datatypes gates b a,
      (for each p of params, (exists t, AST.FormalParameter_type p = Some t /\ type t well typed in Gamma))
      /\ (architectureblock (AST.ArchitectureDecl (Some name) nil datatypes gates (Some b) a)
                           well typed in (env_add_params params Gamma))
      ->
      architecture (AST.ArchitectureDecl (Some name) params datatypes gates (Some b) a)
                   well typed in Gamma

with type_architectureblock: env -> AST.t_ArchitectureDecl -> Prop :=
| type_ArchitectureDecl_datatype:
    forall Gamma name d d_name l gates bhv a,
      (typedecl d well typed in Gamma)
      /\ (AST.DataTypeDecl_name d = Some d_name)
      /\ (architectureblock (AST.ArchitectureDecl (Some name) nil l gates (Some bhv) a)
                           well typed in Gamma[d_name <- EType d])
      ->
      architectureblock (AST.ArchitectureDecl (Some name) nil (d::l) gates (Some bhv) a)
                        well typed in Gamma

| type_ArchitectureDecl_gate:
    forall Gamma name g g_name l bhv a,
      (gate g well typed in Gamma)
      /\ (AST.GateDecl_name g = Some g_name)
      /\ (architectureblock (AST.ArchitectureDecl (Some name) nil nil l (Some bhv) a)
                           well typed in Gamma[g_name <- EGateOrDuty (build_gate_env g)])
      ->
      architectureblock (AST.ArchitectureDecl (Some name) nil nil (g::l) (Some bhv) a)
                        well typed in Gamma

| type_ArchitectureDecl_behavior:
    forall Gamma name bhv a,
      (archbehavior bhv well typed in Gamma)
      /\ (assertion a well typed in Gamma)
      ->
      architectureblock (AST.ArchitectureDecl (Some name) nil nil nil (Some bhv) (Some a)) well typed in Gamma



(** ** Data types *)

with type_datatype: env -> AST.t_DataType -> Prop :=
| type_NamedType:
    forall Gamma n t,
      contains Gamma n (EType t)
      ->
      type (AST.NamedType (Some n)) well typed in Gamma

| type_TupleType:
    forall Gamma fields,
      (values (AST.FieldDecl_name f) for f of fields are distinct)
      /\ (for each f of fields,
         (exists t, AST.FieldDecl_type f = Some t
               /\ type t well typed in Gamma))
      ->
      type (AST.TupleType fields) well typed in Gamma

| type_SequenceType:
    forall Gamma t,
      type t well typed in Gamma
      ->
      type (AST.SequenceType (Some t)) well typed in Gamma

| type_RangeType:
    forall Gamma min max min__min min__max max__min max__max,
      (expression min has type (AST.RangeType (Some min__min) (Some min__max)) in Gamma)
      /\ (expression max has type (AST.RangeType (Some max__min) (Some max__max)) in Gamma)
      /\ min <= max
      ->
      type (AST.RangeType (Some min) (Some max)) well typed in Gamma

(**
 ** Expression
 *)

with type_expression: env -> AST.t_Expression -> AST.t_DataType -> Prop :=
| type_expression_IntegerValue:
    forall Gamma v,
      expression (AST.IntegerValue (Some v))
      has type (AST.RangeType (Some (AST.IntegerValue (Some v)))
                              (Some (AST.IntegerValue (Some v)))) in Gamma

| type_expression_Any:
    forall Gamma tau,
      expression AST.Any has type tau in Gamma

| type_expression_Opposite:
    forall Gamma e min max,
      (expression e has type (AST.RangeType (Some min) (Some max)) in Gamma)
      ->
      expression (AST.UnaryExpression (Some "-") (Some e))
      has type (AST.RangeType (Some (AST.UnaryExpression (Some "-") (Some max)))
                              (Some (AST.UnaryExpression (Some "-") (Some min)))) in Gamma

| type_expression_Same:
    forall Gamma e min max,
      (expression e has type (AST.RangeType (Some min) (Some max)) in Gamma)
      ->
      expression (AST.UnaryExpression (Some "+") (Some e))
      has type (AST.RangeType (Some min) (Some max)) in Gamma

| type_expression_Not:
    forall Gamma e,
      (expression e has type AST.BooleanType in Gamma)
      ->
      expression (AST.UnaryExpression (Some "not") (Some e)) has type AST.BooleanType in Gamma

| type_expression_Add:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (AST.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (AST.BinaryExpression (Some l) (Some "+") (Some r))
      has type (AST.RangeType (Some (AST.BinaryExpression (Some l__min) (Some "+") (Some r__min)))
                              (Some (AST.BinaryExpression (Some l__max) (Some "+") (Some r__max)))) in Gamma

| type_expression_Sub:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (AST.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (AST.BinaryExpression (Some l) (Some "-") (Some r))
      has type (AST.RangeType (Some (AST.BinaryExpression (Some l__min) (Some "-") (Some r__max)))
                              (Some (AST.BinaryExpression (Some l__max) (Some "-") (Some r__min)))) in Gamma

(** %\todo{%The typing rules for [*], [/] and [mod] needs to be
written.%}% *)

| type_expression_Implies:
   forall Gamma l r,
     (expression l has type AST.BooleanType in Gamma)
     /\ (expression r has type AST.BooleanType in Gamma)
     ->
     expression (AST.BinaryExpression (Some l) (Some "implies") (Some r)) has type AST.BooleanType in Gamma

| type_expression_Or:
   forall Gamma l r,
     (expression l has type AST.BooleanType in Gamma)
     /\ (expression r has type AST.BooleanType in Gamma)
     ->
     expression (AST.BinaryExpression (Some l) (Some "or") (Some r)) has type AST.BooleanType in Gamma

| type_expression_Xor:
   forall Gamma l r,
     (expression l has type AST.BooleanType in Gamma)
     /\ (expression r has type AST.BooleanType in Gamma)
     ->
     expression (AST.BinaryExpression (Some l) (Some "xor") (Some r)) has type AST.BooleanType in Gamma

| type_expression_And:
   forall Gamma l r,
     (expression l has type AST.BooleanType in Gamma)
     /\ (expression r has type AST.BooleanType in Gamma)
     ->
     expression (AST.BinaryExpression (Some l) (Some "and") (Some r)) has type AST.BooleanType in Gamma

| type_expression_Equal:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (AST.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (AST.BinaryExpression (Some l) (Some "=") (Some r)) has type AST.BooleanType in Gamma

| type_expression_Diff:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (AST.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (AST.BinaryExpression (Some l) (Some "<>") (Some r)) has type AST.BooleanType in Gamma

| type_expression_Lt:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (AST.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (AST.BinaryExpression (Some l) (Some "<") (Some r)) has type AST.BooleanType in Gamma

| type_expression_Le:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (AST.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (AST.BinaryExpression (Some l) (Some "<=") (Some r)) has type AST.BooleanType in Gamma

| type_expression_Gt:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (AST.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (AST.BinaryExpression (Some l) (Some ">") (Some r)) has type AST.BooleanType in Gamma

| type_expression_Ge:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (AST.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (AST.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (AST.BinaryExpression (Some l) (Some ">=") (Some r)) has type AST.BooleanType in Gamma

| type_expression_Ident:
    forall Gamma x tau,
      (contains Gamma x (EVariable tau))
      ->
      expression (AST.IdentExpression (Some x)) has type tau in Gamma

(** %\note{%The rule [type_expression_MethodCall] assumes that the
type of the [this] parameter is a named type, hence refering to the
declaration of a data type containing some functions (methods).%}% *)

| type_expression_MethodCall:
    forall Gamma this tau tauDecl name formalparams params ret,
      (expression this has type (AST.NamedType (Some tau)) in Gamma)
      /\ (contains Gamma tau (EType tauDecl))
      /\ (method name defined in tauDecl with parameters formalparams returns ret)
      /\ (for each fp p of formalparams params,
         (exists t, AST.FormalParameter_type fp = Some t
               /\ expression p has type t in Gamma))
      ->
      expression (AST.MethodCall (Some this) (Some name) params) has type ret in Gamma

| type_expression_Tuple:
    forall Gamma elts typ,
      (values (AST.TupleElement_label x) for x of elts are distinct)
      /\ (for each e tau of elts typ,
         AST.TupleElement_label e = AST.FieldDecl_name tau)
      /\ (for each e tau of elts typ,
         (exists e',
            AST.TupleElement_value e = Some e'
            /\ exists tau',
                AST.FieldDecl_type tau = Some tau'
                /\ expression e' has type tau' in Gamma))
      ->
      expression (AST.Expression_Tuple elts) has type (AST.TupleType typ) in Gamma

| type_expression_Sequence:
    forall Gamma elts tau,
      (for each e of elts, expression e has type tau in Gamma)
      ->
      expression (AST.Expression_Sequence elts) has type (AST.SequenceType (Some tau)) in Gamma

| type_expression_Map:
    forall Gamma coll tau x e tau__e,
      (expression coll has type (AST.SequenceType (Some tau)) in Gamma)
      /\ (expression e has type tau__e in Gamma[x <- EVariable tau])
      ->
      expression (AST.Map (Some coll) (Some x) (Some e)) has type (AST.SequenceType (Some tau__e)) in Gamma

| type_expression_Select:
    forall Gamma coll tau x e,
      (expression coll has type (AST.SequenceType (Some tau)) in Gamma)
      /\ (expression e has type AST.BooleanType in Gamma[x <- EVariable tau])
      ->
      expression (AST.Select (Some coll) (Some x) (Some e)) has type (AST.SequenceType (Some tau)) in Gamma

| type_expression_Field:
    forall Gamma this tau name tau__f,
      (expression this has type (AST.TupleType tau) in Gamma)
      /\ field_has_type tau name tau__f
      ->
      expression (AST.Field (Some this) (Some name)) has type tau__f in Gamma

(** %\todo{%[CallExpression], [UnobservableValue], [Unify], [Relay]
and [Quantify] are not handled yet.%}% *)

(** ** Expression in the scope of a list of valuings *)

(** %\note{%The valuings are typed in order, and added incrementally
to the typing environment.%}% *)

with type_expression_where: env -> list AST.t_Valuing -> AST.t_Expression
                            -> AST.t_DataType -> Prop :=
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
      expression e under (AST.Valuing_Valuing (Some x) None (Some x__e) :: v) has type tau in Gamma

| type_expression_where_Valuing_Some:
    forall Gamma e tau x x__t x__e x__tau v,
      (expression x__e has type x__tau in Gamma)
      /\ x__tau < x__t
      /\ (expression e under v has type tau in Gamma[x <- EVariable x__t])
      ->
      expression e under (AST.Valuing_Valuing (Some x) (Some x__t) (Some x__e) :: v) has type tau in Gamma


(**
 ** Gate
 *)

with type_gate: env -> AST.t_GateDecl -> Prop :=
| type_GateDecl:
    forall Gamma name conns p,
      (protocol p well typed in Gamma)
      /\ (values (AST.Connection_name c) for c of conns are distinct)
      /\ (for each c of conns, connection c well typed in Gamma)
      ->
      gate (AST.GateDecl (Some name) conns (Some p)) well typed in Gamma


(**
 ** Duty
 *)

with type_duty: env -> AST.t_DutyDecl -> Prop :=
| type_DutyDecl:
    forall Gamma name conns a p,
      (protocol p well typed in Gamma)
      /\ (values (AST.Connection_name c) for c of conns are distinct)
      /\ (for each c of conns, connection c well typed in Gamma)
      /\ (assertion a well typed in Gamma)
      ->
      duty (AST.DutyDecl (Some name) conns (Some a) (Some p)) well typed in Gamma

(** ** Architecture behavior*)

(* %\todo{%TBD%}% *)

with type_archbehavior: env ->  AST.t_ArchBehaviorDecl -> Prop :=

(** ** Behavior *)

with type_behavior: env -> AST.t_BehaviorDecl -> Prop :=
| type_BehaviorDecl:
    forall Gamma name b,
      (body b well typed in Gamma)
      ->
      behavior (AST.BehaviorDecl (Some name) (Some (AST.Behavior b))) well typed in Gamma

(** ** Assertion *)

(** %\todo{TBD}% *)

with type_assertion: env -> AST.t_AssertionDecl -> Prop :=

(** ** Protocol *)

(** %\todo{TBD}% *)

with type_protocol: env -> AST.t_ProtocolDecl -> Prop :=

(** ** Connection *)

with type_connection: env -> AST.t_Connection -> Prop :=
| type_Connection:
    forall Gamma name k m t,
      (type t well typed in Gamma)
      ->
      connection (AST.Connection (Some k) (Some name) (Some m) (Some t)) well typed in Gamma

(** ** Body *)

(** %\note{%The typing rules enforce that statements [RepeatBehavior],
[ChooseBehavior], [RecursiveCall] and [Done] must be the last
statement of a sequence. However, the typing rule [type_EmptyBody]
allows the last statement of a sequence to be of any kind. Last, the
branches of an [IfThen] or [IfThenElse] statement may terminate with
one of the terminating statements ([RepeatBehavior], [ChooseBehavior],
[RecursiveCall] or [Done]) while the conditional statement might be
followed by subsequent statements. In summary, the typing rules are
inconsistent in regard to the question whether the type system
enforces some rules on the last statement of a sequence.%}% *)

with type_body: env -> list AST.t_BehaviorStatement -> Prop :=
| type_EmptyBody:
    forall Gamma,
      body nil well typed in Gamma

| type_Repeat:
    forall Gamma b,
      (body b well typed in Gamma)
      ->
      body (AST.RepeatBehavior (Some (AST.Behavior b)) :: nil) well typed in Gamma

| type_Choose:
    forall Gamma branches,
      (for each b of branches,
       body (AST.Behavior_statements b) well typed in Gamma)
      ->
      body (AST.ChooseBehavior branches :: nil) well typed in Gamma

| type_IfThen:
    forall Gamma c t l,
      (expression c has type AST.BooleanType in Gamma)
      /\ (body t well typed in Gamma)
      /\ (body l well typed in Gamma)
      ->
      body (AST.IfThenElseBehavior (Some c) (Some (AST.Behavior t)) None :: l) well typed in Gamma

| type_IfThenElse:
    forall Gamma c t e l,
      (expression c has type AST.BooleanType in Gamma)
      /\ (body t well typed in Gamma)
      /\ (body e well typed in Gamma)
      /\ (body l well typed in Gamma)
      ->
      body (AST.IfThenElseBehavior (Some c) (Some (AST.Behavior t)) (Some (AST.Behavior e)) :: l)
           well typed in Gamma

| type_ForEach:
    forall Gamma x tau vals b l,
      (expression vals has type (AST.SequenceType (Some tau)) in Gamma)
      /\ (body b well typed in Gamma[x <- EVariable tau ])
      /\ (body l well typed in Gamma)
      ->
      body (AST.ForEachBehavior (Some x) (Some vals) (Some (AST.Behavior b)) :: l) well typed in Gamma

| type_RecursiveCall:
    forall Gamma,
      body (AST.RecursiveCall nil :: nil) well typed in Gamma

| type_TellStatement:
    forall Gamma name e l,
      (expression e has type AST.BooleanType in Gamma)
      /\ (body l well typed in Gamma)
      ->
      body (AST.BehaviorStatement_TellAssertion (Some name) (Some e) :: l) well typed in Gamma

(** The idea underpinning the [type_AskStatement] rule is to assume an
environment [ee] in which all the (free) names of [e] are bound to
some type. Then the type of [e] as well as of the following statements
are done in [ee] merged in [Gamma]. *)

| type_AskStatement:
    forall Gamma name e ee l,
      (forall x, List.In x (names_of_expression e) <-> exists tau, contains ee x (EType tau))
      /\ (expression e has type AST.BooleanType in (Gamma <++ ee))
      /\ (body l well typed in (Gamma <++ ee))
      ->
      body (AST.BehaviorStatement_AskAssertion (Some name) (Some e) :: l) well typed in Gamma

(** %\note{%The [type_ReceiveStatement_In],
[type_ReceiveStatement_InOut], [type_SendStatement_Out] and
[type_SendStatement_InOut] assume that the complex name is a pair:
gate-or-duty, connection.%}% *)

| type_ReceiveStatement_In:
    forall Gamma gd E conn x conn__tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection AST.ModeTypeIn conn__tau))
      /\ (body l well typed in Gamma[x <- EVariable conn__tau])
      ->
      body (AST.Action (Some (AST.ComplexName (gd :: conn :: nil)))
                       (Some (AST.ReceiveAction (Some x))) :: l)
           well typed in Gamma


| type_ReceiveStatement_InOut:
    forall Gamma gd E conn x conn__tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection AST.ModeTypeInout conn__tau))
      /\ (body l well typed in Gamma[x <- EVariable conn__tau])
      ->
      body (AST.Action (Some (AST.ComplexName (gd :: conn :: nil)))
                       (Some (AST.ReceiveAction (Some x))) :: l)
           well typed in Gamma

| type_SendStatement_Out:
    forall Gamma gd E conn conn__tau e tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection AST.ModeTypeOut conn__tau))
      /\ (expression e has type tau in Gamma)
      /\ (tau < conn__tau)
      /\ (body l well typed in Gamma)
      ->
      body (AST.Action (Some (AST.ComplexName (gd :: conn :: nil)))
                       (Some (AST.SendAction (Some e))) :: l)
           well typed in Gamma

| type_SendStatement_InOut:
    forall Gamma gd E conn conn__tau e tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection AST.ModeTypeInout conn__tau))
      /\ (expression e has type tau in Gamma)
      /\ (tau < conn__tau)
      /\ (body l well typed in Gamma)
      ->
      body (AST.Action (Some (AST.ComplexName (gd :: conn :: nil)))
                       (Some (AST.SendAction (Some e))) :: l)
           well typed in Gamma

| type_DoExpr:
    forall Gamma e tau l,
      (expression e has type tau in Gamma)
      /\ (body l well typed in Gamma)
      ->
      body (AST.BehaviorStatement_DoExpr (Some e) :: l) well typed in Gamma

| type_Done:
    forall Gamma,
      body (AST.BehaviorStatement_Done :: nil) well typed in Gamma


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
and "'body' b 'well' 'typed' 'in' Gamma" := (type_body Gamma b)
.
