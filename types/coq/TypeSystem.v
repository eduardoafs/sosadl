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
| EFunction: env_content
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
Reserved Notation "'type' t 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'function' f 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'system' s 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'systemblock' s 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'mediator' m 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'architecture' a 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
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
      /\ (entity (AST.EntityBlock l funs systems mediators architectures) well typed in Gamma[name_of_datatypeDecl d <- EType d])
      ->
      entity (AST.EntityBlock (d::l) funs systems mediators architectures) well typed in Gamma

| type_EntityBlock_function:
    forall Gamma f l systems mediators architectures,
      (function f well typed in Gamma)
      /\ (entity (AST.EntityBlock nil l systems mediators architectures) well typed in Gamma[name_of_functionDecl <- EFunction])
      ->
      entity (AST.EntityBlock nil (f::l) systems mediators architectures) well typed in Gamma

| type_EntityBlock_system:
    forall Gamma s l mediators architectures,
      (system s well typed in Gamma)
      /\ (entity (AST.EntityBlock nil nil l mediators architectures) well typed in Gamma[name_of_systemDecl s <- ESystem])
      ->
      entity (AST.EntityBlock nil nil (s::l) mediators architectures) well typed in Gamma

| type_EntityBlock_mediator:
    forall Gamma m l architectures,
      (mediator m well typed in Gamma)
      /\ (entity (AST.EntityBlock nil nil nil l architectures) well typed in Gamma[name_of_mediatorDecl m <- EMediator])
      ->
      entity (AST.EntityBlock nil nil nil (m::l) architectures) well typed in Gamma

| type_EntityBlock_architecture:
    forall Gamma a l,
      (architecture a well typed in Gamma)
      /\ (entity (AST.EntityBlock nil nil nil nil l) well typed in Gamma[name_of_architectureDecl a <- EArchitecture])
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
      /\ (functions of typedecl l well typed in Gamma[name_of_functionDecl f <- EFunction])
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
      /\ (expression e under vals has type tau in env_add_params params Gamma)
      /\  contains Gamma dataTypeName (EType dataType)
      /\ tau < AST.datatype_of_datatypeDecl dataType
      ->
      function (AST.FunctionDecl name dataName dataTypeName params t vals e) well typed in Gamma

(**
 ** System

%\note{The types of formal parameters are independant of preceding parameters. For instance, {\tt system S(x: integer, y: integer\{x-1 .. x+1\})} is not allowed.}%

%\note{Unlike the Word document, the rule applies in the context of environments $\Delta$ $\Phi$.}%
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
      /\ (systemblock (AST.SystemDecl name nil l gates bhv assrt) well typed in Gamma[name_of_datatypeDecl d <- EType d])
      ->
      systemblock (AST.SystemDecl name nil (d::l) gates bhv assrt) well typed in Gamma

| type_SystemDecl_gate:
    forall Gamma name g l bhv assrt,
      (gate g well typed in Gamma)
      /\ (systemblock (AST.SystemDecl name nil nil l bhv assrt) well typed in Gamma[name_of_gateDecl g <- EGateOrDuty g])
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


(* TBD *)
(**
 ** Mediator
 *)

with type_mediator: type_environment -> function_environment -> variable_environment -> AST.mediatorDecl -> Prop :=
| type_MediatorDecl:
    forall Delta Phi Gamma name params datatypes duties b,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Delta Phi Gamma)
      /\ (for each d of datatypes,
         typedecl d well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      /\ (for each d of duties,
         duty d well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      /\ (behavior b well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      ->
      mediator (AST.MediatorDecl name params datatypes duties b) well typed in Delta Phi Gamma

(**
 ** Architecture

 *)

with type_architecture: type_environment -> function_environment -> variable_environment -> system_environment -> mediator_environment -> AST.architectureDecl -> Prop :=
| type_ArchitectureDecl:
    forall Delta Phi Gamma Sigma Mu name params datatypes gates b a,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Delta Phi Gamma)
      /\ (for each d of datatypes,
         typedecl d well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      /\ (for each g of gates,
         gate g well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      /\ (archbehavior b well typed in (env_add_types datatypes Delta) Phi)
      /\ (assertion a well typed in (env_add_types datatypes Delta) Phi)
      ->
      architecture (AST.ArchitectureDecl name params datatypes gates b a) well typed in Delta Phi Gamma Sigma Mu

(**
 ** Data types

%\note{\coqdocconstr{IntegerType} and \coqdocconstr{ConnectionType} are removed from the abstract language.}%
 *)

with type_datatype: type_environment -> function_environment -> variable_environment -> AST.datatype -> Prop :=
| type_NamedType:
    forall Delta Phi Gamma n t,
      contains Delta n t
      ->
      type (AST.NamedType n) well typed in Delta Phi Gamma

| type_TupleType:
    forall Delta Phi Gamma fields,
      (values (AST.name_of_fieldDecl f) for f of fields are distinct)
      /\ (for each f of fields,
         type (AST.type_of_fieldDecl f) well typed in Delta Phi Gamma)
      ->
      type (AST.TupleType fields) well typed in Delta Phi Gamma

| type_SequenceType:
    forall Delta Phi Gamma t,
      type t well typed in Delta Phi Gamma
      ->
      type (AST.SequenceType t) well typed in Delta Phi Gamma

(**
%\note{In comparison to the Word document, the order condition on the range boundaries is added, using some interpretation system (to be defined); boundaries are assumed to be \coqdocconstr{RangeType}.}%
 *)

| type_RangeType:
    forall Delta Phi Gamma min max min__min min__max max__min max__max,
      (expression min has type (AST.RangeType min__min min__max) in Delta Phi Gamma empty)
      /\ (expression max has type (AST.RangeType max__min max__max) in Delta Phi Gamma empty)
      /\ min <= max
      ->
      type (AST.RangeType min max) well typed in Delta Phi Gamma

(**
 ** Expression

%\todo{}%
 *)

with type_expression: type_environment -> function_environment -> variable_environment -> constituant_environment -> AST.expression -> AST.datatype -> Prop :=

(** ** Expression in the scope of a list of valuings *)
with type_expression_where: type_environment -> function_environment -> variable_environment -> constituant_environment -> list AST.valuing -> AST.expression -> AST.datatype -> Prop :=
| type_expression_where_empty:
    forall Delta Phi Gamma Kappa e tau,
      (expression e has type tau in Delta Phi Gamma Kappa)
      ->
      expression e under nil has type tau in Delta Phi Gamma Kappa

| type_expression_where_Valuing_None:
    forall Delta Phi Gamma Kappa e tau x x__e x__tau v,
      (expression x__e has type x__tau in Delta Phi Gamma Kappa)
      /\ (expression e under v has type tau in Delta Phi (Gamma[x <- x__tau]) Kappa)
      ->
      expression e under (AST.Valuing x None x__e :: v) has type tau in Delta Phi Gamma Kappa


| type_expression_where_Valuing_Some:
    forall Delta Phi Gamma Kappa e tau x x__t x__e x__tau v,
      (expression x__e has type x__t in Delta Phi Gamma Kappa)
      /\ x__t < x__tau
      /\ (expression e under v has type tau in Delta Phi (Gamma[x <- x__tau]) Kappa)
      ->
      expression e under (AST.Valuing x (Some x__t) x__e :: v) has type tau in Delta Phi Gamma Kappa

(**
 ** Gate
 *)

with type_gate: type_environment -> function_environment -> variable_environment -> AST.gateDecl -> Prop :=
| type_GateDecl:
    forall Delta Phi Gamma name conns p,
      (protocol p well typed in Delta Phi)
      /\ (for each c of conns, connection c well typed in Delta Phi Gamma)
      ->
      gate (AST.GateDecl name conns p) well typed in Delta Phi Gamma

(**
 ** Duty
 *)

with type_duty: type_environment -> function_environment -> variable_environment -> AST.dutyDecl -> Prop :=
| type_DutyDecl:
    forall Delta Phi Gamma name conns a p,
      (protocol p well typed in Delta Phi)
      /\ (for each c of conns, connection c well typed in Delta Phi Gamma)
      /\ (assertion a well typed in Delta Phi)
      ->
      duty (AST.DutyDecl name conns a p) well typed in Delta Phi Gamma

(**
 ** Architecture behavior

%\todo{}%
 *)

with type_archbehavior: type_environment -> function_environment ->  AST.archBehaviorDecl -> Prop :=

(**
 ** Behavior

%\todo{}%
 *)

with type_behavior: type_environment -> function_environment -> variable_environment -> AST.behaviorDecl -> Prop :=
| type_BehaviorDecl:
    forall Delta Phi Gamma name params b,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Delta Phi Gamma)
      /\ (body b well typed in Delta Phi (env_add_params params Gamma) (List.map AST.type_of_formalParameter params))
      ->
      behavior (AST.BehaviorDecl name params (AST.Behavior b)) well typed in Delta Phi Gamma

(**
 ** Assertion

%\todo{}%
 *)

with type_assertion: type_environment -> function_environment -> AST.assertionDecl -> Prop :=

(**
 ** Protocol

%\todo{}%
 *)

with type_protocol: type_environment -> function_environment -> AST.protocolDecl -> Prop :=

(**
 ** Connection

%\note{The rule is quite different from the one of the Word document, which was actually incorrect. Indeed, the name of the connection must not be added to the environment since connection names are not first class names.}%
 *)

with type_connection: type_environment -> function_environment -> variable_environment -> AST.connection -> Prop :=
| type_Connection:
    forall Delta Phi Gamma name k m t,
      (type t well typed in Delta Phi Gamma)
      ->
      connection (AST.Connection name k m t) well typed in Delta Phi Gamma

(**
 ** Body

%\todo{}%

%\note{According to the Word document, it's not clear whether the type system enforces some rules on the sequence of statements. For instance, {\tt repeat} is enforced as the latest statement of a body; but no check that all the branches terminate with {\tt done} or recursive call.}%

*)
with type_body: type_environment -> function_environment -> variable_environment -> list AST.datatype -> list AST.statement -> Prop :=
| type_EmptyBody:
    forall Delta Phi Gamma Rho,
      body nil well typed in Delta Phi Gamma Rho

| type_Repeat:
    forall Delta Phi Gamma Rho b,
      (body b well typed in Delta Phi Gamma Rho)
      ->
      body (AST.RepeatBehavior (AST.Behavior b) :: nil) well typed in Delta Phi Gamma Rho

| type_Choose:
    forall Delta Phi Gamma Rho branches,
      (for each b of branches, body (AST.body_of_behavior b) well typed in Delta Phi Gamma Rho)
      ->
      body (AST.ChooseBehavior branches :: nil) well typed in Delta Phi Gamma Rho

| type_IfThen:
    forall Delta Phi Gamma Rho c t l,
      (expression c has type AST.BooleanType in Delta Phi Gamma empty)
      /\ (body t well typed in Delta Phi Gamma Rho)
      /\ (body l well typed in Delta Phi Gamma Rho)
      ->
      body (AST.IfThenElseBehavior c (AST.Behavior t) None :: l) well typed in Delta Phi Gamma Rho

(** %\note{unlike the Word document, {\tt IfThenElse} is not enforced as the last statement.}%

 *)
| type_IfThenElse:
    forall Delta Phi Gamma Rho c t e l,
      (expression c has type AST.BooleanType in Delta Phi Gamma empty)
      /\ (body t well typed in Delta Phi Gamma Rho)
      /\ (body e well typed in Delta Phi Gamma Rho)
      /\ (body l well typed in Delta Phi Gamma Rho)
      ->
      body (AST.IfThenElseBehavior c (AST.Behavior t) (Some (AST.Behavior e)) :: l) well typed in Delta Phi Gamma Rho

| type_ForEach:
    forall Delta Phi Gamma Rho x tau vals b l,
      (expression vals has type (AST.SequenceType tau) in Delta Phi Gamma empty)
      /\ (body b well typed in Delta Phi Gamma[ x <- tau ] Rho)
      /\ (body l well typed in Delta Phi Gamma Rho)
      ->
      body (AST.ForEachBehavior x vals (AST.Behavior b) :: l) well typed in Delta Phi Gamma Rho

| type_RecursiveCall:
    forall Delta Phi Gamma Rho params,
      (for each tau p of Rho params , expression p has type tau in Delta Phi Gamma empty)
      ->
      body (AST.RecursiveCall params :: nil) well typed in Delta Phi Gamma Rho

(** %\note{I guess that in the Word document, the {\tt Behavior(Assert)} rule is in fact {\tt Behavior(Tell)}.}% *)
| type_TellStatement:
    forall Delta Phi Gamma Rho name e l,
      (expression e has type AST.BooleanType in Delta Phi Gamma empty)
      /\ (body l well typed in Delta Phi Gamma Rho)
      ->
      body (AST.AssertStatement (AST.Tell name e) :: l) well typed in Delta Phi Gamma Rho

(** %\note{The idea here is to assume an environment%[ee]% in which all the (free) names of%[e]% are bound to some type; then to type %[e]% as well as the following statements in %[ee]% merged in %[Gamma]%.}% *)
| type_AskStatement:
    forall Delta Phi Gamma Rho name e ee l,
      (forall x, List.In x (AST.names_of_expression e) <-> exists tau, contains ee x tau)
      /\ (expression e has type AST.BooleanType in Delta Phi (Gamma <++ ee) empty)
      /\ (body l well typed in Delta Phi (Gamma <++ ee) Rho)
      ->
      body (AST.AssertStatement (AST.Ask name e) :: l) well typed in Delta Phi Gamma Rho

(**
%\todo{Is is true that the complexnames can only be formed like this: {\tt gate::conn} or {\tt duty::conn}. The following assumes this statement.}%
*)
(*
| type_ReceiveStatement:
    forall Delta Phi Gamma Rho GD gd conn x tau,
      *)

(** ** Notations *)
where "'SoSADL' a 'well' 'typed'" := (type_sosADL a)
and "'unit' u 'well' 'typed'" := (type_unit u)
and "'entity' e 'well' 'typed'" := (type_entityBlock Gamma e)
and "'typedecl' d 'well' 'typed' 'in' Gamma" := (type_datatypeDecl Gamma d)
and "'functions' 'of' 'typedecl' t 'well' 'typed' 'in' Gamma" := (type_datatypeDecl_functions Gamma t)
and "'function' f 'well' 'typed' 'in' Gamma" := (type_function Gamma f)
and "'system' s 'well' 'typed' 'in' Gamma" := (type_system Gamma s)
and "'systemblock' s 'well' 'typed' 'in' Gamma" := (type_systemblock Gamma s).
and "'mediator' m 'well' 'typed' 'in' Gamma" := (type_mediator Gamma m)
and "'architecture' a 'well' 'typed' 'in' Gamma" := (type_architecture Gamma a)
and "'type' d 'well' 'typed' 'in' Gamma" := (type_datatype Gamma d)
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
