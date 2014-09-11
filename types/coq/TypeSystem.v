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
\todo{Must consider the task of merging environment such that different objects of different kinds (e.g., a variable, a system, a type, etc) cannot share the same name.}
*)

(**
 * Kinds of environments
 *)

Definition type_in_env := AST.datatypeDecl.

Axiom function_in_env: Set.
Axiom system_in_env: Set.
Axiom mediator_in_env: Set.
Axiom constituant_in_env: Set.

Definition type_environment := environment type_in_env.
Definition function_environment := environment function_in_env.
Definition system_environment := environment system_in_env.
Definition mediator_environment := environment mediator_in_env.
Definition constituant_environment := environment constituant_in_env.

Definition variable_environment := environment AST.datatype.

(**
 * Notations used for type judgments
 *)

Reserved Notation "'SoSADL' a 'well' 'typed'" (at level 200, no associativity).
Reserved Notation "'unit' u 'well' 'typed'" (at level 200, no associativity).
Reserved Notation "'entity' u 'well' 'typed'" (at level 200, no associativity).
Reserved Notation "'typedecl' t 'well' 'typed' 'in' Delta Phi Gamma" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, no associativity).
Reserved Notation "'type' t 'well' 'typed' 'in' Delta Phi Gamma" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, no associativity).
Reserved Notation "'function' f 'well' 'typed' 'in' Delta Phi" (at level 200, Delta at level 1, Phi at level 1, no associativity).
Reserved Notation "'system' s 'well' 'typed' 'in' Delta Phi Gamma" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, no associativity).
Reserved Notation "'mediator' m 'well' 'typed' 'in' Delta Phi Gamma" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, no associativity).
Reserved Notation "'architecture' a 'well' 'typed' 'in' Delta Phi Gamma Sigma Mu" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, Sigma at level 1, Mu at level 1, no associativity).
Reserved Notation "'expression' e 'has' 'type' t 'in' Delta Phi Gamma Kappa" (at level 200, no associativity, Delta at level 1, Phi at level 1, Gamma at level 1, Kappa at level 1).
Reserved Notation "'expression' e 'under' v 'has' 'type' t 'in' Delta Phi Gamma Kappa" (at level 200, no associativity, Delta at level 1, Phi at level 1, Gamma at level 1, Kappa at level 1).
Reserved Notation "'gate' g 'well' 'typed' 'in' Delta Phi Gamma" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, no associativity).
Reserved Notation "'duty' d 'well' 'typed' 'in' Delta Phi Gamma" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, no associativity).
Reserved Notation "'archbehavior' b 'well' 'typed' 'in' Delta Phi" (at level 200, Delta at level 1, Phi at level 1, no associativity).
Reserved Notation "'behavior' b 'well' 'typed' 'in' Delta Phi Gamma" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, no associativity).
Reserved Notation "'assertion' a 'well' 'typed' 'in' Delta Phi" (at level 200, Delta at level 1, Phi at level 1, no associativity).
Reserved Notation "'protocol' p 'well' 'typed' 'in' Delta Phi" (at level 200, Delta at level 1, Phi at level 1, no associativity).
Reserved Notation "'connection' c 'well' 'typed' 'in' Delta Phi Gamma" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, no associativity).
Reserved Notation "'body' b 'well' 'typed' 'in' Delta Phi Gamma Rho" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, Rho at level 1, no associativity).


(**
 * Functions building environments
 *)

Axiom build_function_env: list AST.functionDecl -> function_environment.
Axiom build_system_env: list AST.systemDecl -> system_environment.
Axiom build_mediator_env: list AST.mediatorDecl -> mediator_environment.

Definition env_add_params  :=
  List.fold_left (fun e f => e[AST.name_of_formalParameter f <- AST.type_of_formalParameter f]).

Definition env_of_params p := env_add_params p empty.

Definition env_add_types :=
  List.fold_left (fun e d => e[AST.name_of_datatypeDecl d <- d]).

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
      entity e well typed
      ->
      unit (AST.SoS n e) well typed

| type_Library:
    forall n e,
      entity e well typed
      ->
      unit (AST.Library n e) well typed

(** ** Entity *)
with type_entityBlock: AST.entityBlock -> Prop :=
| type_EntityBlock:
    forall datatypes functions systems mediators architectures,
      (for each d of datatypes,
       typedecl d well typed in
          (build_type_env datatypes)
            (build_function_env functions) empty)
      /\ (for each f of functions,
         function f well typed in
            (build_type_env datatypes)
              (build_function_env functions))
      /\ (for each s of systems,
         system s well typed in
            (build_type_env datatypes)
              (build_function_env functions)
              empty)
      /\ (for each m of mediators,
         mediator m well typed in
            (build_type_env datatypes)
              (build_function_env functions)
              empty)
      /\ (for each a of architectures,
         architecture a well typed in
            (build_type_env datatypes)
              (build_function_env functions)
              empty
              (build_system_env systems)
              (build_mediator_env mediators))
      ->
      entity (AST.EntityBlock datatypes functions systems mediators architectures) well typed

(** ** Data type declaration *)
with type_datatypeDecl: type_environment -> function_environment -> variable_environment -> AST.datatypeDecl -> Prop :=
| type_DataTypeDecl:
    forall Delta Phi Gamma name t functions,
      (type t well typed in Delta Phi Gamma)
      /\ (for each f of functions,
         function f well typed in Delta Phi)
      ->
      typedecl (AST.DataTypeDecl name t functions) well typed in Delta Phi Gamma

(**
 ** Function declaration

%\note{In the Word document, the \coqdocconstr{FunctionDecl} constructor is erroneously considered being parametered by the type declaration. In fact, the type is referred to by its name. Hence the \ensuremath{\Delta} environment shall be used to retrieve the named type, and this type need not be checked (again).}%
 *)

with type_function: type_environment -> function_environment -> AST.functionDecl -> Prop :=
| type_FunctionDecl:
    forall Delta Phi name dataName dataTypeName params t vals e tau dataType,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Delta Phi empty)
      /\ (expression e under vals has type tau in Delta Phi (env_of_params params) empty)
      /\  contains Delta dataTypeName dataType
      /\ tau < AST.datatype_of_datatypeDecl dataType
      ->
      function (AST.FunctionDecl name dataName dataTypeName params t vals e) well typed in Delta Phi

(**
 ** System

%\note{The types of formal parameters are independant of preceding parameters. For instance, {\tt system S(x: integer, y: integer\{x-1 .. x+1\})} is not allowed.}%

%\note{Unlike the Word document, the rule applies in the context of environments $\Delta$ $\Phi$.}%
 *)

with type_system: type_environment -> function_environment -> variable_environment -> AST.systemDecl -> Prop :=
| type_SystemDecl_Some_assertion:
    forall Delta Phi Gamma name params datatypes gates b a,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Delta Phi Gamma)
      /\ (for each d of datatypes,
         typedecl d well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      /\ (for each g of gates,
         gate g well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      /\ (behavior b well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      /\ (assertion a well typed in (env_add_types datatypes Delta) Phi)
      ->
      system (AST.SystemDecl name params datatypes gates b (Some a)) well typed in Delta Phi Gamma

(**
%\note{The Word document lacks the case where no assertion is provided.}%
*)

| type_SystemDecl_None:
    forall Delta Phi Gamma name params datatypes gates b,
      (for each p of params, type (AST.type_of_formalParameter p) well typed in Delta Phi Gamma)
      /\ (for each d of datatypes,
         typedecl d well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      /\ (for each g of gates,
         gate g well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      /\ (behavior b well typed in (env_add_types datatypes Delta) Phi (env_add_params params Gamma))
      ->
      system (AST.SystemDecl name params datatypes gates b None) well typed in Delta Phi Gamma

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

(** ** Notations *)
where "'SoSADL' a 'well' 'typed'" := (type_sosADL a)
and "'unit' u 'well' 'typed'" := (type_unit u)
and "'entity' e 'well' 'typed'" := (type_entityBlock e)
and "'typedecl' d 'well' 'typed' 'in' Delta Phi Gamma" := (type_datatypeDecl Delta Phi Gamma d)
and "'function' f 'well' 'typed' 'in' Delta Phi" := (type_function Delta Phi f)
and "'system' s 'well' 'typed' 'in' Delta Phi Gamma" := (type_system Delta Phi Gamma s)
and "'mediator' m 'well' 'typed' 'in' Delta Phi Gamma" := (type_mediator Delta Phi Gamma m)
and "'architecture' a 'well' 'typed' 'in' Delta Phi Gamma Sigma Mu" := (type_architecture Delta Phi Gamma Sigma Mu a)
and "'type' d 'well' 'typed' 'in' Delta Phi Gamma" := (type_datatype Delta Phi Gamma d)
and "'expression' e 'has' 'type' t 'in' Delta Phi Gamma Kappa" := (type_expression Delta Phi Gamma Kappa e t)
and "'expression' e 'under' v 'has' 'type' t 'in' Delta Phi Gamma Kappa" := (type_expression_where Delta Phi Gamma Kappa v e t)
and "'gate' g 'well' 'typed' 'in' Delta Phi Gamma" := (type_gate Delta Phi Gamma g)
and "'duty' d 'well' 'typed' 'in' Delta Phi Gamma" := (type_duty Delta Phi Gamma d)
and "'archbehavior' b 'well' 'typed' 'in' Delta Phi" := (type_archbehavior Delta Phi b)
and "'behavior' b 'well' 'typed' 'in' Delta Phi Gamma" := (type_behavior Delta Phi Gamma b)
and "'assertion' a 'well' 'typed' 'in' Delta Phi" := (type_assertion Delta Phi a)
and "'protocol' p 'well' 'typed' 'in' Delta Phi" := (type_protocol Delta Phi p)
and "'connection' c 'well' 'typed' 'in' Delta Phi Gamma" := (type_connection Delta Phi Gamma c)
and "'body' b 'well' 'typed' 'in' Delta Phi Gamma Rho" := (type_body Delta Phi Gamma Rho b)
.
