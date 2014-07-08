Require Import List.
Require Import String.
Require AbstractSoSADL.
Require Import Environment.
Require Import Utils.

Module AST := AbstractSoSADL.

(**
 * Kinds of environments
 *)

Axiom type_in_env: Set.
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
Reserved Notation "'system' s 'well' 'typed' 'in' Delta Phi" (at level 200, Delta at level 1, Phi at level 1, no associativity).
Reserved Notation "'mediator' m 'well' 'typed' 'in' Delta Phi" (at level 200, Delta at level 1, Phi at level 1, no associativity).
Reserved Notation "'architecture' a 'well' 'typed' 'in' Delta Phi Sigma Mu" (at level 200, Delta at level 1, Phi at level 1, Sigma at level 1, Mu at level 1, no associativity).
Reserved Notation "'expression' e 'has' 'type' t 'in' Delta Phi Gamma Kappa" (at level 200, no associativity, Delta at level 1, Phi at level 1, Gamma at level 1, Kappa at level 1). (* TODO: pourquoi cela ne fonctionne-t-il pas avec le mot-clé 'dans'? *)


(**
 * Functions building environments
 *)

Axiom build_type_env: list AST.datatypeDecl -> type_environment.
Axiom build_function_env: list AST.functionDecl -> function_environment.
Axiom build_system_env: list AST.systemDecl -> system_environment.
Axiom build_mediator_env: list AST.mediatorDecl -> mediator_environment.

(**
 * The type system

In the below rules, each inductive type gathers the rules for a single
form of judgment. Rules are built of the following:
- a rule name, here used as the name of the constructor in the inductive type;
- universal quantification of the free names of the rules;
- premises of the rule appear above the [->] operator, connected by the conjunction [/\] operator; and
- conclusion of the rule appear below the [->] operator.
 *)

Inductive type_sosADL: AST.sosADL -> Prop :=
| type_SosADL:
    forall i d,
      unit d well typed
      ->
      SoSADL (AST.SosADL i d) well typed

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
              (build_function_env functions))
      /\ (for each m of mediators,
         mediator m well typed in
            (build_type_env datatypes)
              (build_function_env functions))
      /\ (for each a of architectures,
         architecture a well typed in
            (build_type_env datatypes)
              (build_function_env functions)
              (build_system_env systems)
              (build_mediator_env mediators))
      ->
      entity (AST.EntityBlock datatypes functions systems mediators architectures) well typed

with type_datatypeDecl: type_environment -> function_environment -> variable_environment -> AST.datatypeDecl -> Prop :=
| type_DataTypeDecl:
    forall Delta Phi Gamma t functions,
      (type t well typed in Delta Phi Gamma)
      /\ (for each f of functions,
         function f well typed in Delta Phi)
      ->
      typedecl (AST.DataTypeDecl t functions) well typed in Delta Phi Gamma

with type_function: type_environment -> function_environment -> AST.functionDecl -> Prop :=

with type_system: type_environment -> function_environment -> AST.systemDecl -> Prop :=

with type_mediator: type_environment -> function_environment -> AST.mediatorDecl -> Prop :=

with type_architecture: type_environment -> function_environment -> system_environment -> mediator_environment -> AST.architectureDecl -> Prop :=

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

| type_RangeType:
    forall Delta Phi Gamma min max min__min min__max max__min max__max,
      (expression min has type (AST.RangeType min__min min__max) in Delta Phi Gamma empty)
      /\ (expression max has type (AST.RangeType max__min max__max) in Delta Phi Gamma empty)
      ->
      type (AST.RangeType min max) well typed in Delta Phi Gamma

with type_expression: type_environment -> function_environment -> variable_environment -> constituant_environment -> AST.expression -> AST.datatype -> Prop :=

where "'SoSADL' a 'well' 'typed'" := (type_sosADL a)
and "'unit' u 'well' 'typed'" := (type_unit u)
and "'entity' e 'well' 'typed'" := (type_entityBlock e)
and "'typedecl' d 'well' 'typed' 'in' Delta Phi Gamma" := (type_datatypeDecl Delta Phi Gamma d)
and "'function' f 'well' 'typed' 'in' Delta Phi" := (type_function Delta Phi f)
and "'system' s 'well' 'typed' 'in' Delta Phi" := (type_system Delta Phi s)
and "'mediator' m 'well' 'typed' 'in' Delta Phi" := (type_mediator Delta Phi m)
and "'architecture' a 'well' 'typed' 'in' Delta Phi Sigma Mu" := (type_architecture Delta Phi Sigma Mu a)
and "'type' d 'well' 'typed' 'in' Delta Phi Gamma" := (type_datatype Delta Phi Gamma d)
and "'expression' e 'has' 'type' t 'in' Delta Phi Gamma Kappa" := (type_expression Delta Phi Gamma Kappa e t)
.
