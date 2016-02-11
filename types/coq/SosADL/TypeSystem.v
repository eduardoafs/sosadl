Require Import List.
Require Import String.
Require SosADL.SosADL.
Require Import SosADL.Environment.
Require Import SosADL.Utils.
Require Import SosADL.Interpretation.

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
| GDConnection: SosADL.SosADL.ModeType -> SosADL.SosADL.t_DataType -> gd_env_content.

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
| EType: SosADL.SosADL.t_DataTypeDecl -> env_content
| EFunction: SosADL.SosADL.t_FunctionDecl -> env_content
| ESystem: SosADL.SosADL.t_SystemDecl -> env_content
| EMediator: SosADL.SosADL.t_MediatorDecl -> env_content
| EArchitecture: SosADL.SosADL.t_ArchitectureDecl -> env_content
| EGateOrDuty: environment gd_env_content -> env_content
| EVariable: SosADL.SosADL.t_DataType -> env_content.

Definition env := environment env_content.


(**
 ** Utility functions
 *)

(** [env_add_params] adds a list of formal parameters to an
environment.  *)

Definition env_add_params a b :=
  List.fold_right
    (fun f e =>
       match SosADL.SosADL.FormalParameter_name f with
         | Some name =>
           match SosADL.SosADL.FormalParameter_type f with
             | Some type => e [| name <- EVariable type |]
             | None => e
           end
         | None => e
       end) b a.

(** [conns_environment] builds an environment containing connections,
from a list of these connections. *)

Definition conns_environment l :=
  List.fold_left
    (fun e c =>
       match SosADL.SosADL.Connection_name c with
         | Some name =>
           match SosADL.SosADL.Connection_mode c with
             | Some mode =>
               match SosADL.SosADL.Connection_valueType c with
                 | Some type => e [| name <- GDConnection mode type |]
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
  conns_environment (SosADL.SosADL.GateDecl_connections g).

(** [build_duty_env] builds the secondary environment for a duty
declaration. *)

Definition build_duty_env d :=
  conns_environment (SosADL.SosADL.DutyDecl_connections d).

(**
 * Utilities
 *)

(** The following notations is a shortcut to look for a method in a
data type declaration.  *)

Notation "'method' m 'defined' 'in' d 'with' 'parameters' f 'returns' r" :=
  (List.Exists (fun fd => SosADL.SosADL.FunctionDecl_name fd = Some m
                         /\ SosADL.SosADL.FunctionDecl_parameters fd = f
                         /\ SosADL.SosADL.FunctionDecl_type fd = Some r)
               (SosADL.SosADL.DataTypeDecl_functions d))
    (at level 200, no associativity).

(** [field_has_type] is a predicate to look for a field in a list of
field declarations. *)

Inductive field_has_type: list SosADL.SosADL.t_FieldDecl -> string -> SosADL.SosADL.t_DataType -> Prop :=
| First_Field: forall n t r, field_has_type (SosADL.SosADL.FieldDecl (Some n) (Some t) :: r) n t
| Next_Field: forall n t h r, field_has_type r n t -> field_has_type (h :: r) n t.

Hypothesis names_of_expression: SosADL.SosADL.t_Expression -> list string.
(**
%
\def\todo#1{{\color{red}TODO: #1}}
\def\note#1{{\color{blue}NOTE: #1}}
%
*)

(** * Subtyping relation *)

Reserved Notation "t1 </ t2 'under' Gamma" (at level 70).

Inductive subtype: env -> SosADL.SosADL.t_DataType -> SosADL.SosADL.t_DataType -> Prop :=
| subtype_refl:
    forall Gamma t, t </ t under Gamma
| subtype_range:
    forall Gamma lmi lma rmi rma,
      rmi <= lmi /\ lma <= rma
      -> (SosADL.SosADL.RangeType (Some lmi) (Some lma)) </ (SosADL.SosADL.RangeType (Some rmi) (Some rma)) under Gamma
| subtype_left:
    forall Gamma l r def funs,
      (contains Gamma l (EType (SosADL.SosADL.DataTypeDecl (Some l) (Some def) funs)))
      /\ (def </ r under Gamma)
      ->
      (SosADL.SosADL.NamedType (Some l)) </ r under Gamma
| subtype_right:
    forall Gamma l r def funs,
      (contains Gamma r (EType (SosADL.SosADL.DataTypeDecl (Some r) (Some def) funs)))
      /\ (l </ def under Gamma)
      ->
      l </ (SosADL.SosADL.NamedType (Some r)) under Gamma
| subtype_tuple:
    forall Gamma l r,
      (for each f of r,
       exists n,
         SosADL.SosADL.FieldDecl_name f = Some n
         /\ exists tr,
             SosADL.SosADL.FieldDecl_type f = Some tr
             /\ exists tl, field_has_type l n tl
                     /\ (tl </ tr under Gamma))
      ->
      (SosADL.SosADL.TupleType l) </ (SosADL.SosADL.TupleType r) under Gamma

(** %\todo{%TBD%}% *)

where "t1 </ t2 'under' Gamma" := (subtype Gamma t1 t2)
.

(**
 * Generic constructions

The following provide generic constructions for the type system.

 *)

Definition augment_env (Gamma: env) (n: option string) (c: option env_content) :=
  match n with
  | None => Gamma
  | Some name =>
    match c with
    | None => Gamma
    | Some content => Gamma [| name <- content |]
    end
  end.

(** [incrementally] is a generic set of rules for incremental, ordered definitions. *)

Inductive incrementally
          {T: Set} {P: env -> T -> Prop} {name: T -> option string} {content: T -> option env_content}:
  env -> list T -> env -> Prop :=
  
| incrementally_nil:
    forall
      (Gamma: env)
    ,
      incrementally Gamma nil Gamma

| incrementally_cons:
    forall
      (Gamma: env)
      (x: T)
      (n: option string)
      (c: option env_content)
      (Gammai: env)
      (l: list T)
      (Gamma1: env)
      (p1: P Gamma x)
      (p2: name x = n)
      (p3: content x = c)
      (p4: augment_env Gamma n c = Gammai)
      (p5: incrementally Gammai l Gamma1)
    ,
      incrementally Gamma (x::l) Gamma1
.

Lemma incrementally_fold_left:
  forall {T: Set} (P: env -> T -> Prop) (name: T -> option string)
         (content: T -> option env_content) (l: list T)
         (Gamma: env) (Gamma': env)
         (s: @incrementally T P name content Gamma l Gamma'),
    Gamma' = fold_left (fun r x => augment_env r (name x) (content x)) l Gamma.
Proof.
  intros.
  induction s; subst; auto.
Qed.

Definition augment_env_with_all (Gamma: env) {T: Set} (name: T -> option string) (content: T -> option env_content) (l: list T) :=
  List.fold_right (fun x g => augment_env g (name x) (content x)) Gamma l.

(** [mutually] is a generic rule for unordered, simultaneous, mutual definitions. *)

Inductive mutually
          {T: Set} {P: env -> T -> env -> Prop} {name: T -> option string} {content: T -> option env_content}:
  env -> list T -> env -> Prop :=

| mutually_all:
    forall
      (Gamma: env)
      (l: list T)
      (Gamma1: env)
      (p1: (augment_env_with_all Gamma name content l) = Gamma1)
      (p2: values (name x) for x of l are distinct according to option_string_dec)
      (p3: for each x of l, P Gamma x Gamma1)
    ,
      mutually Gamma l Gamma1
.

(** [optionally] is a generic rule for an optional statement. *)

Inductive optionally {T: Set} {P: env -> T -> Prop}:
  env -> option T -> Prop :=
| optionally_None:
    forall
      (Gamma: env)
    ,
      optionally Gamma None

| optionally_Some:
    forall
      (Gamma: env)
      (x: T)
      (p1: P Gamma x)
    ,
      optionally Gamma (Some x)
.

(**
 * Notations

The following notations defines all the judgment forms in the type
system. Usually, the typing environment is denoted [Gamma].

The judgement for statements ([body]) has a second environment denoted
[Pi], holding the types of the formal parameters of the enclosing
behavior. This second environment [Pi] is mandatory to type the
recursive call statement.

 *)

Reserved Notation "'expression' e 'is' 'constant' 'integer'" (at level 200, no associativity).
Reserved Notation "'SoSADL' a 'well' 'typed'" (at level 200, no associativity).
Reserved Notation "'unit' u 'well' 'typed' 'in' Gamma" (at level 200, no associativity).
Reserved Notation "'entity' u 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'typedecl' t 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'functions' 'of' 'typedecl' t 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'function' f 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'type' t 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'system' s 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
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
 ** Constant expressions
 *)

Inductive constexpr_expression: SosADL.SosADL.t_Expression -> Prop :=
| constexpr_IntegerValue:
    forall
      (v: BinInt.Z)
    ,
      expression (SosADL.SosADL.IntegerValue (Some v)) is constant integer

| constexpr_Opposite:
    forall
      (e: SosADL.SosADL.t_Expression)
      (p: expression e is constant integer)
    ,
      expression (SosADL.SosADL.UnaryExpression (Some "-") (Some e)) is constant integer

| constexpr_Same:
    forall
      (e: SosADL.SosADL.t_Expression)
      (p: expression e is constant integer)
    ,
      expression (SosADL.SosADL.UnaryExpression (Some "+") (Some e)) is constant integer

| constexpr_Add:
    forall
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: expression l is constant integer)
      (p2: expression r is constant integer)
    ,
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "+") (Some r)) is constant integer

| constexpr_Sub:
    forall
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: expression l is constant integer)
      (p2: expression r is constant integer)
    ,
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "-") (Some r)) is constant integer

| constexpr_Mul:
    forall
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: expression l is constant integer)
      (p2: expression r is constant integer)
    ,
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "*") (Some r)) is constant integer

| constexpr_Div:
    forall
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: expression l is constant integer)
      (p2: expression r is constant integer)
    ,
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "/") (Some r)) is constant integer

| constexpr_Mod:
    forall
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: expression l is constant integer)
      (p2: expression r is constant integer)
    ,
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "mod") (Some r)) is constant integer
                 
where "'expression' e 'is' 'constant' 'integer'" := (constexpr_expression e)
.

(** ** Data types *)

Inductive type_datatype: env -> SosADL.SosADL.t_DataType -> Prop :=
| type_NamedType:
    forall
      (Gamma: env)
      (n: string)
      (t: SosADL.SosADL.t_DataTypeDecl)
      (p: contains Gamma n (EType t))
    ,
      type (SosADL.SosADL.NamedType (Some n)) well typed in Gamma

| type_TupleType:
    forall
      (Gamma: env)
      (fields: list SosADL.SosADL.t_FieldDecl)
      (p1: @mutually _ (fun gamma f _ =>
                          exists t, SosADL.SosADL.FieldDecl_type f = Some t
                                    /\ type t well typed in Gamma)
                     (fun _ => None)
                     (fun _ => None)
                     Gamma fields Gamma)
(*                     
      (p1: values (SosADL.SosADL.FieldDecl_name f) for f of fields are distinct according to option_string_dec)
      (p2: for each f of fields,
           (exists t, SosADL.SosADL.FieldDecl_type f = Some t
                      /\ type t well typed in Gamma))
*)
    ,
      type (SosADL.SosADL.TupleType fields) well typed in Gamma

| type_SequenceType:
    forall
      (Gamma: env)
      (t: SosADL.SosADL.t_DataType)
      (p: type t well typed in Gamma)
    ,
      type (SosADL.SosADL.SequenceType (Some t)) well typed in Gamma

                                                       (*
| type_RangeType:
    forall Gamma min max min__min min__max max__min max__max,
      (expression min has type (SosADL.SosADL.RangeType (Some min__min) (Some min__max)) in Gamma)
      /\ (expression max has type (SosADL.SosADL.RangeType (Some max__min) (Some max__max)) in Gamma)
      /\ min <= max
      ->
      type (SosADL.SosADL.RangeType (Some min) (Some max)) well typed in Gamma
*)

| type_RangeType_trivial:
    forall
      (Gamma: env)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: expression min is constant integer)
      (p2: expression max is constant integer)
      (p3: min <= max)
    ,
      type (SosADL.SosADL.RangeType (Some min)
                          (Some max)) well typed in Gamma

where "'type' t 'well' 'typed' 'in' Gamma" := (type_datatype Gamma t)
.



(** ** Data type declaration *)

(** %\note{%The functions (methods) of the data type declaration can
be mutually recursive. Indeed, they are typed in an environment that
binds the data type declaration, including the list of functions
(methods).%}% *)

Inductive type_datatypeDecl: env -> SosADL.SosADL.t_DataTypeDecl -> Prop :=
       (* TODO
| type_DataTypeDecl_Some:
    forall Gamma name t funs,
      (type t well typed in Gamma)
      /\ (values (SosADL.SosADL.FunctionDecl_name x) for x of funs are distinct)
      /\ (functions of typedecl funs
                   well typed in Gamma [| name <- EType (SosADL.SosADL.DataTypeDecl (Some name) (Some t) funs) |])
      ->
      typedecl (SosADL.SosADL.DataTypeDecl (Some name) (Some t) funs) well typed in Gamma

| type_DataTypeDecl_None:
    forall Gamma name,
      typedecl (SosADL.SosADL.DataTypeDecl (Some name) None nil) well typed in Gamma
*)

(** %\note{%The functions (methods) of the data type declaration are
typed in order. In fact, this is not mandatory since the environment
remains the same while traversing the list of functions. The rule
might be simplified in this regard, using, e.g., [List.Forall].%}% *)

with type_datatypeDecl_functions: env -> list SosADL.SosADL.t_FunctionDecl -> Prop :=
       (* TODO
| type_datatypeDecl_empty:
    forall Gamma, functions of typedecl nil well typed in Gamma

| type_datatypeDecl_f:
    forall Gamma f l,
      (function f well typed in Gamma)
      /\ (functions of typedecl l well typed in Gamma)
      ->
      functions of typedecl (f::l) well typed in Gamma
*)
                                 
(** ** Function declaration *)

with type_function: env -> SosADL.SosADL.t_FunctionDecl -> Prop :=
       (* TODO
| type_FunctionDecl:
    forall Gamma name dataName dataTypeName params t vals e tau dtname dttype dtfuns,
      (for each p of params, (exists t, SosADL.SosADL.FormalParameter_type p = Some t /\ type t well typed in Gamma))
      /\ (expression e under vals has type tau in (env_add_params params Gamma [| dataName <- EVariable (SosADL.SosADL.NamedType (Some dataTypeName)) |]))
      /\ (contains Gamma dataTypeName (EType (SosADL.SosADL.DataTypeDecl (Some dtname) (Some dttype) dtfuns)))
      /\ (tau </ t under Gamma)
      ->
      function (SosADL.SosADL.FunctionDecl (Some dataName) (Some dataTypeName) (Some name) params (Some t) vals (Some e))
               well typed in Gamma
*)


(** ** Mediator *)

(** %\note{%By choice, the elements declared in the mediator are typed
in order by the set rules for [type_mediatorblock].%}% *)

with type_mediator: env -> SosADL.SosADL.t_MediatorDecl -> Prop :=
       (* TODO
| type_MediatorDecl:
    forall Gamma name params datatypes duties b assump assert,
      (for each p of params, (exists t, SosADL.SosADL.FormalParameter_type p = Some t /\ type t well typed in Gamma))
        /\ (mediatorblock (SosADL.SosADL.MediatorDecl (Some name) nil datatypes duties (Some b) assump assert)
                         well typed in (env_add_params params Gamma))
      ->
      mediator (SosADL.SosADL.MediatorDecl (Some name) params datatypes duties (Some b) assump assert) well typed in Gamma
*)

with type_mediatorblock: env -> SosADL.SosADL.t_MediatorDecl -> Prop :=

  (** %\todo{%Data type declarations in mediators should be inspired from the rules for systems.%}% *)
  (* TODO
| type_MediatorDecl_datatype:
    forall Gamma name d d_name l duties bhv assump assert,
      (typedecl d well typed in Gamma)
      /\ (SosADL.SosADL.DataTypeDecl_name d = Some d_name)
      /\ (mediatorblock (SosADL.SosADL.MediatorDecl (Some name) nil l duties (Some bhv) assump assert)
                       well typed in Gamma [| d_name <- EType d |])
      ->
      mediatorblock (SosADL.SosADL.MediatorDecl (Some name) nil (d::l) duties (Some bhv) assump assert) well typed in Gamma


| type_MediatorDecl_duty:
    forall Gamma name d d_name l bhv assump assert,
      (duty d well typed in Gamma)
      /\ (SosADL.SosADL.DutyDecl_name d = Some d_name)
      /\ (mediatorblock (SosADL.SosADL.MediatorDecl (Some name) nil nil l (Some bhv) assump assert)
                       well typed in Gamma [| d_name <- EGateOrDuty (build_duty_env d) |])
      ->
      mediatorblock (SosADL.SosADL.MediatorDecl (Some name) nil nil (d::l) (Some bhv) assump assert) well typed in Gamma

| type_MediatorDecl_Behavior:
    forall Gamma name bhv assump assert,
      (behavior bhv well typed in Gamma)
      ->
      mediatorblock (SosADL.SosADL.MediatorDecl name nil nil nil (Some bhv) assump assert) well typed in Gamma
   *)
       
(** ** Architecture *)

(** %\note{%By choice, the elements declared in the architecture are
typed in order by the set rules for [type_architectureblock].%}% *)

with type_architecture: env -> SosADL.SosADL.t_ArchitectureDecl -> Prop :=
(* TODO
     | type_ArchitectureDecl:
    forall Gamma name params datatypes gates b a,
      (for each p of params, (exists t, SosADL.SosADL.FormalParameter_type p = Some t /\ type t well typed in Gamma))
      /\ (architectureblock (SosADL.SosADL.ArchitectureDecl (Some name) nil datatypes gates (Some b) a)
                           well typed in (env_add_params params Gamma))
      ->
      architecture (SosADL.SosADL.ArchitectureDecl (Some name) params datatypes gates (Some b) a)
                   well typed in Gamma
*)
with type_architectureblock: env -> SosADL.SosADL.t_ArchitectureDecl -> Prop :=

  (** %\todo{%Data type declarations in architectures should be inspired from the rules for systems.%}% *)
  (* TODO
| type_ArchitectureDecl_datatype:
    forall Gamma name d d_name l gates bhv a,
      (typedecl d well typed in Gamma)
      /\ (SosADL.SosADL.DataTypeDecl_name d = Some d_name)
      /\ (architectureblock (SosADL.SosADL.ArchitectureDecl (Some name) nil l gates (Some bhv) a)
                           well typed in Gamma [| d_name <- EType d |])
      ->
      architectureblock (SosADL.SosADL.ArchitectureDecl (Some name) nil (d::l) gates (Some bhv) a)
                        well typed in Gamma

  
| type_ArchitectureDecl_gate:
    forall Gamma name g g_name l bhv a,
      (gate g well typed in Gamma)
      /\ (SosADL.SosADL.GateDecl_name g = Some g_name)
      /\ (architectureblock (SosADL.SosADL.ArchitectureDecl (Some name) nil nil l (Some bhv) a)
                           well typed in Gamma [| g_name <- EGateOrDuty (build_gate_env g) |])
      ->
      architectureblock (SosADL.SosADL.ArchitectureDecl (Some name) nil nil (g::l) (Some bhv) a)
                        well typed in Gamma

| type_ArchitectureDecl_behavior:
    forall Gamma name bhv a,
      (archbehavior bhv well typed in Gamma)
      /\ (assertion a well typed in Gamma)
      ->
      architectureblock (SosADL.SosADL.ArchitectureDecl (Some name) nil nil nil (Some bhv) (Some a)) well typed in Gamma
*)


(**
 ** Expression
 *)

with type_expression: env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop :=
| type_expression_IntegerValue:
    forall Gamma v,
      expression (SosADL.SosADL.IntegerValue (Some v))
      has type (SosADL.SosADL.RangeType (Some (SosADL.SosADL.IntegerValue (Some v)))
                              (Some (SosADL.SosADL.IntegerValue (Some v)))) in Gamma

| type_expression_Any:
    forall Gamma tau,
      expression SosADL.SosADL.Any has type tau in Gamma

| type_expression_Opposite:
    forall Gamma e min max,
      (expression e has type (SosADL.SosADL.RangeType (Some min) (Some max)) in Gamma)
      ->
      expression (SosADL.SosADL.UnaryExpression (Some "-") (Some e))
      has type (SosADL.SosADL.RangeType (Some (SosADL.SosADL.UnaryExpression (Some "-") (Some max)))
                              (Some (SosADL.SosADL.UnaryExpression (Some "-") (Some min)))) in Gamma

| type_expression_Same:
    forall Gamma e min max,
      (expression e has type (SosADL.SosADL.RangeType (Some min) (Some max)) in Gamma)
      ->
      expression (SosADL.SosADL.UnaryExpression (Some "+") (Some e))
      has type (SosADL.SosADL.RangeType (Some min) (Some max)) in Gamma

| type_expression_Not:
    forall Gamma e,
      (expression e has type SosADL.SosADL.BooleanType in Gamma)
      ->
      expression (SosADL.SosADL.UnaryExpression (Some "not") (Some e)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Add:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (SosADL.SosADL.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (SosADL.SosADL.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "+") (Some r))
      has type (SosADL.SosADL.RangeType (Some (SosADL.SosADL.BinaryExpression (Some l__min) (Some "+") (Some r__min)))
                              (Some (SosADL.SosADL.BinaryExpression (Some l__max) (Some "+") (Some r__max)))) in Gamma

| type_expression_Sub:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (SosADL.SosADL.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (SosADL.SosADL.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "-") (Some r))
      has type (SosADL.SosADL.RangeType (Some (SosADL.SosADL.BinaryExpression (Some l__min) (Some "-") (Some r__max)))
                              (Some (SosADL.SosADL.BinaryExpression (Some l__max) (Some "-") (Some r__min)))) in Gamma

(** %\todo{%The typing rules for [*], [/] and [mod] needs to be
written.%}% *)

| type_expression_Implies:
   forall Gamma l r,
     (expression l has type SosADL.SosADL.BooleanType in Gamma)
     /\ (expression r has type SosADL.SosADL.BooleanType in Gamma)
     ->
     expression (SosADL.SosADL.BinaryExpression (Some l) (Some "implies") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Or:
   forall Gamma l r,
     (expression l has type SosADL.SosADL.BooleanType in Gamma)
     /\ (expression r has type SosADL.SosADL.BooleanType in Gamma)
     ->
     expression (SosADL.SosADL.BinaryExpression (Some l) (Some "or") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Xor:
   forall Gamma l r,
     (expression l has type SosADL.SosADL.BooleanType in Gamma)
     /\ (expression r has type SosADL.SosADL.BooleanType in Gamma)
     ->
     expression (SosADL.SosADL.BinaryExpression (Some l) (Some "xor") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_And:
   forall Gamma l r,
     (expression l has type SosADL.SosADL.BooleanType in Gamma)
     /\ (expression r has type SosADL.SosADL.BooleanType in Gamma)
     ->
     expression (SosADL.SosADL.BinaryExpression (Some l) (Some "and") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Equal:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (SosADL.SosADL.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (SosADL.SosADL.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "=") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Diff:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (SosADL.SosADL.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (SosADL.SosADL.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "<>") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Lt:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (SosADL.SosADL.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (SosADL.SosADL.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "<") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Le:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (SosADL.SosADL.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (SosADL.SosADL.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some "<=") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Gt:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (SosADL.SosADL.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (SosADL.SosADL.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some ">") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Ge:
    forall Gamma l l__min l__max r r__min r__max,
      (expression l has type (SosADL.SosADL.RangeType (Some l__min) (Some l__max)) in Gamma)
      /\ (expression r has type (SosADL.SosADL.RangeType (Some r__min) (Some r__max)) in Gamma)
      ->
      expression (SosADL.SosADL.BinaryExpression (Some l) (Some ">=") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Ident:
    forall Gamma x tau tau__e,
      (contains Gamma x (EVariable tau))
      /\ (tau </ tau__e under Gamma)
      ->
      expression (SosADL.SosADL.IdentExpression (Some x)) has type tau__e in Gamma

(** %\note{%The rule [type_expression_MethodCall] assumes that the
type of the [this] parameter is a named type, hence refering to the
declaration of a data type containing some functions (methods).%}% *)

| type_expression_MethodCall:
    forall Gamma this tau tauDecl name formalparams params ret,
      (expression this has type (SosADL.SosADL.NamedType (Some tau)) in Gamma)
      /\ (contains Gamma tau (EType tauDecl))
      /\ (method name defined in tauDecl with parameters formalparams returns ret)
      /\ (for each fp p of formalparams params,
         (exists t, SosADL.SosADL.FormalParameter_type fp = Some t
               /\ (exists tp, (expression p has type tp in Gamma)
                        /\ tp </ t under Gamma)))
      ->
      expression (SosADL.SosADL.MethodCall (Some this) (Some name) params) has type ret in Gamma

| type_expression_Tuple:
    forall Gamma elts typ,
      (values (SosADL.SosADL.TupleElement_label x) for x of elts are distinct according to option_string_dec)
      /\ (for each e tau of elts typ,
         SosADL.SosADL.TupleElement_label e = SosADL.SosADL.FieldDecl_name tau)
      /\ (for each e tau of elts typ,
         (exists e',
            SosADL.SosADL.TupleElement_value e = Some e'
            /\ exists tau',
                SosADL.SosADL.FieldDecl_type tau = Some tau'
                /\ expression e' has type tau' in Gamma))
      ->
      expression (SosADL.SosADL.Expression_Tuple elts) has type (SosADL.SosADL.TupleType typ) in Gamma

| type_expression_Sequence:
    forall Gamma elts tau,
      (for each e of elts, expression e has type tau in Gamma)
      ->
      expression (SosADL.SosADL.Expression_Sequence elts) has type (SosADL.SosADL.SequenceType (Some tau)) in Gamma

| type_expression_Map:
    forall Gamma coll tau x e tau__e,
      (expression coll has type (SosADL.SosADL.SequenceType (Some tau)) in Gamma)
      /\ (expression e has type tau__e in Gamma [| x <- EVariable tau |])
      ->
      expression (SosADL.SosADL.Map (Some coll) (Some x) (Some e)) has type (SosADL.SosADL.SequenceType (Some tau__e)) in Gamma

| type_expression_Select:
    forall Gamma coll tau x e,
      (expression coll has type (SosADL.SosADL.SequenceType (Some tau)) in Gamma)
      /\ (expression e has type SosADL.SosADL.BooleanType in Gamma [| x <- EVariable tau |])
      ->
      expression (SosADL.SosADL.Select (Some coll) (Some x) (Some e)) has type (SosADL.SosADL.SequenceType (Some tau)) in Gamma

| type_expression_Field:
    forall Gamma this tau name tau__f,
      (expression this has type (SosADL.SosADL.TupleType tau) in Gamma)
      /\ field_has_type tau name tau__f
      ->
      expression (SosADL.SosADL.Field (Some this) (Some name)) has type tau__f in Gamma

(** %\todo{%[CallExpression], [UnobservableValue], [Unify], [Relay]
and [Quantify] are not handled yet.%}% *)

(** ** Expression in the scope of a list of valuings *)

(** %\note{%The valuings are typed in order, and added incrementally
to the typing environment.%}% *)

with type_expression_where: env -> list SosADL.SosADL.t_Valuing -> SosADL.SosADL.t_Expression
                            -> SosADL.SosADL.t_DataType -> Prop :=
| type_expression_where_empty:
    forall Gamma e tau,
      (expression e has type tau in Gamma)
      ->
      expression e under nil has type tau in Gamma

| type_expression_where_Valuing_None:
    forall Gamma e tau x x__e x__tau v,
      (expression x__e has type x__tau in Gamma)
      /\ (expression e under v has type tau in Gamma [| x <- EVariable x__tau |])
      ->
      expression e under (SosADL.SosADL.Valuing_Valuing (Some x) None (Some x__e) :: v) has type tau in Gamma

| type_expression_where_Valuing_Some:
    forall Gamma e tau x x__t x__e x__tau v,
      (expression x__e has type x__tau in Gamma)
      /\ (x__tau </ x__t under Gamma)
      /\ (expression e under v has type tau in Gamma [| x <- EVariable x__t |])
      ->
      expression e under (SosADL.SosADL.Valuing_Valuing (Some x) (Some x__t) (Some x__e) :: v) has type tau in Gamma


(**
 ** Gate
 *)

with type_gate: env -> SosADL.SosADL.t_GateDecl -> Prop :=
| type_GateDecl:
    forall Gamma name conns p,
      (protocol p well typed in Gamma)
      /\ (values (SosADL.SosADL.Connection_name c) for c of conns are distinct according to option_string_dec)
      /\ (for each c of conns, connection c well typed in Gamma)
      ->
      gate (SosADL.SosADL.GateDecl (Some name) conns (Some p)) well typed in Gamma


(**
 ** Duty
 *)

with type_duty: env -> SosADL.SosADL.t_DutyDecl -> Prop :=
| type_DutyDecl:
    forall Gamma name conns a p,
      (protocol p well typed in Gamma)
      /\ (values (SosADL.SosADL.Connection_name c) for c of conns are distinct according to option_string_dec)
      /\ (for each c of conns, connection c well typed in Gamma)
      /\ (assertion a well typed in Gamma)
      ->
      duty (SosADL.SosADL.DutyDecl (Some name) conns (Some a) (Some p)) well typed in Gamma

(** ** Architecture behavior*)

(* %\todo{%TBD%}% *)

with type_archbehavior: env ->  SosADL.SosADL.t_ArchBehaviorDecl -> Prop :=

(** ** Behavior *)

with type_behavior: env -> SosADL.SosADL.t_BehaviorDecl -> Prop :=
| type_BehaviorDecl:
    forall Gamma name b,
      (body b well typed in Gamma)
      ->
      behavior (SosADL.SosADL.BehaviorDecl (Some name) (Some (SosADL.SosADL.Behavior b))) well typed in Gamma

(** ** Assertion *)

(** %\todo{TBD}% *)

with type_assertion: env -> SosADL.SosADL.t_AssertionDecl -> Prop :=

(** ** Protocol *)

(** %\todo{TBD}% *)

with type_protocol: env -> SosADL.SosADL.t_ProtocolDecl -> Prop :=

(** ** Connection *)

with type_connection: env -> SosADL.SosADL.t_Connection -> Prop :=
| type_Connection:
    forall Gamma name k m t,
      (type t well typed in Gamma)
      ->
      connection (SosADL.SosADL.Connection (Some k) (Some name) (Some m) (Some t)) well typed in Gamma

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

with type_body: env -> list SosADL.SosADL.t_BehaviorStatement -> Prop :=
| type_EmptyBody:
    forall Gamma,
      body nil well typed in Gamma

| type_Valuing_None:
    forall Gamma x e tau l,
      (expression e has type tau in Gamma)
      /\ (body l well typed in Gamma [| x <- EVariable tau |])
      ->
      body (SosADL.SosADL.BehaviorStatement_Valuing (Some x) None (Some e) :: l) well typed in Gamma

| type_Valuing_Some:
    forall Gamma x e tau tau__e l,
      (expression e has type tau__e in Gamma)
      /\ (tau__e </ tau under Gamma)
      /\ (body l well typed in Gamma [| x <- EVariable  tau |])
      ->
      body (SosADL.SosADL.BehaviorStatement_Valuing (Some x) (Some tau) (Some e) :: l) well typed in Gamma

| type_Repeat:
    forall Gamma b,
      (body b well typed in Gamma)
      ->
      body (SosADL.SosADL.RepeatBehavior (Some (SosADL.SosADL.Behavior b)) :: nil) well typed in Gamma

| type_Choose:
    forall Gamma branches,
      (for each b of branches,
       body (SosADL.SosADL.Behavior_statements b) well typed in Gamma)
      ->
      body (SosADL.SosADL.ChooseBehavior branches :: nil) well typed in Gamma

| type_IfThen:
    forall Gamma c t l,
      (expression c has type SosADL.SosADL.BooleanType in Gamma)
      /\ (body t well typed in Gamma)
      /\ (body l well typed in Gamma)
      ->
      body (SosADL.SosADL.IfThenElseBehavior (Some c) (Some (SosADL.SosADL.Behavior t)) None :: l) well typed in Gamma

| type_IfThenElse:
    forall Gamma c t e,
      (expression c has type SosADL.SosADL.BooleanType in Gamma)
      /\ (body t well typed in Gamma)
      /\ (body e well typed in Gamma)
      ->
      body (SosADL.SosADL.IfThenElseBehavior (Some c) (Some (SosADL.SosADL.Behavior t)) (Some (SosADL.SosADL.Behavior e)) :: nil)
           well typed in Gamma

| type_ForEach:
    forall Gamma x tau vals b l,
      (expression vals has type (SosADL.SosADL.SequenceType (Some tau)) in Gamma)
      /\ (body b well typed in Gamma [| x <- EVariable tau |])
      /\ (body l well typed in Gamma)
      ->
      body (SosADL.SosADL.ForEachBehavior (Some x) (Some vals) (Some (SosADL.SosADL.Behavior b)) :: l) well typed in Gamma

| type_RecursiveCall:
    forall Gamma,
      body (SosADL.SosADL.RecursiveCall nil :: nil) well typed in Gamma

| type_TellStatement:
    forall Gamma name e l,
      (expression e has type SosADL.SosADL.BooleanType in Gamma)
      /\ (body l well typed in Gamma)
      ->
      body (SosADL.SosADL.BehaviorStatement_TellAssertion (Some name) (Some e) :: l) well typed in Gamma

(** The idea underpinning the [type_AskStatement] rule is to assume an
environment [ee] in which all the (free) names of [e] are bound to
some type. Then the type of [e] as well as of the following statements
are done in [ee] merged in [Gamma]. *)

                                                                                 (** *)
  (*
| type_AskStatement:
    forall Gamma name e ee l,
      (forall x, List.In x (names_of_expression e) <-> exists tau, contains ee x (EType tau))
      /\ (expression e has type SosADL.SosADL.BooleanType in (Gamma <++ ee))
      /\ (body l well typed in (Gamma <++ ee))
      ->
      body (SosADL.SosADL.BehaviorStatement_AskAssertion (Some name) (Some e) :: l) well typed in Gamma
*)

(** %\note{%The [type_ReceiveStatement_In],
[type_ReceiveStatement_InOut], [type_SendStatement_Out] and
[type_SendStatement_InOut] assume that the complex name is a pair:
gate-or-duty, connection.%}% *)

| type_ReceiveStatement_In:
    forall Gamma gd E conn x conn__tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection SosADL.SosADL.ModeTypeIn conn__tau))
      /\ (body l well typed in Gamma [| x <- EVariable conn__tau |])
      ->
      body (SosADL.SosADL.Action (Some (SosADL.SosADL.ComplexName (gd :: conn :: nil)))
                       (Some (SosADL.SosADL.ReceiveAction (Some x))) :: l)
           well typed in Gamma


| type_ReceiveStatement_InOut:
    forall Gamma gd E conn x conn__tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection SosADL.SosADL.ModeTypeInout conn__tau))
      /\ (body l well typed in Gamma [| x <- EVariable conn__tau |])
      ->
      body (SosADL.SosADL.Action (Some (SosADL.SosADL.ComplexName (gd :: conn :: nil)))
                       (Some (SosADL.SosADL.ReceiveAction (Some x))) :: l)
           well typed in Gamma

| type_SendStatement_Out:
    forall Gamma gd E conn conn__tau e tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection SosADL.SosADL.ModeTypeOut conn__tau))
      /\ (expression e has type tau in Gamma)
      /\ (tau </ conn__tau under Gamma)
      /\ (body l well typed in Gamma)
      ->
      body (SosADL.SosADL.Action (Some (SosADL.SosADL.ComplexName (gd :: conn :: nil)))
                       (Some (SosADL.SosADL.SendAction (Some e))) :: l)
           well typed in Gamma

| type_SendStatement_InOut:
    forall Gamma gd E conn conn__tau e tau l,
      (contains Gamma gd (EGateOrDuty E))
      /\ (contains E conn (GDConnection SosADL.SosADL.ModeTypeInout conn__tau))
      /\ (expression e has type tau in Gamma)
      /\ (tau </ conn__tau under Gamma)
      /\ (body l well typed in Gamma)
      ->
      body (SosADL.SosADL.Action (Some (SosADL.SosADL.ComplexName (gd :: conn :: nil)))
                       (Some (SosADL.SosADL.SendAction (Some e))) :: l)
           well typed in Gamma

| type_DoExpr:
    forall Gamma e tau l,
      (expression e has type tau in Gamma)
      /\ (body l well typed in Gamma)
      ->
      body (SosADL.SosADL.BehaviorStatement_DoExpr (Some e) :: l) well typed in Gamma

| type_Done:
    forall Gamma,
      body (SosADL.SosADL.BehaviorStatement_Done :: nil) well typed in Gamma


where "'typedecl' t 'well' 'typed' 'in' Gamma" := (type_datatypeDecl Gamma t)
and "'functions' 'of' 'typedecl' t 'well' 'typed' 'in' Gamma" := (type_datatypeDecl_functions Gamma t)
and "'function' f 'well' 'typed' 'in' Gamma" := (type_function Gamma f)
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

Definition type_datatypeDecls Gamma l Gamma1 := @incrementally _ type_datatypeDecl SosADL.SosADL.DataTypeDecl_name (fun x => Some (EType x)) Gamma l Gamma1.
Definition type_functionDecls Gamma l Gamma1 := @incrementally _ type_function SosADL.SosADL.FunctionDecl_name (fun x => Some (EFunction x)) Gamma l Gamma1.
Definition type_mediators Gamma l Gamma1 := @incrementally _ type_mediator SosADL.SosADL.MediatorDecl_name (fun x => Some (EMediator x)) Gamma l Gamma1.
Definition type_architectures Gamma l Gamma1 := @incrementally _ type_architecture SosADL.SosADL.ArchitectureDecl_name (fun x => Some (EArchitecture x)) Gamma l Gamma1.
Definition formalParameter_to_EVariable p :=
  match SosADL.SosADL.FormalParameter_type p with
  | None => None
  | Some t => Some (EVariable t)
  end.
Definition type_formalParameters Gamma l Gamma1 :=
  @mutually _ (fun gamma p _ =>
                 exists t,
                   SosADL.SosADL.FormalParameter_type p = Some t
                   /\ type t well typed in Gamma)
            SosADL.SosADL.FormalParameter_name
            formalParameter_to_EVariable
            Gamma l Gamma1.
Definition type_gates Gamma l Gamma1 := @incrementally _ type_gate SosADL.SosADL.GateDecl_name (fun x => (** TODO *) None) Gamma l Gamma1.

(** ** System *)

(** %\note{%By choice, the elements declared in the system are typed
in order by the set rules for [type_systemblock].%}% *)

Inductive type_system: env -> SosADL.SosADL.t_SystemDecl -> Prop :=
| type_SystemDecl:
    forall
      (Gamma: env)
      (name: string)
      (params: list SosADL.SosADL.t_FormalParameter)
      (Gamma1: env)
      (datatypes: list SosADL.SosADL.t_DataTypeDecl)
      (Gamma2: env)
      (gates: list SosADL.SosADL.t_GateDecl)
      (Gamma3: env)
      (bhv: SosADL.SosADL.t_BehaviorDecl)
      (assrt: option SosADL.SosADL.t_AssertionDecl)
      (p1: type_formalParameters Gamma params Gamma1)
      (p2: type_datatypeDecls Gamma1 datatypes Gamma2)
      (p3: type_gates Gamma2 gates Gamma3)
      (p4: behavior bhv well typed in Gamma3)
      (p5: @optionally _ (fun g a => assertion a well typed in g) Gamma3 assrt)
    ,
      system (SosADL.SosADL.SystemDecl (Some name) params datatypes gates (Some bhv) assrt) well typed in Gamma
where "'system' s 'well' 'typed' 'in' Gamma" := (type_system Gamma s)
.

Definition type_systems Gamma l Gamma1 := @incrementally _ type_system SosADL.SosADL.SystemDecl_name (fun x => Some (ESystem x)) Gamma l Gamma1.

(** ** Entity *)

(** %\note{%We choose that the order of the declaration is
significant for the typing rules. Namely, the scope of a declaration
starts after this declaration and spans until the end of the enclosing
block. This choice prevents, e.g., (mutually) recursive
declarations. This behavior is implemented by the following rules,
each of which exhausts of list of declarations in order.%}% *)

Inductive type_entityBlock: env -> SosADL.SosADL.t_EntityBlock -> Prop :=
| type_EntityBlock_whole:
    forall
      (Gamma: env)
      (datatypes: list SosADL.SosADL.t_DataTypeDecl)
      (Gamma1: env)
      (funs: list SosADL.SosADL.t_FunctionDecl)
      (Gamma2: env)
      (systems: list SosADL.SosADL.t_SystemDecl)
      (Gamma3: env)
      (mediators: list SosADL.SosADL.t_MediatorDecl)
      (Gamma4: env)
      (architectures: list SosADL.SosADL.t_ArchitectureDecl)
      (Gamma5: env)
      (p1: type_datatypeDecls Gamma datatypes Gamma1)
      (p2: type_functionDecls Gamma1 funs Gamma2)
      (p3: type_systems Gamma2 systems Gamma3)
      (p4: type_mediators Gamma3 mediators Gamma4)
      (p5: type_architectures Gamma4 architectures Gamma5)
    ,
      entity (SosADL.SosADL.EntityBlock datatypes funs systems mediators architectures) well typed in Gamma
  
where "'entity' u 'well' 'typed' 'in' Gamma" := (type_entityBlock Gamma u)
.

(**
 ** Compilation unit

The two forms of compulation unit (SoS or library) are handled in the
same way by the typing rules.  *)

(** %\note{%The environment is added in anticipation of the handling of the imports.%}% *)

Inductive type_unit: env -> SosADL.SosADL.t_Unit -> Prop :=
| type_SoS:
    forall (Gamma: env)
           (n: string)
           (e: SosADL.SosADL.t_EntityBlock)
           (p: entity e well typed in Gamma)
    ,
      unit (SosADL.SosADL.SoS (Some n) (Some e)) well typed in Gamma

| type_Library:
    forall (Gamma: env)
           (n: string)
           (e: SosADL.SosADL.t_EntityBlock)
           (p: entity e well typed in Gamma)
    ,
      unit (SosADL.SosADL.Library (Some n) (Some e)) well typed in Gamma
where "'unit' u 'well' 'typed' 'in' Gamma" := (type_unit Gamma u)
.

(**
 ** SoS architecture

%\todo{%The import list is currently ignored.%}%
 *)

Inductive type_sosADL: SosADL.SosADL.t_SosADL -> Prop :=
| type_SosADL:
    forall (i: list SosADL.SosADL.t_Import)
           (d: SosADL.SosADL.t_Unit)
           (p: unit d well typed in empty)
    ,
      SoSADL (SosADL.SosADL.SosADL i (Some d)) well typed
where "'SoSADL' a 'well' 'typed'" := (type_sosADL a)
.

