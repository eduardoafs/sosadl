Require Import List.
Require Import String.
Require SosADL.sosADL.
Require SosADL.SosADL.
Require SosADL.Accessors.
Require Import SosADL.Environment.
Require Import SosADL.Utils.
Require Import SosADL.Interpretation.
Require Import BinInt.

(** printing Delta $\Delta$ #&Delta;# *)
(** printing Phi $\Phi$ #&Phi;# *)
(** printing Gamma $\Gamma$ #&Gamma;# *)
(** printing Gamma1 $\Gamma_1$ #&Gamma;1# *)
(** printing Gamma2 $\Gamma_2$ #&Gamma;2# *)
(** printing Gamma3 $\Gamma_3$ #&Gamma;3# *)
(** printing Gamma4 $\Gamma_4$ #&Gamma;4# *)
(** printing Gamma5 $\Gamma_5$ #&Gamma;5# *)
(** printing Gammap $\Gamma_p$ #&Gamma;p# *)
(** printing Gammav $\Gamma_v$ #&Gamma;v# *)
(** printing tau $\tau$ #&tau;# *)
(** printing tau__e $\tau_e$ #&tau;<sub>e</sub># *)
(** printing tau__f $\tau_f$ #&tau;<sub>f</sub># *)
(** printing tau__x $\tau_x$ #&tau;<sub>x</sub># *)
(** printing Pi $\Pi$ #&Pi;# *)
(** printing empty $\emptyset$ #&empty;# *)
(** printing </ $\subseteq$ #&sube;# *)
(** printing False $\bot$ #&perp;# *)
(** printing conn__tau $conn_{\tau}$ #conn<sub>&tau;</sub># *)
(** printing l__tau $l_{\tau}$ #l<sub>&tau;</sub># *)
(** printing r__tau $r_{\tau}$ #r<sub>&tau;</sub># *)
(** printing l__min $l_{min}$ #l<sub>min</sub># *)
(** printing l__max $l_{max}$ #l<sub>max</sub># *)
(** printing r__min $r_{min}$ #r<sub>min</sub># *)
(** printing r__max $r_{max}$ #r<sub>max</sub># *)
(** printing r_min $r_{min}$ #r<sub>min</sub># *)
(** printing r_max $r_{max}$ #r<sub>max</sub># *)
(** printing x__min $x_{min}$ #x<sub>min</sub># *)
(** printing x__max $x_{max}$ #x<sub>max</sub># *)
(** printing x__min_ $x_{min'}$ #x<sub>min'</sub># *)
(** printing x__max_ $x_{max'}$ #x<sub>max'</sub># *)
(** printing x_min $x_{min}$ #x<sub>min</sub># *)
(** printing x_max $x_{max}$ #x<sub>max</sub># *)
(** printing x_min_ $x_{min'}$ #x<sub>min'</sub># *)
(** printing x_max_ $x_{max'}$ #x<sub>max'</sub># *)

(**
%
\def\todo#1{{\color{red}TODO: #1}}
\def\note#1{{\color{blue}NOTE: #1}}
\def\deprecated#1{{\color{purple}DEPRECATED: #1}}
%
 *)

(**

The definition of the type system is structured in several
pieces. First come the definition of the environment, which is a map
from (bound) names to type information. Then come few helper
definitions in order to ease dealing with connections, methods and
tuple fields. The helper definitions provides the semantics for
resolution. They are followed by a definition for subtyping. Next come
a couple of generic meta-judgments and meta-rules that capture some
specific patterns. A simple notion for constant expressions is then
defined before the typing judgments.

 *)

(** * Environment

An environment captures the type information for bound names. Its
management implements scoping, visibility and masking.

We choose to have a single environment for all the kinds of objects,
hence to have a single namespace. The following type describes all the
objects that can be stored in the typing environment. The main kinds of objects are:

- [EType]: data type declaration and its associated methods
- [ESystem], [EMediator] and [EArchitecture]: declaration of an architectural entity
- [EGateOrDuty]: list of connections for a gate or a duty
- [EVariable]: value-storing variable
- [EConnection] a single connection, within a gate or a duty

%\note{%The type system implements structural subtyping. This is the reason why each data type declaration is stored in the environment with a substituting type.%}%

 *)

Inductive env_content: Type :=
| EType: SosADL.SosADL.t_DataTypeDecl -> SosADL.SosADL.t_DataType
         -> list SosADL.SosADL.t_FunctionDecl -> env_content
| ESystem: SosADL.SosADL.t_SystemDecl -> env_content
| EMediator: SosADL.SosADL.t_MediatorDecl -> env_content
| EArchitecture: SosADL.SosADL.t_ArchitectureDecl -> env_content
| EGateOrDuty: list SosADL.SosADL.t_Connection -> env_content
| EVariable: SosADL.SosADL.t_DataType -> env_content
| EConnection: SosADL.SosADL.t_Connection -> env_content.

Definition env := environment env_content.

(**
 * Utilities
 *)

(**
 ** Communication helpers
 *)

(** The [connection_defined] predicate states that a connection with
given properties (name, mode, type and environment) exists in a given
list.

%\note{%The predicate is expressed as the existence of a rank [i] at
 which the connection is assumed to exist in the given list. This
 approach simplifies the generation of the proof, which is here a pair
 of an integer and an [eq_refl] value.%}%
*)

Definition connection_defined
           (l: list SosADL.SosADL.t_Connection)
           (is_env: bool)
           (conn: string)
           (mode: SosADL.SosADL.ModeType)
           (tau: SosADL.SosADL.t_DataType)
  := exists (i: Z), match List.nth_error l (Z.to_nat i) with
               | Some c => c = SosADL.SosADL.Connection
                                (Some is_env) (Some conn) (Some mode) (Some tau)
               | None => False
               end.

(**The [type_connectionname] predicate states that a connection with
given properties (complex name, mode, type and environment) exists in
a given environment. The complex name can either be the fully qualified name
(gate-or-duty, name pair) or a singleton name.
*)

Inductive type_connectionname:
  env -> SosADL.SosADL.t_ComplexName -> bool
  -> SosADL.SosADL.ModeType -> SosADL.SosADL.t_DataType -> Prop :=
  
| type_connectionname_qualified:
    forall (Gamma: env)
      (gd: string)
      (endpoints: list SosADL.SosADL.t_Connection)
      (is_env: bool)
      (conn: string)
      (mode: SosADL.SosADL.ModeType)
      (conn__tau: SosADL.SosADL.t_DataType)
      (p1: contains Gamma gd (EGateOrDuty endpoints))
      (p2: connection_defined endpoints is_env conn mode conn__tau)
    ,
      type_connectionname Gamma (SosADL.SosADL.ComplexName (cons gd (cons conn nil))) is_env mode conn__tau

| type_connectionname_simple:
    forall (Gamma: env)
      (is_env: bool)
      (conn: string)
      (mode: SosADL.SosADL.ModeType)
      (conn__tau: SosADL.SosADL.t_DataType)
      (p1: contains Gamma conn (EConnection
                                  (SosADL.SosADL.Connection
                                     (Some is_env) (Some conn) (Some mode) (Some conn__tau))))
    ,
      type_connectionname Gamma (SosADL.SosADL.ComplexName (cons conn nil)) is_env mode conn__tau
.


(** [mode_send] and [mode_receive] state the valid connection modes
for sending and receiving data, respectively.  *)

Inductive mode_send: SosADL.SosADL.ModeType -> Prop :=
| mode_send_out: mode_send SosADL.SosADL.ModeTypeOut
| mode_send_inout: mode_send SosADL.SosADL.ModeTypeInout.

Inductive mode_receive: SosADL.SosADL.ModeType -> Prop :=
| mode_receive_in: mode_receive SosADL.SosADL.ModeTypeIn
| mode_receive_inout: mode_receive SosADL.SosADL.ModeTypeInout.

(**
 ** Method helpers
 *)

(** The [method_defined] predicate states that a method with given
name, self type, return type and formal parameters exist in a given
list of function declarations. [method_defined'] and
[method_defined''] are semantically-equivalent alternative definitions
for this predicate. Their equivalence can be proved. *)

Definition method_defined'
           (m: string)
           (l: list SosADL.SosADL.t_FunctionDecl)
           (tau: SosADL.SosADL.t_DataType)
           (f: list SosADL.SosADL.t_FormalParameter)
           (r: SosADL.SosADL.t_DataType)
  := List.Exists (fun fd =>
                    match SosADL.Accessors.FunctionDecl_data fd with
                    | Some fp => SosADL.Accessors.FormalParameter_type fp
                    | None => None
                    end = Some tau
                    /\ SosADL.Accessors.FunctionDecl_name fd = Some m
                    /\ SosADL.Accessors.FunctionDecl_parameters fd = f
                    /\ SosADL.Accessors.FunctionDecl_type fd = Some r)
                 l.

Definition method_defined''
           (m: string)
           (l: list SosADL.SosADL.t_FunctionDecl)
           (tau: SosADL.SosADL.t_DataType)
           (f: list SosADL.SosADL.t_FormalParameter)
           (r: SosADL.SosADL.t_DataType)
  := exists (i: nat), match List.nth_error l i with
               | Some fd =>
                 match SosADL.Accessors.FunctionDecl_data fd with
                 | Some fp => SosADL.Accessors.FormalParameter_type fp
                 | None => None
                 end = Some tau
                 /\ SosADL.Accessors.FunctionDecl_name fd = Some m
                 /\ SosADL.Accessors.FunctionDecl_parameters fd = f
                 /\ SosADL.Accessors.FunctionDecl_type fd = Some r
               | None => False
               end.

Definition method_defined
           (m: string)
           (l: list SosADL.SosADL.t_FunctionDecl)
           (tau: SosADL.SosADL.t_DataType)
           (f: list SosADL.SosADL.t_FormalParameter)
           (r: SosADL.SosADL.t_DataType)
  := exists (i: Z), match List.nth_error l (Z.to_nat i) with
               | Some fd =>
                 match SosADL.Accessors.FunctionDecl_data fd with
                 | Some fp => SosADL.Accessors.FormalParameter_type fp
                 | None => None
                 end = Some tau
                 /\ SosADL.Accessors.FunctionDecl_name fd = Some m
                 /\ SosADL.Accessors.FunctionDecl_parameters fd = f
                 /\ SosADL.Accessors.FunctionDecl_type fd = Some r
               | None => False
               end.

Notation "'method' m 'defined' 'in' d 'with' tau 'parameters' f 'returns' r" :=
  (method_defined m d tau f r)
    (at level 200, no associativity).

(**
 ** Field helpers
 *)

(** [field_has_type] is a predicate that looks for a field with given
name and type in a list of field declarations. *)

Inductive field_has_type:
  list SosADL.SosADL.t_FieldDecl -> string -> SosADL.SosADL.t_DataType -> Prop :=
| First_Field:
    forall n t r,
      field_has_type (SosADL.SosADL.FieldDecl (Some n) (Some t) :: r) n t
                     
| Next_Field:
    forall n t h r,
      field_has_type r n t -> field_has_type (h :: r) n t.

(** [field_type] is a function that returns the type of a field given
by its name. *)

Fixpoint field_type (l: list SosADL.SosADL.t_FieldDecl) (n: string) {struct l}:
  option SosADL.SosADL.t_DataType :=
  match l with
  | nil => None
  | (SosADL.sosADL.sosADL_FieldDecl_sosADL_FieldDecl (Some f) r) :: tl =>
    if string_dec n f then r else field_type tl n
  | _ :: tl => field_type tl n
  end.


(** * Subtyping relation *)

Reserved Notation "t1 </ t2" (at level 70).

(** The [subtype] relation states whenever a type is included in
another type. Inclusion is here understood as the inclusion of the
sets of values corresponding to the types, which is especially
meaningful for range types. Tuple and sequence types are covariant.
Moreover, a tuple type is included in another tuple type if and only
if it declares the same fields possibly with additional ones.

%\note{%The [subtype] relation, like the reminder of the type system,
 implements structural subtyping. This is the reason why no subtyping
 rule applies to named types, except [subtype_refl], the reflectivity
 rule.%}% *)

Inductive subtype:
  SosADL.SosADL.t_DataType -> SosADL.SosADL.t_DataType -> Prop :=
  
| subtype_refl:
    forall
      (t: SosADL.SosADL.t_DataType)
    ,
      t </ t

| subtype_range:
    forall
      (lmi: SosADL.SosADL.t_Expression)
      (lma: SosADL.SosADL.t_Expression)
      (rmi: SosADL.SosADL.t_Expression)
      (rma: SosADL.SosADL.t_Expression)
      (p1: rmi <= lmi)
      (p2: lma <= rma)
    ,
      (SosADL.SosADL.RangeType (Some lmi) (Some lma))
        </ (SosADL.SosADL.RangeType (Some rmi) (Some rma))

| subtype_tuple:
    forall (l: list SosADL.SosADL.t_FieldDecl)
      (r: list SosADL.SosADL.t_FieldDecl)
      (p1: for each f of r,
           exists n,
             SosADL.Accessors.FieldDecl_name f = Some n
             /\ exists tr,
               SosADL.Accessors.FieldDecl_type f = Some tr
               /\ exists tl, field_type l n = Some tl
                       /\ (tl </ tr))
    ,
      (SosADL.SosADL.TupleType l) </ (SosADL.SosADL.TupleType r)

| subtype_sequence:
    forall (l: SosADL.SosADL.t_DataType)
      (r: SosADL.SosADL.t_DataType)
      (p1: l </ r)
    ,
      (SosADL.SosADL.SequenceType (Some l))
        </ (SosADL.SosADL.SequenceType (Some r))

where "t1 </ t2" := (subtype t1 t2)
.

(** * Generic constructions

The following definitions provide generic constructions for the type
system, especially to deal with definitions and with optionality.

[augment_env] is a function that optionally binds a new name in an
environment.  *)

Definition augment_env (Gamma: env) (n: option string) (c: option env_content) :=
  match n with
  | None => Gamma
  | Some name =>
    match c with
    | None => Gamma
    | Some content => Gamma [| name <- content |]
    end
  end.

(** [incrementally] is a generic set of rules for incremental ordered
definitions, i.e., each definition can be used in subsequent
definitions. [incrementally] can be proved to fold the list in the
same way as [fold_left]. *)

Inductive incrementally
          {T: Type} {P: env -> T -> env -> Prop}:
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
      (Gammai: env)
      (l: list T)
      (Gamma1: env)
      (p1: P Gamma x Gammai)
      (p2: incrementally Gammai l Gamma1)
    ,
      incrementally Gamma (x::l) Gamma1
.

(** A [simple_increment] is to be used in conjunction with
[incrementally] in order to implement its [P] parameter when it made
of a proof of an (arbitrary) property along with a call to
[augment_env]. *)

Inductive simple_increment
          (T: Type) (P: env -> T -> Prop) (name: T -> option string)
          (content: T -> option env_content):
  env -> T -> env -> Prop :=

| simple_increment_step:
    forall
      (Gamma: env)
      (x: T)
      (Gamma1: env)
      (p1: Gamma1 = augment_env Gamma (name x) (content x))
      (p2: P Gamma x)
    ,
      simple_increment T P name content Gamma x Gamma1
.

(** [augment_env_with_all] binds a list of names in an
environment. This function is intended to be used in conjunction with
[mutually]: it assumes that the order in which the names are bound is
irrelevant.

%\note{%The implementation uses [fold_right] because it is
 tail-recursive.%}% *)

Definition augment_env_with_all
           (Gamma: env) {T: Type} (name: T -> option string)
           (content: T -> option env_content) (l: list T) :=
  List.fold_right (fun x g => augment_env g (name x) (content x)) Gamma l.

(** [mutually] is a generic rule for unordered, simultaneous, mutual
definitions that can refer to each other. *)

Inductive mutually
          {T: Type} {P: env -> T -> env -> Prop} {name: T -> option string}
          {content: T -> option env_content}:
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

(** [mutually_translate] is a generic rule for unordered,
simultaneous, mutual definitions that can refer to each other. The
difference between [mutually] and [mutually_translate] is that the
latter offers the opportunity to translate the items added to the
environment. *)

Inductive mutually_translate
          {T: Type} {P: env -> T -> T -> env -> Prop} {name: T -> option string}
          {content: T -> option env_content}:
  env -> list T -> list T -> env -> Prop :=

| mutually_translate_all:
    forall
      (Gamma: env)
      (l: list T)
      (l1: list T)
      (Gamma1: env)
      (p1: (augment_env_with_all Gamma name content l1) = Gamma1)
      (p2: values (name x) for x of l1 are distinct according to option_string_dec)
      (p3: for each x x1 of l l1, (name x) = (name x1) /\ P Gamma x x1 Gamma1)
    ,
      mutually_translate Gamma l l1 Gamma1
.

(** [optionally] is a generic rule that proves an optional
statement. *)

Inductive optionally {T: Type} {P: env -> T -> Prop}:
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

(** * Notations

** Judgements

The following notations define all the judgment forms in the type
system. Usually, the environment is denoted [Gamma].  *)

Reserved Notation "'expression' e 'is' 'constant' 'integer'"
         (at level 200, no associativity).
Reserved Notation "'SoSADL' a 'well' 'typed'" (at level 200, no associativity).
Reserved Notation "'unit' u 'well' 'typed' 'in' Gamma" (at level 200, no associativity).
Reserved Notation "'entity' u 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'typedecl' t 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'function' f 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'type' t 'looks' 'fine'" (at level 200, no associativity).
Reserved Notation "'type' t 'is' u 'in' Gamma"
         (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'system' s 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'mediator' m 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'architecture' a 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'architectureblock' a 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'expression' e 'has' 'type' t 'in' Gamma"
         (at level 200, no associativity, Gamma at level 1).
Reserved Notation "'expression' 'node' e 'has' 'type' t 'in' Gamma"
         (at level 200, no associativity, Gamma at level 1).
Reserved Notation "'archbehavior' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'behavior' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'assertion' a 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'protocol' p 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'final' 'protocol' p 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'nonfinal' 'protocol' p 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'protocol' 'statement' s 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1"
         (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'final' 'body' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'statement' b 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'nonfinal' 'body' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).

(**
 ** SoSADL notations
 *)

(** The [sosadl_scope] notation scope and [%sosadl] key are used to
provide convenient notations for SoSADL expressions.  *)

Import ListNotations.
Require Import SosADLNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Delimit Scope sosadl_scope with sosadl.

(**
 * The type system
 *)

(** In the following rules, each inductive type gathers the rules for
a single form of judgment. Rules are built of the following:

- a rule name, here used as the name of the constructor in the inductive type;
- universal quantification of the free names of the rules;
- premises of the rule appear as additional parameters whose name usually starts with [p]; and
- conclusion of the rule appear below the [,].
 *)

(**
 ** Constant expressions
 *)

(** The [constexpr_expression] predicate states that an expression is
manifestly constant. It is based on a syntactical criterion.

%\deprecated{%The criterion is overly strict as it does not allow (for
 instance) the use of literal tuples nor sequences. This predicate is
 not used in the type system.%}% *)

Inductive constexpr_expression: SosADL.SosADL.t_Expression -> Prop :=
| constexpr_IntegerValue:
    forall
      (v: BinInt.Z)
    ,
      expression (# v)%sosadl is constant integer

| constexpr_Opposite:
    forall
      (e: SosADL.SosADL.t_Expression)
      (p: expression e is constant integer)
    ,
      expression (- e)%sosadl is constant integer

| constexpr_Same:
    forall
      (e: SosADL.SosADL.t_Expression)
      (p: expression e is constant integer)
    ,
      expression (+ e)%sosadl is constant integer

| constexpr_Add:
    forall
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: expression l is constant integer)
      (p2: expression r is constant integer)
    ,
      expression (l + r)%sosadl is constant integer

| constexpr_Sub:
    forall
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: expression l is constant integer)
      (p2: expression r is constant integer)
    ,
      expression (l - r)%sosadl is constant integer

| constexpr_Mul:
    forall
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: expression l is constant integer)
      (p2: expression r is constant integer)
    ,
      expression (l * r)%sosadl is constant integer

| constexpr_Div:
    forall
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: expression l is constant integer)
      (p2: expression r is constant integer)
    ,
      expression (l / r)%sosadl is constant integer

| constexpr_Mod:
    forall
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: expression l is constant integer)
      (p2: expression r is constant integer)
    ,
      expression (l mod r)%sosadl is constant integer
                 
where "'expression' e 'is' 'constant' 'integer'" := (constexpr_expression e)
.

(** ** Data types

The [check_datatype] predicate asserts that a data type is valid. A
data type is said valid if and only if, when it is a range type, the
lower bound is smaller than or equal to the upper bound according to
some interpretation. Tuple type and sequence type are valid if the
item types are valid as well. Named type and boolean type are always
valid.

%\note{%In the case of range type, their interpretation ensures that
the bounds are integer.%}% *)

Inductive check_datatype: SosADL.SosADL.t_DataType -> Prop :=
| check_NamedType:
    forall
      (n: string)
    ,
      type (SosADL.SosADL.NamedType (Some n)) looks fine

| check_TupleType:
    forall
      (fields: list SosADL.SosADL.t_FieldDecl)
      (p1: values (SosADL.Accessors.FieldDecl_name f) for f of fields
                  are distinct according to option_string_dec)
      (p2: for each f of fields,
           exists t, (SosADL.Accessors.FieldDecl_type f = Some t
                 /\ type t looks fine))
    ,
      type (SosADL.SosADL.TupleType fields) looks fine

| check_SequenceType:
    forall
      (t: SosADL.SosADL.t_DataType)
      (p: type t looks fine)
    ,
      type (SosADL.SosADL.SequenceType (Some t)) looks fine

| check_RangeType_trivial:
    forall
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: min <= max)
    ,
      type [min, max]%sosadl looks fine

| check_BooleanType:
      type SosADL.SosADL.BooleanType looks fine

where "'type' t 'looks' 'fine'" := (check_datatype t)
.

(** [type_datatype] is a predicate that asserts that a data type is
correct in a given environment and that, according to this
environment, it should be substituted by a given data type.

Substitution occurs recursively in the data type. Whenever a named
type is found, it is substituted as found in the environment.

%\note{%Type substitution is part of the mechanics that implements
 structural typing.%}% *)

Inductive type_datatype:
  env -> SosADL.SosADL.t_DataType -> SosADL.SosADL.t_DataType -> Prop :=
| type_NamedType:
    forall
      (Gamma: env)
      (n: string)
      (u: SosADL.SosADL.t_DataType)
      (t: SosADL.SosADL.t_DataTypeDecl)
      (p: exists m, contains Gamma n (EType t u m))
    ,
      type (SosADL.SosADL.NamedType (Some n)) is u in Gamma

| type_TupleType:
    forall
      (Gamma: env)
      (fields: list SosADL.SosADL.t_FieldDecl)
      (fields': list SosADL.SosADL.t_FieldDecl)
      (p1: values (SosADL.Accessors.FieldDecl_name f) for f of fields
                  are distinct according to option_string_dec)
      (p2: for each f f' of fields fields',
           SosADL.Accessors.FieldDecl_name f = SosADL.Accessors.FieldDecl_name f'
           /\ exists t, SosADL.Accessors.FieldDecl_type f = Some t
                  /\ exists t', SosADL.Accessors.FieldDecl_type f' = Some t'
                          /\ type t is t' in Gamma)
    ,
      type (SosADL.SosADL.TupleType fields)
           is (SosADL.SosADL.TupleType fields') in Gamma

| type_SequenceType:
    forall
      (Gamma: env)
      (t: SosADL.SosADL.t_DataType)
      (t': SosADL.SosADL.t_DataType)
      (p: type t is t' in Gamma)
    ,
      type (SosADL.SosADL.SequenceType (Some t))
           is (SosADL.SosADL.SequenceType (Some t')) in Gamma

| type_RangeType_trivial:
    forall
      (Gamma: env)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: min <= max)
    ,
      type [min, max]%sosadl is [min, max]%sosadl in Gamma

| type_BooleanType:
    forall
      (Gamma: env)
    ,
      type SosADL.SosADL.BooleanType is SosADL.SosADL.BooleanType in Gamma

where "'type' t 'is' u 'in' Gamma" := (type_datatype Gamma t u)
.

(** ** Expression

Before running into the type system for expressions, we first
introduce some definitions and properties about interval arithmetic,
and more specifically for the [mod] operator:

- [range_modulo_min] asserts the suitable lower bound;
- [range_modulo_max] the suitable upper bound.
 *)

Inductive range_modulo_min:
  SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression
  -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression
  -> SosADL.SosADL.t_Expression -> Prop :=
| range_modulo_min_pos:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (min: SosADL.SosADL.t_Expression)
      (p1: (# 1%Z)%sosadl <= rmin)
      (p2: min <= (# 1%Z - rmax)%sosadl)
    ,
      range_modulo_min lmin lmax rmin rmax min

| range_modulo_min_zero:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (min: SosADL.SosADL.t_Expression)
      (p1: (# 0%Z)%sosadl <= lmin)
      (p2: min <= (# 0%Z)%sosadl)
    ,
      range_modulo_min lmin lmax rmin rmax min

| range_modulo_min_neg:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (min: SosADL.SosADL.t_Expression)
      (p1: rmax <= (- # 1%Z)%sosadl)
      (p2: min <= (rmin + # 1%Z)%sosadl)
    ,
      range_modulo_min lmin lmax rmin rmax min
.

Inductive range_modulo_max:
  SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression
  -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression
  -> SosADL.SosADL.t_Expression -> Prop :=
| range_modulo_max_pos:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: (# 1%Z)%sosadl <= rmin)
      (p2: (rmax - # 1%Z)%sosadl <= max)
    ,
      range_modulo_max lmin lmax rmin rmax max

| range_modulo_max_zero:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: lmax <= (# 0%Z)%sosadl)
      (p2: (# 0%Z)%sosadl <= max)
    ,
      range_modulo_max lmin lmax rmin rmax max

| range_modulo_max_neg:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: rmax <= (- # 1%Z)%sosadl)
      (p2: ((- # 1%Z) - rmin)%sosadl <= max)
    ,
      range_modulo_max lmin lmax rmin rmax max
.

(** [type_expression] asserts that an expression has a given type in a
given environment. This judgment is suitable for computable
expression, i.e., it does not allow [any] nor [unify] operators. It can be used in the following contexts:

- expressions used as range type boundaries;
- expressions in valuings;
- expressions in function bodies;
- expressions in do statements;
- expressions in send statements.

The rules are structured in two sets of mutually recursive judgements:

- [type_expression] is the callable judgement. It checks that the given type is valid as well.
- [type_expression_node] contains the actual typing rules.
 *)

Inductive type_expression_node
          {type_expression: env -> SosADL.SosADL.t_Expression
                            -> SosADL.SosADL.t_DataType -> Prop}:
  env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop :=
                      
| type_expression_IntegerValue:
    forall
      (Gamma: env)
      (v: BinInt.Z)
    ,
      type_expression_node Gamma
                            (# v)%sosadl
                            [# v, # v]%sosadl

| type_expression_Opposite:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma e tau)
      (p2: tau </ [min, max]%sosadl)
    ,
      type_expression_node Gamma
                           (- e)%sosadl
                           [- max, - min]%sosadl

| type_expression_Same:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma e tau)
      (p2: tau </ [min, max]%sosadl)
    ,
      type_expression_node Gamma
                           (+ e)%sosadl
                           [min, max]%sosadl

| type_expression_Not:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (p1: type_expression Gamma e tau)
      (p2: tau </ SosADL.SosADL.BooleanType)
    ,
      type_expression_node Gamma
                           (! e)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_Add:
    forall
      (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
    ,
      type_expression_node Gamma
                           (l + r)%sosadl
                           [ l__min + r__min, l__max + r__max ]%sosadl

| type_expression_Sub:
    forall
      (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
    ,
      type_expression_node Gamma
                           (l - r)%sosadl
                           [ l__min - r__max, l__max - r__min ]%sosadl

| type_expression_Mul:
    forall
      (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
      (p5: min <= (l__min * r__min)%sosadl)
      (p6: min <= (l__min * r__max)%sosadl)
      (p7: min <= (l__max * r__min)%sosadl)
      (p8: min <= (l__max * r__max)%sosadl)
      (p9: (l__min * r__min)%sosadl <= max)
      (pa: (l__min * r__max)%sosadl <= max)
      (pb: (l__max *  r__min)%sosadl <= max)
      (pc: (l__max * r__max)%sosadl <= max)
    ,
      type_expression_node Gamma
                           (l * r)%sosadl
                           [min, max]%sosadl

| type_expression_Div_pos:
    forall
      (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
      (p5: (# 1%Z)%sosadl <= r__min)
      (p6: min <= (l__min / r__min)%sosadl)
      (p7: min <= (l__min / r__max)%sosadl)
      (p8: min <= (l__max / r__min)%sosadl)
      (p9: min <= (l__max / r__max)%sosadl)
      (pa: (l__min / r__min)%sosadl <= max)
      (pb: (l__min / r__max)%sosadl <= max)
      (pc: (l__max / r__min)%sosadl <= max)
      (pd: (l__max / r__max)%sosadl <= max)
    ,
      type_expression_node Gamma
                           (l / r)%sosadl
                           [min, max]%sosadl

| type_expression_Div_neg:
    forall
      (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
      (p5: (r__max <= (- # 1%Z)%sosadl))
      (p6: min <= (l__min / r__min)%sosadl)
      (p7: min <= (l__min / r__max)%sosadl)
      (p8: min <= (l__max / r__min)%sosadl)
      (p9: min <= (l__max / r__max)%sosadl)
      (pa: (l__min / r__min)%sosadl <= max)
      (pb: (l__min / r__max)%sosadl <= max)
      (pc: (l__max / r__min)%sosadl <= max)
      (pd: (l__max / r__max)%sosadl <= max)
    ,
      type_expression_node Gamma
                           (l / r)%sosadl
                           [min, max]%sosadl

| type_expression_Mod:
    forall
      (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
      (p5: range_modulo_min l__min l__max r__min r__max min)
      (p6: range_modulo_max l__min l__max r__min r__max max)
    ,
      type_expression_node Gamma
                           (l mod r)%sosadl
                           [min, max]%sosadl

| type_expression_Implies:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ SosADL.SosADL.BooleanType)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ SosADL.SosADL.BooleanType)
    ,
      type_expression_node Gamma
                           (l -> r)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_Or:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ SosADL.SosADL.BooleanType)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ SosADL.SosADL.BooleanType)
    ,
      type_expression_node Gamma
                           (l || r)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_Xor:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ SosADL.SosADL.BooleanType)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ SosADL.SosADL.BooleanType)
    ,
      type_expression_node Gamma
                           (l ^^ r)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_And:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ SosADL.SosADL.BooleanType)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ SosADL.SosADL.BooleanType)
    ,
      type_expression_node Gamma
                           (l && r)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_Equal:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
    ,
      type_expression_node Gamma
                           (l = r)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_Diff:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
    ,
      type_expression_node Gamma
                           (l <> r)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_Lt:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
    ,
      type_expression_node Gamma
                           (l < r)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_Le:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
    ,
      type_expression_node Gamma
                           (l <= r)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_Gt:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
    ,
      type_expression_node Gamma
                           (l > r)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_Ge:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (l__min: SosADL.SosADL.t_Expression)
      (l__max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (r__min: SosADL.SosADL.t_Expression)
      (r__max: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma l l__tau)
      (p2: l__tau </ [l__min, l__max]%sosadl)
      (p3: type_expression Gamma r r__tau)
      (p4: r__tau </ [r__min, r__max]%sosadl)
    ,
      type_expression_node Gamma
                           (l >= r)%sosadl
                           SosADL.SosADL.BooleanType

| type_expression_Ident:
    forall (Gamma: env)
      (x: string)
      (tau: SosADL.SosADL.t_DataType)
      (p: contains Gamma x (EVariable tau))
    ,
      type_expression_node Gamma
                           (SosADL.SosADL.IdentExpression (Some x))
                           tau

(** %\note{%The rule [type_expression_MethodCall] accept any method
 declaration with the correct name and compatible parameter and [self]
 types. With this definition, the type checker can freely choose any
 such method declaration.%}% *)

| type_expression_MethodCall:
    forall (Gamma: env)
      (self: SosADL.SosADL.t_Expression)
      (t: SosADL.SosADL.t_DataType)
      (typeDecl: SosADL.SosADL.t_DataTypeDecl)
      (tau: SosADL.SosADL.t_DataType)
      (methods: list SosADL.SosADL.t_FunctionDecl)
      (name: string)
      (formalparams: list SosADL.SosADL.t_FormalParameter)
      (ret: SosADL.SosADL.t_DataType)
      (params: list SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma self t)
      (p2: binds Gamma (EType typeDecl tau methods))
      (p4: t </ tau)
      (p5: method name defined in methods
       with tau parameters formalparams returns ret)
      (p6: for each fp p of formalparams params,
           (exists t, SosADL.Accessors.FormalParameter_type fp = Some t
                 /\ (exists tp, (type_expression Gamma p tp)
                          /\ tp </ t)))
    ,
      type_expression_node Gamma
                           (SosADL.SosADL.MethodCall
                              (Some self) (Some name) params)
                           ret

| type_expression_Tuple:
    forall (Gamma: env)
      (elts: list SosADL.SosADL.t_TupleElement)
      (typ: list SosADL.SosADL.t_FieldDecl)
      (p1: values (SosADL.Accessors.TupleElement_label x) for x of elts
                  are distinct according to option_string_dec)
      (p2: for each e f of elts typ,
         SosADL.Accessors.TupleElement_label e = SosADL.Accessors.FieldDecl_name f)
      (p3: for each e f of elts typ,
         (exists (e': SosADL.SosADL.t_Expression),
            SosADL.Accessors.TupleElement_value e = Some e'
            /\ exists (f': SosADL.SosADL.t_DataType),
                SosADL.Accessors.FieldDecl_type f = Some f'
                /\ type_expression Gamma e' f'))
    ,
      type_expression_node Gamma
                           (SosADL.SosADL.Tuple elts)
                           (SosADL.SosADL.TupleType typ)

| type_expression_Field:
    forall (Gamma: env)
      (self: SosADL.SosADL.t_Expression)
      (tau: list SosADL.SosADL.t_FieldDecl)
      (name: string)
      (tau__f: SosADL.SosADL.t_DataType)
      (p1: type_expression Gamma self (SosADL.SosADL.TupleType tau))
      (p2: field_type tau name = Some tau__f)
    ,
      type_expression_node Gamma
                           (self ::: name)%sosadl
                           tau__f

| type_expression_Sequence:
    forall (Gamma: env)
      (elts: list SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (p1: for each e of elts,
           exists t, (type_expression Gamma e t)
                /\ t </ tau)
    ,
      type_expression_node Gamma
                           (SosADL.SosADL.Sequence elts)
                           (SosADL.SosADL.SequenceType (Some tau))

| type_expression_Map:
    forall (Gamma: env)
      (obj: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (x: string)
      (e: SosADL.SosADL.t_Expression)
      (tau__e: SosADL.SosADL.t_DataType)
      (p1: type_expression Gamma obj (SosADL.SosADL.SequenceType (Some tau)))
      (p2: type_expression (Gamma [| x <- EVariable tau |]) e tau__e)
    ,
      type_expression_node Gamma
                           (obj :: { x -> e})%sosadl
                           (SosADL.SosADL.SequenceType (Some tau__e))

| type_expression_Select:
    forall (Gamma: env)
      (obj: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (x: string)
      (e: SosADL.SosADL.t_Expression)
      (p1: type_expression Gamma obj (SosADL.SosADL.SequenceType (Some tau)))
      (p2: type_expression (Gamma [| x <- EVariable tau |]) e SosADL.SosADL.BooleanType)
    ,
      type_expression_node Gamma
                           (obj :: { x | e})%sosadl
                           (SosADL.SosADL.SequenceType (Some tau))

.

Inductive type_expression:
  env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop :=
  
| type_expression_and_type:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (t: SosADL.SosADL.t_DataType)
      (p1: @type_expression_node type_expression Gamma e t)
      (p2: type t looks fine)
    ,
      expression e has type t in Gamma
where "'expression' e 'has' 'type' t 'in' Gamma" := (type_expression Gamma e t)
.

(** ** Valuings *)

(** In a list, the valuings are handled one after the other, using
[incrementally].

When the type of a valuing is missing, the computed type of the
expression is used instead.  *)

Inductive type_valuing
          {type_expression': env -> SosADL.SosADL.t_Expression
                             -> SosADL.SosADL.t_DataType -> Prop}:
  env -> SosADL.SosADL.t_Valuing -> env -> Prop :=

| type_Valuing_typed:
    forall (Gamma: env)
      (x: string)
      (tau: SosADL.SosADL.t_DataType)
      (tau1: SosADL.SosADL.t_DataType)
      (e: SosADL.SosADL.t_Expression)
      (tau__e: SosADL.SosADL.t_DataType)
      (p1: type_expression' Gamma e tau__e)
      (p2: tau__e </ tau1)
      (p3: type tau is tau1 in Gamma)
    ,
      type_valuing Gamma
                   (valuing x is tau = e)%sosadl
                   (Gamma [| x <- EVariable tau1 |])

| type_Valuing_inferred:
    forall (Gamma: env)
      (x: string)
      (e: SosADL.SosADL.t_Expression)
      (tau__e: SosADL.SosADL.t_DataType)
      (p1: type_expression' Gamma e tau__e)
    ,
      type_valuing Gamma
                   (valuing x = e)%sosadl
                   (Gamma [| x <- EVariable tau__e |])
.

Definition type_valuings
           {type_expression': env -> SosADL.SosADL.t_Expression
                              -> SosADL.SosADL.t_DataType -> Prop}
           Gamma l Gamma1 :=
  @incrementally _ (fun g e g1 => @type_valuing type_expression' g e g1)
                 Gamma l Gamma1.

(** ** Conditional statements *)

(** Unless conditional statements update the environment in each
branch according to the tests being evaluated, range types are almost
impractical. [condition_true] and [condition_false] aim at specifying
a (rather naive) strategy to do this. These judgments rely on
[smallest] (respectively [greatest]), which asserts that an expression
is the minimum (respectively the maximum) of two given expression. *)

Inductive smallest:
  SosADL.SosADL.t_Expression
  -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> Prop :=
| smallest_l:
    forall (m: SosADL.SosADL.t_Expression)
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: l <= m)
      (p2: l <= r)
    ,
      smallest m l r
| smallest_r:
    forall (m: SosADL.SosADL.t_Expression)
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: r <= m)
      (p2: r <= l)
    ,
      smallest m l r
.

Inductive greatest:
  SosADL.SosADL.t_Expression
  -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> Prop :=
| greatest_l:
    forall (m: SosADL.SosADL.t_Expression)
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: m <= l)
      (p2: r <= l)
    ,
      greatest m l r
| greatest_r:
    forall (m: SosADL.SosADL.t_Expression)
      (l: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (p1: m <= r)
      (p2: l <= r)
    ,
      greatest m l r
.

(** [negated_comparison] returns the negation of a given comparison
operator. *)

Definition negated_comparison op :=
  match op with
  | "<" => Some ">="
  | "<=" => Some ">"
  | ">" => Some "<="
  | ">=" => Some "<"
  | "=" => Some "<>"
  | "<>" => Some "="
  | _ => None
  end.

(** [symmetric_comparison] returns the symmetric operator of a given
comparison operator. *)

Definition symmetric_comparison op :=
  match op with
  | "<" => Some ">"
  | "<=" => Some ">="
  | ">" => Some "<"
  | ">=" => Some "<="
  | "=" => Some "="
  | "<>" => Some "<>"
  | _ => None
  end.

(**
- [condition_true] asserts the environment in the [then] branch of a conditional statement, i.e., assuming that a given condition evaluates to [true].
- [condition_false] is similar to [condition_true], but for the [then] branch of a conditional statement, i.e., assuming that a given condition evaluates to [false].

The supported condition forms are:
- comparisons;
- negation;
- in [condition_true]: conjunction;
- in [condition_false]: disjunction.

Whenever a condition [x <= y] is found to surely hold in the branch, when [x] and [y] are variables, [x] and [y] are rebound such that the upper bound of [x] is updated to the upper bound of [y], and the lower bound of [y] is updated to the lower bound of [x]. The algorithm proceeds in the same way when either [x] or [y] is not a variable.

%\note{%The non-determinism in the rules can make the algorithm never terminate, due to [condition_true_sym]. Though, it is quite easy to derive an effective algorithm from the rules.%}%
*)

Inductive condition_true: env -> SosADL.SosADL.t_Expression -> env -> Prop :=
| condition_true_general:
    forall (Gamma: env)
      (c: SosADL.SosADL.t_Expression)
    ,
      condition_true Gamma c Gamma

| condition_true_not:
    forall (Gamma: env)
      (c: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: condition_false Gamma c Gamma1)
    ,
      condition_true Gamma (! c)%sosadl Gamma

| condition_true_and:
    forall (Gamma: env)
      (c1: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (c2: SosADL.SosADL.t_Expression)
      (Gamma2: env)
      (p1: condition_true Gamma c1 Gamma1)
      (p2: condition_true Gamma1 c2 Gamma2)
    ,
      condition_true Gamma (c1 && c2)%sosadl Gamma2

| condition_true_lt:
    forall (Gamma: env)
      (x: string)
      (x_min: SosADL.SosADL.t_Expression)
      (x_max: SosADL.SosADL.t_Expression)
      (x_max_: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r_min: SosADL.SosADL.t_Expression)
      (r_max: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: expression (SosADL.SosADL.IdentExpression (Some x))
                      has type [x_min, x_max]%sosadl in Gamma)
      (p2: expression r has type [r_min, r_max]%sosadl in Gamma)
      (p3: smallest x_max_
                    x_max (r_max - # 1%Z)%sosadl)
      (p4: type [x_min, x_max_]%sosadl looks fine)
      (p5: condition_true (Gamma [| x <- EVariable [x_min, x_max_]%sosadl |])
                          (r > (SosADL.SosADL.IdentExpression (Some x)))%sosadl
                          Gamma1)
    ,
      condition_true Gamma ((SosADL.SosADL.IdentExpression (Some x)) < r)%sosadl Gamma1

| condition_true_le:
    forall (Gamma: env)
      (x: string)
      (x_min: SosADL.SosADL.t_Expression)
      (x_max: SosADL.SosADL.t_Expression)
      (x_max_: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r_min: SosADL.SosADL.t_Expression)
      (r_max: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: expression (SosADL.SosADL.IdentExpression (Some x))
                      has type [x_min, x_max]%sosadl in Gamma)
      (p2: expression r has type [r_min, r_max]%sosadl in Gamma)
      (p3: smallest x_max_ x_max r_max)
      (p4: type [x_min, x_max_]%sosadl looks fine)
      (p5: condition_true (Gamma [| x <- EVariable [x_min, x_max_]%sosadl |])
                          (r >= (SosADL.SosADL.IdentExpression (Some x)))%sosadl
                          Gamma1)
    ,
      condition_true Gamma ((SosADL.SosADL.IdentExpression (Some x)) <= r)%sosadl Gamma1

| condition_true_eq:
    forall (Gamma: env)
      (x: string)
      (x_min: SosADL.SosADL.t_Expression)
      (x_min_: SosADL.SosADL.t_Expression)
      (x_max: SosADL.SosADL.t_Expression)
      (x_max_: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r_min: SosADL.SosADL.t_Expression)
      (r_max: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: expression (SosADL.SosADL.IdentExpression (Some x))
                      has type [x_min, x_max]%sosadl in Gamma)
      (p2: expression r has type [r_min, r_max]%sosadl in Gamma)
      (p3: greatest x_min_ x_min r_min)
      (p4: smallest x_max_ x_max r_max)
      (p5: type [x_min_, x_max_]%sosadl looks fine)
      (p6: condition_true
             (Gamma [| x <- EVariable [x_min_, x_max_]%sosadl |])
             (r = (SosADL.SosADL.IdentExpression (Some x)))%sosadl
             Gamma1)
    ,
      condition_true Gamma ((SosADL.SosADL.IdentExpression (Some x)) = r)%sosadl Gamma1

| condition_true_ge:
    forall (Gamma: env)
      (x: string)
      (x_min: SosADL.SosADL.t_Expression)
      (x_min_: SosADL.SosADL.t_Expression)
      (x_max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r_min: SosADL.SosADL.t_Expression)
      (r_max: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: expression (SosADL.SosADL.IdentExpression (Some x))
                      has type [x_min, x_max]%sosadl in Gamma)
      (p2: expression r has type [r_min, r_max]%sosadl in Gamma)
      (p3: greatest x_min_ x_min r_min)
      (p4: type [x_min_, x_max]%sosadl looks fine)
      (p5: condition_true (Gamma [| x <- EVariable [x_min_, x_max]%sosadl |])
                          (r <= (SosADL.SosADL.IdentExpression (Some x)))%sosadl
                          Gamma1)
    ,
      condition_true Gamma ((SosADL.SosADL.IdentExpression (Some x)) >= r)%sosadl Gamma1

| condition_true_gt:
    forall (Gamma: env)
      (x: string)
      (x_min: SosADL.SosADL.t_Expression)
      (x_min_: SosADL.SosADL.t_Expression)
      (x_max: SosADL.SosADL.t_Expression)
      (r: SosADL.SosADL.t_Expression)
      (r_min: SosADL.SosADL.t_Expression)
      (r_max: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: expression (SosADL.SosADL.IdentExpression (Some x))
                      has type [x_min, x_max]%sosadl in Gamma)
      (p2: expression r has type [r_min, r_max]%sosadl in Gamma)
      (p3: greatest x_min_ x_min
                    (r_min + # 1%Z)%sosadl)
      (p4: type [x_min_, x_max]%sosadl looks fine)
      (p5: condition_true (Gamma [| x <- EVariable [x_min_, x_max]%sosadl |])
                          (r < (SosADL.SosADL.IdentExpression (Some x)))%sosadl
                          Gamma1)
    ,
      condition_true Gamma ((SosADL.SosADL.IdentExpression (Some x)) > r)%sosadl Gamma1

| condition_true_sym:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (op: string)
      (r: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: condition_true
             Gamma (SosADL.SosADL.BinaryExpression
                      (Some r) (symmetric_comparison op) (Some l)) Gamma1)
    ,
      condition_true
        Gamma (SosADL.SosADL.BinaryExpression (Some l) (Some op) (Some r)) Gamma1

with condition_false: env -> SosADL.SosADL.t_Expression -> env -> Prop :=
| condition_false_general:
    forall (Gamma: env)
      (c: SosADL.SosADL.t_Expression)
    ,
      condition_false Gamma c Gamma

| condition_false_not:
    forall (Gamma: env)
      (c: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: condition_true Gamma c Gamma1)
    ,
      condition_false Gamma (! c)%sosadl Gamma

| condition_false_or:
    forall (Gamma: env)
      (c1: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (c2: SosADL.SosADL.t_Expression)
      (Gamma2: env)
      (p1: condition_false Gamma c1 Gamma1)
      (p2: condition_false Gamma1 c2 Gamma2)
    ,
      condition_false Gamma (c1 || c2)%sosadl Gamma2

| condition_false_cmp:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (op: string)
      (r: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: condition_true
             Gamma (SosADL.SosADL.BinaryExpression
                      (Some l) (negated_comparison op) (Some r)) Gamma1)
    ,
      condition_false Gamma (SosADL.SosADL.BinaryExpression
                               (Some l) (Some op) (Some r)) Gamma1
.

(** ** Generic rules for behaviors, protocols and assertions *)

  
(** The typing rules enforce tail statement requirements.

- [RepeatBehavior], [RecursiveCall] and [DoneBehavior] are tail
  statements, i.e., they cannot be followed by any subsequent
  statement.

- [ValuingBehavior], [AssertBehavior], [Action], [ForEachBehavior] and
  [DoExprBehavior] are non-tail statements. They must mandatorily be
  followed by subsequent statement.

- [IfThenElseBehavior] statements may or may not be the last statement
  of a sequence. When an [IfThenElseBehavior] statement is at a tail
  position, it must contain both [then] and [else] clauses, and the
  branches must be terminated by a tail statement.

  At non-tail position, the [else] clause is optional and the branches
  must not contain any tail statement. Futhermore, the typing rule
  adjusts the typing environment in each branch according to the
  condition. See [condition_true] and [condition_false] for further
  details.

- [ChooseBehavior] statements behave like [IfThenElseBehavior]
  statements. Note that the rules for [ChooseBehavior] do not enforce
  any restriction on the branches, such as the usual requirement that
  each branch starts with a blocking communication statement.

The typing rules for behavior bodies are structured as follow:

- [type_generic_prefixstatement] types a single non-tail statement and synthetizes
  the new environment for subsequent statements.

- [type_generic_nonfinalbody] types a non-final body of statements, i.e., with
  no tail statement.

- [type_generic_finalbody] types a final body of statements, i.e., terminated
  by a tail statement.

*)

(** %\todo{%[TellAssertion] and [AskAssertion] have still to be dealt with.%}% *)

Inductive type_generic_finalbody
          {t_Body: Type}
          {t_Statement: Type}
          (block: list t_Statement -> t_Body)
          (s_Choose: list t_Body -> t_Statement)
          (s_Done: t_Statement)
          (s_IfThenElse: option SosADL.SosADL.t_Expression -> option t_Body -> option t_Body -> t_Statement)
          (s_Repeat: option t_Body -> t_Statement)
          (p_Other: env -> t_Statement -> Prop)
          (type_expression:
             env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop)
          (type_generic_prefix: env -> t_Statement -> env -> Prop)
          (type_generic_nonfinalbody: env -> list t_Statement -> Prop):
  env -> list t_Statement -> Prop :=

| type_generic_other:
    forall
      (Gamma: env)
      (s: t_Statement)
      (p1: p_Other Gamma s)
    ,
      type_generic_finalbody
        block s_Choose s_Done s_IfThenElse s_Repeat p_Other
        type_expression
        type_generic_prefix type_generic_nonfinalbody
        Gamma [s]

| type_generic_prefix:
    forall
      (Gamma: env)
      (s: t_Statement)
      (Gamma1: env)
      (l: list t_Statement)
      (p1: type_generic_prefix Gamma s Gamma1)
      (p2: type_generic_finalbody
             block s_Choose s_Done s_IfThenElse s_Repeat p_Other
             type_expression
             type_generic_prefix type_generic_nonfinalbody
             Gamma1 l)
    ,
      type_generic_finalbody
        block s_Choose s_Done s_IfThenElse s_Repeat p_Other
        type_expression
        type_generic_prefix type_generic_nonfinalbody
        Gamma (s :: l)

| type_generic_Repeat:
    forall
      (Gamma: env)
      (b: list t_Statement)
      (p1: type_generic_nonfinalbody Gamma b)
    ,
      type_generic_finalbody
        block s_Choose s_Done s_IfThenElse s_Repeat p_Other
        type_expression
        type_generic_prefix type_generic_nonfinalbody
        Gamma [s_Repeat (Some (block b))]

| type_generic_IfThenElse:
    forall
      (Gamma: env)
      (c: SosADL.SosADL.t_Expression)
      (Gammat: env)
      (t: list t_Statement)
      (Gammae: env)
      (e: list t_Statement)
      (p1: type_expression Gamma c SosADL.SosADL.BooleanType)
      (p2: condition_true Gamma c Gammat)
      (p3: type_generic_finalbody
             block s_Choose s_Done s_IfThenElse s_Repeat p_Other
             type_expression
             type_generic_prefix type_generic_nonfinalbody
             Gammat t)
      (p4: condition_false Gamma c Gammae)
      (p5: type_generic_finalbody
             block s_Choose s_Done s_IfThenElse s_Repeat p_Other
             type_expression
             type_generic_prefix type_generic_nonfinalbody
             Gammae e)
    ,
      type_generic_finalbody
        block s_Choose s_Done s_IfThenElse s_Repeat p_Other
        type_expression
        type_generic_prefix type_generic_nonfinalbody
        Gamma [s_IfThenElse (Some c) (Some (block t)) (Some (block e))]

| type_generic_Choose:
    forall (Gamma: env)
      (branches: list (list t_Statement))
      (p1: for each b of branches,
           type_generic_finalbody
             block s_Choose s_Done s_IfThenElse s_Repeat p_Other
             type_expression
             type_generic_prefix type_generic_nonfinalbody
             Gamma b)
    ,
      type_generic_finalbody
        block s_Choose s_Done s_IfThenElse s_Repeat p_Other
        type_expression
        type_generic_prefix type_generic_nonfinalbody
        Gamma [s_Choose (map block branches)]

| type_generic_Done:
    forall
      (Gamma: env)
    ,
      type_generic_finalbody
        block s_Choose s_Done s_IfThenElse s_Repeat p_Other
        type_expression
        type_generic_prefix type_generic_nonfinalbody
        Gamma [s_Done]

.

Inductive type_generic_prefixstatement
          {t_Body: Type}
          {t_Statement: Type}
          {t_Command: Type}
          (block: list t_Statement -> t_Body)
          (s_Action:
             option SosADL.SosADL.t_ComplexName
             -> option t_Command -> t_Statement)
          (s_Choose: list t_Body -> t_Statement)
          (s_DoExpr: option SosADL.SosADL.t_Expression -> t_Statement)
          (s_ForEach: option string -> option SosADL.SosADL.t_Expression -> option t_Body -> t_Statement)
          (s_IfThenElse: option SosADL.SosADL.t_Expression -> option t_Body -> option t_Body -> t_Statement)
          (s_Valuing: option SosADL.SosADL.t_Valuing -> t_Statement)
          (c_Send: option SosADL.SosADL.t_Expression -> t_Command)
          (c_Receive: option string -> t_Command)
          (p_Other: env -> t_Statement -> env -> Prop)
          (type_expression:
             env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop)
          (type_generic_nonfinalbody: env -> list t_Statement -> Prop):
  env -> t_Statement -> env -> Prop :=

| type_generic_otherprefix:
    forall
      (Gamma: env)
      (s: t_Statement)
      (Gamma1: env)
      (p1: p_Other Gamma s Gamma1)
    ,
      type_generic_prefixstatement
        block s_Action s_Choose s_DoExpr s_ForEach s_IfThenElse s_Valuing
        c_Send c_Receive p_Other type_expression type_generic_nonfinalbody
        Gamma s Gamma1
    
| type_generic_DoExpr:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (p1: type_expression Gamma e tau)
    ,
      type_generic_prefixstatement
        block s_Action s_Choose s_DoExpr s_ForEach s_IfThenElse s_Valuing
        c_Send c_Receive p_Other type_expression type_generic_nonfinalbody
        Gamma (s_DoExpr (Some e)) Gamma

| type_generic_Valuing:
    forall
      (Gamma: env)
      (v: SosADL.SosADL.t_Valuing)
      (Gamma1: env)
      (p1: @type_valuing type_expression Gamma v Gamma1)
    ,
      type_generic_prefixstatement
        block s_Action s_Choose s_DoExpr s_ForEach s_IfThenElse s_Valuing
        c_Send c_Receive p_Other type_expression type_generic_nonfinalbody
        Gamma (s_Valuing (Some v)) Gamma1

| type_generic_IfThenElse_prefix:
    forall
      (Gamma: env)
      (c: SosADL.SosADL.t_Expression)
      (Gammat: env)
      (t: list t_Statement)
      (oe: option t_Body)
      (p1: type_expression Gamma c SosADL.SosADL.BooleanType)
      (p2: condition_true Gamma c Gammat)
      (p3: type_generic_nonfinalbody Gammat t)
      (p4: @optionally _
                       (fun g e =>
                          exists (Gammae: env),
                            condition_false g c Gammae
                            /\ exists (e: list t_Statement),
                              oe = Some (block e)
                              /\ (type_generic_nonfinalbody Gammae e))
                       Gamma oe)
    ,
      type_generic_prefixstatement
        block s_Action s_Choose s_DoExpr s_ForEach s_IfThenElse s_Valuing
        c_Send c_Receive p_Other type_expression type_generic_nonfinalbody
        Gamma (s_IfThenElse (Some c) (Some (block t)) oe) Gamma

| type_generic_Choose_prefix:
    forall (Gamma: env)
      (branches: list (list t_Statement))
      (p1: for each b of branches,
           type_generic_nonfinalbody Gamma b)
    ,
      type_generic_prefixstatement
        block s_Action s_Choose s_DoExpr s_ForEach s_IfThenElse s_Valuing
        c_Send c_Receive p_Other type_expression type_generic_nonfinalbody
        Gamma (s_Choose (map block branches)) Gamma

| type_generic_ForEach:
    forall (Gamma: env)
      (x: string)
      (vals: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (tau__x: SosADL.SosADL.t_DataType)
      (b: list t_Statement)
      (p1: type_expression Gamma vals (SosADL.SosADL.SequenceType (Some tau)))
      (p2: type_generic_nonfinalbody (Gamma [| x <- EVariable tau__x |]) b)
      (p3: tau </ tau__x)
    ,
      type_generic_prefixstatement
        block s_Action s_Choose s_DoExpr s_ForEach s_IfThenElse s_Valuing
        c_Send c_Receive p_Other type_expression type_generic_nonfinalbody
        Gamma (s_ForEach (Some x) (Some vals) (Some (block b))) Gamma

| type_generic_Send:
    forall (Gamma: env)
      (cn: SosADL.SosADL.t_ComplexName)
      (is_env: bool)
      (mode: SosADL.SosADL.ModeType)
      (conn__tau: SosADL.SosADL.t_DataType)
      (e: SosADL.SosADL.t_Expression)
      (tau__e: SosADL.SosADL.t_DataType)
      (p1: type_connectionname Gamma cn is_env mode conn__tau)
      (p2: mode_send mode)
      (p3: type_expression Gamma e tau__e)
      (p4: tau__e </ conn__tau)
    ,
      type_generic_prefixstatement
        block s_Action s_Choose s_DoExpr s_ForEach s_IfThenElse s_Valuing
        c_Send c_Receive p_Other type_expression type_generic_nonfinalbody
        Gamma
        (s_Action (Some cn) (Some (c_Send (Some e))))
        Gamma

| type_generic_Receive:
    forall (Gamma: env)
      (cn: SosADL.SosADL.t_ComplexName)
      (is_env: bool)
      (mode: SosADL.SosADL.ModeType)
      (conn__tau: SosADL.SosADL.t_DataType)
      (x: string)
      (Gamma1: env)
      (p1: type_connectionname Gamma cn is_env mode conn__tau)
      (p2: mode_receive mode)
      (p3: Gamma1 = Gamma[| x <- EVariable conn__tau |])
    ,
      type_generic_prefixstatement
        block s_Action s_Choose s_DoExpr s_ForEach s_IfThenElse s_Valuing
        c_Send c_Receive p_Other type_expression type_generic_nonfinalbody
        Gamma
        (s_Action (Some cn) (Some (c_Receive (Some x))))
        Gamma1
.

Inductive type_generic_nonfinalbody
          {t_Statement: Type}
          (type_generic_prefix: env -> t_Statement -> env -> Prop):
  env -> list t_Statement -> Prop :=

| type_generic_empty:
    forall
      (Gamma: env)
    ,
      type_generic_nonfinalbody type_generic_prefix Gamma nil

| type_generic_nonfinalprefix:
    forall
      (Gamma: env)
      (s: t_Statement)
      (Gamma1: env)
      (l: list t_Statement)
      (p1: type_generic_prefix Gamma s Gamma1)
      (p2: type_generic_nonfinalbody type_generic_prefix Gamma1 l)
    ,
      type_generic_nonfinalbody type_generic_prefix Gamma (s :: l)
.
  

(** ** Body *)

Inductive type_bodyprefix_other:
  env -> SosADL.SosADL.t_BehaviorStatement -> env -> Prop :=
.

Inductive type_bodyprefix:
  env -> SosADL.SosADL.t_BehaviorStatement -> env -> Prop :=

| type_bodyprefix_generic:
    forall
      (Gamma: env)
      (s: SosADL.SosADL.t_BehaviorStatement)
      (Gamma1: env)
      (p1: type_generic_prefixstatement
             SosADL.SosADL.Behavior
             SosADL.SosADL.Action
             SosADL.SosADL.ChooseBehavior
             SosADL.SosADL.DoExprBehavior
             SosADL.SosADL.ForEachBehavior
             SosADL.SosADL.IfThenElseBehavior
             SosADL.SosADL.ValuingBehavior
             SosADL.SosADL.SendAction
             SosADL.SosADL.ReceiveAction
             type_bodyprefix_other
             type_expression
             type_nonfinalbody
             Gamma s Gamma1)
    ,
      statement s well typed in Gamma yields to Gamma1

with type_nonfinalbody: env -> list SosADL.SosADL.t_BehaviorStatement -> Prop :=

| type_nonfinalbody_generic:
    forall
      (Gamma: env)
      (l: list SosADL.SosADL.t_BehaviorStatement)
      (p1: type_generic_nonfinalbody type_bodyprefix Gamma l)
    ,
      nonfinal body l well typed in Gamma

where "'statement' b 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1"
        := (type_bodyprefix Gamma b Gamma1)
and "'nonfinal' 'body' b 'well' 'typed' 'in' Gamma" := (type_nonfinalbody Gamma b)
.

Inductive type_finalbody_other: env -> SosADL.SosADL.t_BehaviorStatement -> Prop :=
| type_finalbody_RecursiveCall:
    forall
      (Gamma: env)
    ,
      type_finalbody_other Gamma (SosADL.SosADL.RecursiveCall nil)
.

Inductive type_finalbody: env -> list SosADL.SosADL.t_BehaviorStatement -> Prop :=

| type_finalbody_generic:
    forall (Gamma: env)
      (l: list SosADL.SosADL.t_BehaviorStatement)
      (p1: type_generic_finalbody
             SosADL.SosADL.Behavior
             SosADL.SosADL.ChooseBehavior
             SosADL.SosADL.DoneBehavior
             SosADL.SosADL.IfThenElseBehavior
             SosADL.SosADL.RepeatBehavior
             type_finalbody_other
             type_expression
             type_bodyprefix type_nonfinalbody
             Gamma l)
    ,
      final body l well typed in Gamma

where "'final' 'body' b 'well' 'typed' 'in' Gamma" := (type_finalbody Gamma b)
.
  
(** ** Behavior *)

Inductive type_behavior: env -> SosADL.SosADL.t_BehaviorDecl -> Prop :=
| type_BehaviorDecl:
    forall (Gamma: env)
      (name: string)
      (b: list SosADL.SosADL.t_BehaviorStatement)
      (p1: final body b well typed in Gamma)
    ,
      behavior (SosADL.SosADL.BehaviorDecl
                  (Some name) (Some (SosADL.SosADL.Behavior b)))
               well typed in Gamma

where "'behavior' b 'well' 'typed' 'in' Gamma" := (type_behavior Gamma b)
.

(** ** Protocol and assertion

%\todo{%revise this paragraph.%}%
Protocols are handled similarly to behaviors, with the noticeable
exception that [Any] is allowed in expressions, and [AnyAction] as a
prefix statement.

 *)

Inductive type_protocol_root_expression:
  env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop :=
  
| type_protocol_root_expression_and_type:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (t: SosADL.SosADL.t_DataType)
      (p1: type_protocol_root_expression_node Gamma e t)
      (p2: type t looks fine)
    ,
      type_protocol_root_expression Gamma e t

with type_protocol_nonroot_expression:
  env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop :=
  
| type_protocol_nonroot_expression_and_type:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (t: SosADL.SosADL.t_DataType)
      (p1: type_protocol_nonroot_expression_node Gamma e t)
      (p2: type t looks fine)
    ,
      type_protocol_nonroot_expression Gamma e t
                                       
with type_protocol_root_expression_node:
  env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop :=

| type_protocol_root_expression_nonroot:
    forall (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (t: SosADL.SosADL.t_DataType)
      (p1: type_protocol_nonroot_expression_node
             Gamma e t)
    ,
      type_protocol_root_expression_node Gamma e t

| type_protocol_root_expression_any:
    forall (Gamma: env)
      (t: SosADL.SosADL.t_DataType)
    ,
      type_protocol_root_expression_node Gamma SosADL.SosADL.Any t

with type_protocol_nonroot_expression_node:
  env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop :=

| type_protocol_nonroot_expression_generic:
    forall (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (t: SosADL.SosADL.t_DataType)
      (p1: @type_expression_node
             type_protocol_nonroot_expression
             Gamma e t)
    ,
      type_protocol_nonroot_expression_node Gamma e t

| type_protocol_nonroot_expression_MethodCall:
    forall (Gamma: env)
      (self: SosADL.SosADL.t_Expression)
      (t: SosADL.SosADL.t_DataType)
      (typeDecl: SosADL.SosADL.t_DataTypeDecl)
      (tau: SosADL.SosADL.t_DataType)
      (methods: list SosADL.SosADL.t_FunctionDecl)
      (name: string)
      (formalparams: list SosADL.SosADL.t_FormalParameter)
      (ret: SosADL.SosADL.t_DataType)
      (params: list SosADL.SosADL.t_Expression)
      (p1: type_protocol_nonroot_expression Gamma self t)
      (p2: binds Gamma (EType typeDecl tau methods))
      (p4: t </ tau)
      (p5: method name defined in methods
       with tau parameters formalparams returns ret)
      (p6: for each fp p of formalparams params,
           (exists t, SosADL.Accessors.FormalParameter_type fp = Some t
                 /\ (exists tp, (type_protocol_root_expression Gamma p tp)
                          /\ tp </ t)))
    ,
      type_protocol_nonroot_expression_node
        Gamma
        (SosADL.SosADL.MethodCall
           (Some self) (Some name) params)
        ret

.

Inductive type_protocolprefix_other:
  env -> SosADL.SosADL.t_ProtocolStatement -> env -> Prop :=

| type_protocolprefix_AnyAction:
    forall (Gamma: env)
    ,
      type_protocolprefix_other
        Gamma
        SosADL.SosADL.AnyAction
        Gamma

| type_protocolprefix_ReceiveAny:
    forall (Gamma: env)
      (cn: SosADL.SosADL.t_ComplexName)
      (is_env: bool)
      (mode: SosADL.SosADL.ModeType)
      (conn__tau: SosADL.SosADL.t_DataType)
      (p1: type_connectionname Gamma cn is_env mode conn__tau)
      (p2: mode_receive mode)
    ,
      type_protocolprefix_other
        Gamma
        (SosADL.SosADL.ProtocolAction
           (Some cn)
           (Some SosADL.SosADL.ReceiveAnyProtocolAction))
        Gamma

| type_protocolprefix_Repeat:
    forall (Gamma: env)
      (l: list SosADL.SosADL.t_ProtocolStatement)
      (p1: type_nonfinalprotocol Gamma l)
    ,
      type_protocolprefix_other
        Gamma
        (SosADL.SosADL.RepeatProtocol
           (Some (SosADL.SosADL.Protocol l)))
        Gamma

with type_bodyprotocol:
  env -> SosADL.SosADL.t_ProtocolStatement -> env -> Prop :=

| type_bodyprotocol_generic:
    forall
      (Gamma: env)
      (s: SosADL.SosADL.t_ProtocolStatement)
      (Gamma1: env)
      (p1: type_generic_prefixstatement
             SosADL.SosADL.Protocol
             SosADL.SosADL.ProtocolAction
             SosADL.SosADL.ChooseProtocol
             SosADL.SosADL.DoExprProtocol
             SosADL.SosADL.ForEachProtocol
             SosADL.SosADL.IfThenElseProtocol
             SosADL.SosADL.ValuingProtocol
             SosADL.SosADL.SendProtocolAction
             SosADL.SosADL.ReceiveProtocolAction
             type_protocolprefix_other
             type_protocol_root_expression
             type_nonfinalprotocol
             Gamma s Gamma1)
    ,
      protocol statement s well typed in Gamma yields to Gamma1

with type_nonfinalprotocol: env -> list SosADL.SosADL.t_ProtocolStatement -> Prop :=

| type_nonfinalprotocol_generic:
    forall
      (Gamma: env)
      (l: list SosADL.SosADL.t_ProtocolStatement)
      (p1: type_generic_nonfinalbody type_bodyprotocol Gamma l)
    ,
      nonfinal protocol l well typed in Gamma

where "'protocol' 'statement' b 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1"
        := (type_bodyprotocol Gamma b Gamma1)
and "'nonfinal' 'protocol' b 'well' 'typed' 'in' Gamma"
               := (type_nonfinalprotocol Gamma b)
.

Inductive type_finalprotocol_other: env -> SosADL.SosADL.t_ProtocolStatement -> Prop :=
.

Inductive type_finalprotocol: env -> list SosADL.SosADL.t_ProtocolStatement -> Prop :=

| type_finalprotocol_generic:
    forall (Gamma: env)
      (l: list SosADL.SosADL.t_ProtocolStatement)
      (p1: type_generic_finalbody
             SosADL.SosADL.Protocol
             SosADL.SosADL.ChooseProtocol
             SosADL.SosADL.DoneProtocol
             SosADL.SosADL.IfThenElseProtocol
             SosADL.SosADL.RepeatProtocol
             type_finalprotocol_other
             type_protocol_root_expression
             type_bodyprotocol type_nonfinalprotocol
             Gamma l)
    ,
      final protocol l well typed in Gamma

where "'final' 'protocol' p 'well' 'typed' 'in' Gamma" := (type_finalprotocol Gamma p)
.

Inductive type_protocol: env -> SosADL.SosADL.t_ProtocolDecl -> Prop :=

| type_ProtocolDecl:
    forall (Gamma: env)
      (name: string)
      (body: list SosADL.SosADL.t_ProtocolStatement)
      (p1: final protocol body well typed in Gamma)
    ,
      protocol (SosADL.SosADL.ProtocolDecl
                  (Some name) (Some (SosADL.SosADL.Protocol body)))
               well typed in Gamma

where "'protocol' p 'well' 'typed' 'in' Gamma" := (type_protocol Gamma p)
.

Inductive type_assertion: env -> SosADL.SosADL.t_AssertionDecl -> Prop :=

| type_AssertionDecl:
    forall (Gamma: env)
      (name: string)
      (body: list SosADL.SosADL.t_ProtocolStatement)
      (p1: final protocol body well typed in Gamma)
    ,
      assertion (SosADL.SosADL.AssertionDecl
                   (Some name) (Some (SosADL.SosADL.Protocol body)))
               well typed in Gamma

where "'assertion' p 'well' 'typed' 'in' Gamma" := (type_assertion Gamma p)
.

(**
 ** Formal parameters
 *)

(** Regardless the context where they appear, formal parameters enter
the environment in no specific order. In addition, they cannot refer
to each other. The typing rule therefore calls the generic
[mutually_translate] rule.

[formalParameter_to_EVariable] builds an environment item for a given
formal parameter. *)

Definition formalParameter_to_EVariable p :=
  match SosADL.Accessors.FormalParameter_type p with
  | None => None
  | Some t => Some (EVariable t)
  end.

(** [type_formalParameter] asserts that a formal parameter is
correctly defined in a given environment. It synthetizes a new formal
parameter in which the data type has been substituted according to
[type_datatype]. *)

Inductive type_formalParameter:
  env -> SosADL.SosADL.t_FormalParameter
  -> SosADL.SosADL.t_FormalParameter -> env -> Prop :=

| type_FormalParameter_typed:
    forall (Gamma: env)
      (n: string)
      (t: SosADL.SosADL.t_DataType)
      (t1: SosADL.SosADL.t_DataType)
      (Gamma1: env)
      (p1: type t is t1 in Gamma)
    ,
      type_formalParameter
        Gamma (SosADL.SosADL.FormalParameter (Some n) (Some t))
        (SosADL.SosADL.FormalParameter (Some n) (Some t1)) Gamma1
.

(** [type_formalParameters] asserts that a list of formal parameters
is correct in a given environment.  It synthetizes a new list of
formal parameters in which the data types have been substituted
according to [type_datatype]. This predicate invokes the generic
[mutually_translate] judgment with the right parameters. *)

Definition type_formalParameters Gamma l l1 Gamma1 :=
  @mutually_translate _ type_formalParameter
                      SosADL.Accessors.FormalParameter_name
                      formalParameter_to_EVariable
                      Gamma l l1 Gamma1.

(** ** Connections *)

(** Connections are typed similarly to formal parameters: they cannot
refer to each other, and the order of the declarations is
insignificant. [type_connection] states the typing rules for a single
connection. [type_connections] invokes [mutually_translate] with the
right parameters in order to type a list of connections. *)

Inductive type_connection:
  env -> SosADL.SosADL.t_Connection
  -> SosADL.SosADL.t_Connection -> env -> Prop :=

| type_Connection_simple:
    forall (Gamma: env)
      (name: string)
      (k: bool)
      (m: SosADL.SosADL.ModeType)
      (t: SosADL.SosADL.t_DataType)
      (t1: SosADL.SosADL.t_DataType)
      (Gamma1: env)
      (p1: type t is t1 in Gamma)
    ,
      type_connection
        Gamma (SosADL.SosADL.Connection (Some k) (Some name) (Some m) (Some t))
        (SosADL.SosADL.Connection (Some k) (Some name) (Some m) (Some t1)) Gamma1
.

Definition type_connections Gamma l l1 Gamma1 :=
  @mutually_translate _ type_connection
                      SosADL.Accessors.Connection_name
                      (fun x => Some (EConnection x))
                      Gamma l l1 Gamma1.
(** ** Gates and duties

Gates and duties are typed in a similar way. The only difference
follows from the fact that the former appear only in systems while the
latter in mediators. Like formal parameters and connections, they
cannot refer to each other, and the order of their declarations is
insignificant. [type_gate] is the judgement for a single
gate. [type_gates] uses [mutually_translate] in order to deal with a
list of gates. *)

Inductive type_gate:
  env -> SosADL.SosADL.t_GateDecl
  -> SosADL.SosADL.t_GateDecl -> env -> Prop :=
  
| type_GateDecl:
    forall (Gamma: env)
      (name: string)
      (conns: list SosADL.SosADL.t_Connection)
      (conns1: list SosADL.SosADL.t_Connection)
      (Gamma2: env)
      (ps: list SosADL.SosADL.t_ProtocolDecl)
      (Gamma1: env)
      (p1: type_connections Gamma conns conns1 Gamma2)
      (p2: for each p of ps,
           protocol p well typed in Gamma2)
    ,
      type_gate
        Gamma (SosADL.SosADL.GateDecl (Some name) conns ps)
        (SosADL.SosADL.GateDecl (Some name) conns1 ps) Gamma1
.

Definition gateDecl_to_EGateOrDuty g :=
  Some (EGateOrDuty (SosADL.Accessors.GateDecl_connections g)).

Definition type_gates Gamma l Gamma1 :=
  exists l1,
    @mutually_translate _ type_gate
                        SosADL.Accessors.GateDecl_name
                        gateDecl_to_EGateOrDuty
                        Gamma l l1 Gamma1.

Inductive type_duty:
  env -> SosADL.SosADL.t_DutyDecl
  -> SosADL.SosADL.t_DutyDecl -> env -> Prop :=
  
| type_DutyDecl:
    forall (Gamma: env)
      (name: string)
      (conns: list SosADL.SosADL.t_Connection)
      (conns1: list SosADL.SosADL.t_Connection)
      (Gamma2: env)
      (assump: list SosADL.SosADL.t_AssertionDecl)
      (ps: list SosADL.SosADL.t_ProtocolDecl)
      (Gamma1: env)
      (p1: type_connections Gamma conns conns1 Gamma2)
      (p2: for each a of assump,
           assertion a well typed in Gamma2)
      (p3: for each p of ps,
           protocol p well typed in Gamma2)
    ,
      type_duty
        Gamma (SosADL.SosADL.DutyDecl (Some name) conns assump ps)
        (SosADL.SosADL.DutyDecl (Some name) conns1 assump ps) Gamma1
.

Definition dutyDecl_to_EGateOrDuty g :=
  Some (EGateOrDuty (SosADL.Accessors.DutyDecl_connections g)).

Definition type_duties Gamma l Gamma1 :=
  exists l1,
    @mutually_translate _ type_duty
                        SosADL.Accessors.DutyDecl_name
                        dutyDecl_to_EGateOrDuty
                        Gamma l l1 Gamma1.

(** ** Function declaration *)


(** %\note{%Since the language does not allow conditional expression,
permitting (mutually) recursive functions is irrelevant.%}% *)

(** %\note{%Since the concrete grammar restricts all the functions to
be methods, only this case is taken into account.%}% *)

Inductive type_function: env -> SosADL.SosADL.t_FunctionDecl -> env -> Prop :=

| type_FunctionDecl_Method:
    forall
      (Gamma: env)
      (dataName: string)
      (dataTypeName: string)
      (dataTypeDecl: SosADL.SosADL.t_DataTypeDecl)
      (dataTypeReal: SosADL.SosADL.t_DataType)
      (dataTypeMethods: list SosADL.SosADL.t_FunctionDecl)
      (name: string)
      (params: list SosADL.SosADL.t_FormalParameter)
      (params': list SosADL.SosADL.t_FormalParameter)
      (Gammap: env)
      (rettype: SosADL.SosADL.t_DataType)
      (rettype': SosADL.SosADL.t_DataType)
      (vals: list SosADL.SosADL.t_Valuing)
      (Gammav: env)
      (retexpr: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (Gamma1: env)
      (p1: Gamma [| dataTypeName |] =
           Some (EType dataTypeDecl dataTypeReal dataTypeMethods))
      (p2: type rettype is rettype' in Gamma)
      (p3: type_formalParameters
             Gamma
             (SosADL.SosADL.FormalParameter
                (Some dataName)
                (Some (SosADL.SosADL.NamedType
                         (Some dataTypeName))) :: params)
             (SosADL.SosADL.FormalParameter
                (Some dataName)
                (Some dataTypeReal) :: params')
             Gammap)
      (p4: @type_valuings type_expression Gammap vals Gammav)
      (p5: expression retexpr has type tau in Gammav)
      (p6: tau </ rettype')
      (p7: Gamma1 =
           Gamma [| dataTypeName <- EType dataTypeDecl dataTypeReal
                                 ((SosADL.SosADL.FunctionDecl
                                     (Some (SosADL.SosADL.FormalParameter
                                              (Some dataName)
                                              (Some dataTypeReal)))
                                     (Some name) params' (Some rettype')
                                     vals (Some retexpr))
                                    :: dataTypeMethods) |])
    ,
      function (SosADL.SosADL.FunctionDecl
                  (Some (SosADL.SosADL.FormalParameter
                           (Some dataName)
                           (Some (SosADL.SosADL.NamedType
                                    (Some dataTypeName)))))
                  (Some name) params (Some rettype) vals (Some retexpr))
               well typed in Gamma
               yields to Gamma1

where "'function' f 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1"
        := (type_function Gamma f Gamma1)
.

Definition type_functionDecls Gamma l Gamma1 := @incrementally _ type_function Gamma l Gamma1.

(** ** Data type declaration *)

(** In order to allow abstract (named) types despite the general
approach based on structural typing, abstract (named) types are
substituted by a uniquely generated named type. This approach avoids
clashes and ensures the uniqueness of the abstract (named) types.

[name_is_fresh] yields [true] if a name is fresh in a given
environment. *)

Fixpoint name_is_fresh (e: env) (x: string): bool :=
  match e with
  | h :: r =>
    andb
    match (value h) with
    | EType _ (SosADL.sosADL.sosADL_DataType_sosADL_NamedType (Some n)) _ =>
      (negb (string_eqb x n))
    | _ => true
    end (name_is_fresh r x)
  | nil => true
  end.

Inductive type_datatypeDecl:
  env -> SosADL.SosADL.t_DataTypeDecl -> env -> Prop :=
| type_DataTypeDecl_def:
    forall
      (Gamma: env)
      (name: string)
      (t: SosADL.SosADL.t_DataType)
      (t': SosADL.SosADL.t_DataType)
      (funs: list SosADL.SosADL.t_FunctionDecl)
      (Gamma1: env)
      (p1: type t is t' in Gamma)
      (p2: for each f of funs,
           exists p,
             SosADL.Accessors.FunctionDecl_data f = Some p
             /\ SosADL.Accessors.FormalParameter_type p
               = Some (SosADL.SosADL.NamedType (Some name)))
      (p3: type_functionDecls
             (Gamma [| name <- EType
                            (SosADL.SosADL.DataTypeDecl
                               (Some name) (Some t) funs)
                            t' nil |]) funs Gamma1)
    ,
      typedecl (SosADL.SosADL.DataTypeDecl (Some name) (Some t) funs)
               well typed in Gamma yields to Gamma1

| type_DataTypeDecl_def_None:
    forall
      (Gamma: env)
      (name: string)
      (name': string)
      (funs: list SosADL.SosADL.t_FunctionDecl)
      (Gamma1: env)
      (p1: name_is_fresh Gamma name' = true)
      (p2: for each f of funs,
           exists p,
             SosADL.Accessors.FunctionDecl_data f = Some p
             /\ SosADL.Accessors.FormalParameter_type p
               = Some (SosADL.SosADL.NamedType (Some name)))
      (p3: type_functionDecls
             (Gamma [| name <- EType
                            (SosADL.SosADL.DataTypeDecl
                               (Some name) None funs)
                            (SosADL.SosADL.NamedType (Some name'))
                            nil |]) funs Gamma1)
    ,
      typedecl (SosADL.SosADL.DataTypeDecl (Some name) None funs)
               well typed in Gamma yields to Gamma1

where "'typedecl' t 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1"
        := (type_datatypeDecl Gamma t Gamma1)
.

Definition type_datatypeDecls Gamma l Gamma1 :=
  @incrementally _ type_datatypeDecl Gamma l Gamma1.

(** ** System *)

Inductive type_system: env -> SosADL.SosADL.t_SystemDecl -> Prop :=
| type_SystemDecl:
    forall
      (Gamma: env)
      (name: string)
      (params: list SosADL.SosADL.t_FormalParameter)
      (params': list SosADL.SosADL.t_FormalParameter)
      (Gamma1: env)
      (datatypes: list SosADL.SosADL.t_DataTypeDecl)
      (Gamma2: env)
      (gates: list SosADL.SosADL.t_GateDecl)
      (Gamma3: env)
      (bhv: SosADL.SosADL.t_BehaviorDecl)
      (assrt: list SosADL.SosADL.t_AssertionDecl)
      (p1: type_formalParameters Gamma params params' Gamma1)
      (p2: type_datatypeDecls Gamma1 datatypes Gamma2)
      (p3: type_gates Gamma2 gates Gamma3)
      (p4: behavior bhv well typed in Gamma3)
      (p5: for each a of assrt,
           assertion a well typed in Gamma3)
    ,
      system (SosADL.SosADL.SystemDecl
                (Some name) params datatypes gates (Some bhv) assrt)
             well typed in Gamma

where "'system' s 'well' 'typed' 'in' Gamma" := (type_system Gamma s)
.

Definition type_systems Gamma l Gamma1 :=
  @incrementally _ (simple_increment _ type_system
                                     SosADL.Accessors.SystemDecl_name
                                     (fun x => Some (ESystem x)))
                 Gamma l Gamma1.

(** ** Mediator

Mediators are similar to systems, except that they declare duties
instead of gates.

 *)

Inductive type_mediator: env -> SosADL.SosADL.t_MediatorDecl -> Prop :=

| type_MediatorDecl:
    forall (Gamma: env)
      (name: string)
      (params: list SosADL.SosADL.t_FormalParameter)
      (params': list SosADL.SosADL.t_FormalParameter)
      (Gamma1: env)
      (datatypes: list SosADL.SosADL.t_DataTypeDecl)
      (Gamma2: env)
      (duties: list SosADL.SosADL.t_DutyDecl)
      (Gamma3: env)
      (b: SosADL.SosADL.t_BehaviorDecl)
      (assump: list SosADL.SosADL.t_AssertionDecl)
      (assrt: list SosADL.SosADL.t_AssertionDecl)
      (p1: type_formalParameters Gamma params params' Gamma1)
      (p2: type_datatypeDecls Gamma1 datatypes Gamma2)
      (p3: type_duties Gamma2 duties Gamma3)
      (p4: behavior b well typed in Gamma3)
      (p5: for each a of assump,
           assertion a well typed in Gamma3)
      (p6: for each a of assrt,
           assertion a well typed in Gamma3)
    ,
      mediator (SosADL.SosADL.MediatorDecl
                  (Some name) params datatypes duties
                  (Some b) assump assrt) well typed in Gamma
       
where "'mediator' m 'well' 'typed' 'in' Gamma" := (type_mediator Gamma m)
.

Definition type_mediators Gamma l Gamma1 :=
  @incrementally _ (simple_increment _ type_mediator
                                     SosADL.Accessors.MediatorDecl_name
                                     (fun x => Some (EMediator x)))
                 Gamma l Gamma1.

(** ** Architecture *)

(** %\todo{% %}% *)

Inductive type_architecture: env -> SosADL.SosADL.t_ArchitectureDecl -> Prop :=

with type_architectureblock: env -> SosADL.SosADL.t_ArchitectureDecl -> Prop :=



(** ** Architecture behavior*)

(** %\todo{% %}% *)

with type_archbehavior: env ->  SosADL.SosADL.t_ArchBehaviorDecl -> Prop :=


where "'architecture' a 'well' 'typed' 'in' Gamma" := (type_architecture Gamma a)
and "'architectureblock' a 'well' 'typed' 'in' Gamma" := (type_architectureblock Gamma a)
and "'archbehavior' b 'well' 'typed' 'in' Gamma" := (type_archbehavior Gamma b)
.

Definition type_architectures Gamma l Gamma1 :=
  @incrementally _ (simple_increment _ type_architecture
                                     SosADL.Accessors.ArchitectureDecl_name
                                     (fun x => Some (EArchitecture x)))
                 Gamma l Gamma1.

(** ** Entity *)

(** The order of the declaration is significant for the typing
rules. Namely, the scope of a declaration starts after this
declaration and spans until the end of the enclosing block. This
choice prevents, e.g., (mutually) recursive declarations. *)

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
      entity (SosADL.SosADL.EntityBlock
                datatypes funs systems mediators architectures)
             well typed in Gamma
  
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
| type_SosADL_file:
    forall (i: list SosADL.SosADL.t_Import)
           (d: SosADL.SosADL.t_Unit)
           (p: unit d well typed in empty)
    ,
      SoSADL (SosADL.SosADL.SosADL i (Some d)) well typed
where "'SoSADL' a 'well' 'typed'" := (type_sosADL a)
.

