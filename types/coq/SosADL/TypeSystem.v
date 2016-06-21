Require Import List.
Require Import String.
Require SosADL.SosADL.
Require Import SosADL.Environment.
Require Import SosADL.Utils.
Require Import SosADL.Interpretation.
Require Import BinInt.

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
 ** Objects in [Gamma], the main environment

We choose to have a single environment for all the kinds of objects,
hence to have a single namespace. The following type describes all the
objects that can be stored in the typing environment. The main kinds of objects are:

- [EType]: data type declaration
- [EGateOrDuty]: list of connections for a gate or a duty
- [EVariable]: value-storing variable

 *)

Inductive env_content: Set :=
| EType: SosADL.SosADL.t_DataTypeDecl -> SosADL.SosADL.t_DataType -> list SosADL.SosADL.t_FunctionDecl -> env_content
| EFunction: SosADL.SosADL.t_FunctionDecl -> env_content
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

(** The following notations is a shortcut to look for a method in a
data type declaration.  *)

Definition method_defined'
           (m: string)
           (l: list SosADL.SosADL.t_FunctionDecl)
           (tau: SosADL.SosADL.t_DataType)
           (f: list SosADL.SosADL.t_FormalParameter)
           (r: SosADL.SosADL.t_DataType)
  := List.Exists (fun fd =>
                    match SosADL.SosADL.FunctionDecl_data fd with
                    | Some fp => SosADL.SosADL.FormalParameter_type fp
                    | None => None
                    end = Some tau
                    /\ SosADL.SosADL.FunctionDecl_name fd = Some m
                    /\ SosADL.SosADL.FunctionDecl_parameters fd = f
                    /\ SosADL.SosADL.FunctionDecl_type fd = Some r)
                 l.

Definition method_defined''
           (m: string)
           (l: list SosADL.SosADL.t_FunctionDecl)
           (tau: SosADL.SosADL.t_DataType)
           (f: list SosADL.SosADL.t_FormalParameter)
           (r: SosADL.SosADL.t_DataType)
  := exists (i: nat), match List.nth_error l i with
               | Some fd =>
                 match SosADL.SosADL.FunctionDecl_data fd with
                 | Some fp => SosADL.SosADL.FormalParameter_type fp
                 | None => None
                 end = Some tau
                 /\ SosADL.SosADL.FunctionDecl_name fd = Some m
                 /\ SosADL.SosADL.FunctionDecl_parameters fd = f
                 /\ SosADL.SosADL.FunctionDecl_type fd = Some r
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
                 match SosADL.SosADL.FunctionDecl_data fd with
                 | Some fp => SosADL.SosADL.FormalParameter_type fp
                 | None => None
                 end = Some tau
                 /\ SosADL.SosADL.FunctionDecl_name fd = Some m
                 /\ SosADL.SosADL.FunctionDecl_parameters fd = f
                 /\ SosADL.SosADL.FunctionDecl_type fd = Some r
               | None => False
               end.

Notation "'method' m 'defined' 'in' d 'with' tau 'parameters' f 'returns' r" :=
  (method_defined m d tau f r)
    (at level 200, no associativity).

(** [field_has_type] is a predicate to look for a field in a list of
field declarations. *)

Inductive field_has_type: list SosADL.SosADL.t_FieldDecl -> string -> SosADL.SosADL.t_DataType -> Prop :=
| First_Field: forall n t r, field_has_type (SosADL.SosADL.FieldDecl (Some n) (Some t) :: r) n t
| Next_Field: forall n t h r, field_has_type r n t -> field_has_type (h :: r) n t.

Fixpoint field_type (l: list SosADL.SosADL.t_FieldDecl) (n: string) {struct l}: option SosADL.SosADL.t_DataType :=
  match l with
  | nil => None
  | (SosADL.SosADL.FieldDecl (Some f) r) :: tl => if string_dec n f then r else field_type tl n
  | _ :: tl => field_type tl n
  end.

(*Hypothesis names_of_expression: SosADL.SosADL.t_Expression -> list string.*)

(**
%
\def\todo#1{{\color{red}TODO: #1}}
\def\note#1{{\color{blue}NOTE: #1}}
%
 *)

(** * Subtyping relation *)

Reserved Notation "t1 </ t2" (at level 70).

Inductive subtype: SosADL.SosADL.t_DataType -> SosADL.SosADL.t_DataType -> Prop :=
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
      (SosADL.SosADL.RangeType (Some lmi) (Some lma)) </ (SosADL.SosADL.RangeType (Some rmi) (Some rma))

| subtype_tuple:
    forall (l: list SosADL.SosADL.t_FieldDecl)
      (r: list SosADL.SosADL.t_FieldDecl)
      (p1: for each f of r,
           exists n,
             SosADL.SosADL.FieldDecl_name f = Some n
             /\ exists tr,
               SosADL.SosADL.FieldDecl_type f = Some tr
               /\ exists tl, field_type l n = Some tl
                       /\ (tl </ tr))
    ,
      (SosADL.SosADL.TupleType l) </ (SosADL.SosADL.TupleType r)

| subtype_sequence:
    forall (l: SosADL.SosADL.t_DataType)
      (r: SosADL.SosADL.t_DataType)
      (p1: l </ r)
    ,
      (SosADL.SosADL.SequenceType (Some l)) </ (SosADL.SosADL.SequenceType (Some r))

where "t1 </ t2" := (subtype t1 t2)
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
          {T: Set} {P: env -> T -> env -> Prop}:
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

Inductive simple_increment
          (T: Set) (P: env -> T -> Prop) (name: T -> option string)
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

Lemma incrementally_fold_left:
  forall {T: Set} (P: env -> T -> env -> Prop) (name: T -> option string)
         (content: T -> option env_content)
         (p: forall g x g', P g x g' -> g' = augment_env g (name x) (content x))
         (l: list T)
         (Gamma: env) (Gamma': env)
         (s: @incrementally T P Gamma l Gamma'),
    Gamma' = fold_left (fun r x => augment_env r (name x) (content x)) l Gamma.
Proof.
  intros.
  induction s.
  - auto.
  - apply p in p1. subst. auto.
Qed.

Lemma simple_incrementally_fold_left:
  forall {T: Set} (P: env -> T -> Prop) (name: T -> option string)
         (content: T -> option env_content)
         (l: list T)
         (Gamma: env) (Gamma': env)
         (s: @incrementally T (simple_increment T P name content) Gamma l Gamma'),
    Gamma' = fold_left (fun r x => augment_env r (name x) (content x)) l Gamma.
Proof.
  intros T P name content l Gamma Gamma'. apply incrementally_fold_left. intros g x g' H.
  destruct H. auto.
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

(** [mutually_translate] is a generic rule for unordered, simultaneous, mutual definitions. *)

Inductive mutually_translate
          {T: Set} {P: env -> T -> T -> env -> Prop} {name: T -> option string} {content: T -> option env_content}:
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
Reserved Notation "'typedecl' t 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'function' f 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'type' t 'looks' 'fine'" (at level 200, no associativity).
Reserved Notation "'type' t 'is' u 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'system' s 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'mediator' m 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'mediatorblock' m 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'architecture' a 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'architectureblock' a 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'expression' e 'has' 'type' t 'in' Gamma" (at level 200, no associativity, Gamma at level 1).
Reserved Notation "'expression' 'node' e 'has' 'type' t 'in' Gamma" (at level 200, no associativity, Gamma at level 1).
Reserved Notation "'archbehavior' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'behavior' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'assertion' a 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'protocol' p 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'final' 'body' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'statement' b 'prefixing' r 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'nonfinal' 'body' b 'well' 'typed' 'in' Gamma" (at level 200, Gamma at level 1, no associativity).
Reserved Notation "'valuing' v 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1" (at level 200, Gamma at level 1, no associativity).

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

Inductive check_datatype: SosADL.SosADL.t_DataType -> Prop :=
| check_NamedType:
    forall
      (n: string)
    ,
      type (SosADL.SosADL.NamedType (Some n)) looks fine

| check_TupleType:
    forall
      (fields: list SosADL.SosADL.t_FieldDecl)
      (p1: values (SosADL.SosADL.FieldDecl_name f) for f of fields are distinct according to option_string_dec)
      (p2: for each f of fields, exists t, SosADL.SosADL.FieldDecl_type f = Some t
                                      /\ type t looks fine)
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
      type (SosADL.SosADL.RangeType (Some min)
                                    (Some max)) looks fine

| check_BooleanType:
      type SosADL.SosADL.BooleanType looks fine

where "'type' t 'looks' 'fine'" := (check_datatype t)
.

Inductive type_datatype: env -> SosADL.SosADL.t_DataType -> SosADL.SosADL.t_DataType -> Prop :=
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
      (p1: values (SosADL.SosADL.FieldDecl_name f) for f of fields are distinct according to option_string_dec)
      (p2: for each f f' of fields fields',
           SosADL.SosADL.FieldDecl_name f = SosADL.SosADL.FieldDecl_name f'
           /\ exists t, SosADL.SosADL.FieldDecl_type f = Some t
                  /\ exists t', SosADL.SosADL.FieldDecl_type f' = Some t'
                                      /\ type t is t' in Gamma)
    ,
      type (SosADL.SosADL.TupleType fields) is (SosADL.SosADL.TupleType fields') in Gamma

| type_SequenceType:
    forall
      (Gamma: env)
      (t: SosADL.SosADL.t_DataType)
      (t': SosADL.SosADL.t_DataType)
      (p: type t is t' in Gamma)
    ,
      type (SosADL.SosADL.SequenceType (Some t)) is (SosADL.SosADL.SequenceType (Some t')) in Gamma

| type_RangeType_trivial:
    forall
      (Gamma: env)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: min <= max)
    ,
      type (SosADL.SosADL.RangeType (Some min)
                                    (Some max))
           is (SosADL.SosADL.RangeType (Some min)
                                       (Some max)) in Gamma

| type_BooleanType:
    forall
      (Gamma: env)
    ,
      type SosADL.SosADL.BooleanType is SosADL.SosADL.BooleanType in Gamma

where "'type' t 'is' u 'in' Gamma" := (type_datatype Gamma t u)
.

(**
 ** Expression

Before running into the type system for expressions, we first introduce some definitions and properties about interval arithmetic.

 *)

Inductive range_modulo_min: SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> Prop :=
| range_modulo_min_pos:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (min: SosADL.SosADL.t_Expression)
      (p1: (SosADL.SosADL.IntegerValue (Some 1%Z)) <= rmin)
      (p2: min <= (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.IntegerValue (Some 1%Z))) (Some "-") (Some rmax)))
    ,
      range_modulo_min lmin lmax rmin rmax min

| range_modulo_min_zero:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (min: SosADL.SosADL.t_Expression)
      (p1: (SosADL.SosADL.IntegerValue (Some 0%Z)) <= lmin)
      (p2: min <= (SosADL.SosADL.IntegerValue (Some 0%Z)))
    ,
      range_modulo_min lmin lmax rmin rmax min

| range_modulo_min_neg:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (min: SosADL.SosADL.t_Expression)
      (p1: rmax <= (SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))))
      (p2: min <= (SosADL.SosADL.BinaryExpression (Some rmin) (Some "+") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))))
    ,
      range_modulo_min lmin lmax rmin rmax min
.

Inductive range_modulo_max: SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> Prop :=
| range_modulo_max_pos:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: (SosADL.SosADL.IntegerValue (Some 1%Z)) <= rmin)
      (p2: (SosADL.SosADL.BinaryExpression (Some rmax) (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))) <= max)
    ,
      range_modulo_max lmin lmax rmin rmax max

| range_modulo_max_zero:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: lmax <= (SosADL.SosADL.IntegerValue (Some 0%Z)))
      (p2: (SosADL.SosADL.IntegerValue (Some 0%Z)) <= max)
    ,
      range_modulo_max lmin lmax rmin rmax max

| range_modulo_max_neg:
    forall
      (lmin: SosADL.SosADL.t_Expression)
      (lmax: SosADL.SosADL.t_Expression)
      (rmin: SosADL.SosADL.t_Expression)
      (rmax: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: rmax <= (SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))))
      (p2: (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z))))) (Some "-") (Some rmin)) <= max)
    ,
      range_modulo_max lmin lmax rmin rmax max
.

(*
%\note{%This set of rules is restricted to computable expressions. This means that [any] and unifications are excluded from these rules. It indeed seems reasonnable,
at least as a first step, that [any] is allowed solely in the protocols and assertions. %}%
*)

Inductive type_expression: env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop :=
| type_expression_and_type:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (t: SosADL.SosADL.t_DataType)
      (p1: expression node e has type t in Gamma)
      (p2: type t looks fine)
    ,
      expression e has type t in Gamma

with type_expression_node: env -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_DataType -> Prop :=
                      
| type_expression_IntegerValue:
    forall
      (Gamma: env)
      (v: BinInt.Z)
    ,
      expression node (SosADL.SosADL.IntegerValue (Some v))
      has type (SosADL.SosADL.RangeType
                  (Some (SosADL.SosADL.IntegerValue (Some v)))
                  (Some (SosADL.SosADL.IntegerValue (Some v)))) in Gamma

| type_expression_Opposite:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: expression e has type tau in Gamma)
      (p2: tau </ (SosADL.SosADL.RangeType (Some min) (Some max)))
    ,
      expression node (SosADL.SosADL.UnaryExpression (Some "-") (Some e))
                 has type (SosADL.SosADL.RangeType
                             (Some (SosADL.SosADL.UnaryExpression (Some "-") (Some max)))
                             (Some (SosADL.SosADL.UnaryExpression (Some "-") (Some min)))) in Gamma

| type_expression_Same:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (min: SosADL.SosADL.t_Expression)
      (max: SosADL.SosADL.t_Expression)
      (p1: expression e has type tau in Gamma)
      (p2: tau </ (SosADL.SosADL.RangeType (Some min) (Some max)))
    ,
      expression node (SosADL.SosADL.UnaryExpression (Some "+") (Some e))
      has type (SosADL.SosADL.RangeType (Some min) (Some max)) in Gamma


| type_expression_Not:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (p1: expression e has type tau in Gamma)
      (p2: tau </ SosADL.SosADL.BooleanType)
    ,
      expression node (SosADL.SosADL.UnaryExpression (Some "not") (Some e)) has type SosADL.SosADL.BooleanType in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ (SosADL.SosADL.RangeType (Some l__min) (Some l__max)))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ (SosADL.SosADL.RangeType (Some r__min) (Some r__max)))
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "+") (Some r))
      has type (SosADL.SosADL.RangeType (Some (SosADL.SosADL.BinaryExpression (Some l__min) (Some "+") (Some r__min)))
                              (Some (SosADL.SosADL.BinaryExpression (Some l__max) (Some "+") (Some r__max)))) in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ (SosADL.SosADL.RangeType (Some l__min) (Some l__max)))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ (SosADL.SosADL.RangeType (Some r__min) (Some r__max)))
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "-") (Some r))
      has type (SosADL.SosADL.RangeType (Some (SosADL.SosADL.BinaryExpression (Some l__min) (Some "-") (Some r__max)))
                              (Some (SosADL.SosADL.BinaryExpression (Some l__max) (Some "-") (Some r__min)))) in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ (SosADL.SosADL.RangeType (Some l__min) (Some l__max)))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ (SosADL.SosADL.RangeType (Some r__min) (Some r__max)))
      (p5: min <= (SosADL.SosADL.BinaryExpression (Some l__min) (Some "*") (Some r__min)))
      (p6: min <= (SosADL.SosADL.BinaryExpression (Some l__min) (Some "*") (Some r__max)))
      (p7: min <= (SosADL.SosADL.BinaryExpression (Some l__max) (Some "*") (Some r__min)))
      (p8: min <= (SosADL.SosADL.BinaryExpression (Some l__max) (Some "*") (Some r__max)))
      (p9: (SosADL.SosADL.BinaryExpression (Some l__min) (Some "*") (Some r__min)) <= max)
      (pa: (SosADL.SosADL.BinaryExpression (Some l__min) (Some "*") (Some r__max)) <= max)
      (pb: (SosADL.SosADL.BinaryExpression (Some l__max) (Some "*") (Some r__min)) <= max)
      (pc: (SosADL.SosADL.BinaryExpression (Some l__max) (Some "*") (Some r__max)) <= max)
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "*") (Some r))
      has type (SosADL.SosADL.RangeType (Some min) (Some max)) in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ (SosADL.SosADL.RangeType (Some l__min) (Some l__max)))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ (SosADL.SosADL.RangeType (Some r__min) (Some r__max)))
      (p5: (SosADL.SosADL.IntegerValue (Some 1%Z)) <= r__min)
      (p6: min <= (SosADL.SosADL.BinaryExpression (Some l__min) (Some "/") (Some r__min)))
      (p7: min <= (SosADL.SosADL.BinaryExpression (Some l__min) (Some "/") (Some r__max)))
      (p8: min <= (SosADL.SosADL.BinaryExpression (Some l__max) (Some "/") (Some r__min)))
      (p9: min <= (SosADL.SosADL.BinaryExpression (Some l__max) (Some "/") (Some r__max)))
      (pa: (SosADL.SosADL.BinaryExpression (Some l__min) (Some "/") (Some r__min)) <= max)
      (pb: (SosADL.SosADL.BinaryExpression (Some l__min) (Some "/") (Some r__max)) <= max)
      (pc: (SosADL.SosADL.BinaryExpression (Some l__max) (Some "/") (Some r__min)) <= max)
      (pd: (SosADL.SosADL.BinaryExpression (Some l__max) (Some "/") (Some r__max)) <= max)
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "/") (Some r))
      has type (SosADL.SosADL.RangeType (Some min) (Some max)) in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ (SosADL.SosADL.RangeType (Some l__min) (Some l__max)))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ (SosADL.SosADL.RangeType (Some r__min) (Some r__max)))
      (p5: (r__max <= (SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z))))))
      (p6: min <= (SosADL.SosADL.BinaryExpression (Some l__min) (Some "/") (Some r__min)))
      (p7: min <= (SosADL.SosADL.BinaryExpression (Some l__min) (Some "/") (Some r__max)))
      (p8: min <= (SosADL.SosADL.BinaryExpression (Some l__max) (Some "/") (Some r__min)))
      (p9: min <= (SosADL.SosADL.BinaryExpression (Some l__max) (Some "/") (Some r__max)))
      (pa: (SosADL.SosADL.BinaryExpression (Some l__min) (Some "/") (Some r__min)) <= max)
      (pb: (SosADL.SosADL.BinaryExpression (Some l__min) (Some "/") (Some r__max)) <= max)
      (pc: (SosADL.SosADL.BinaryExpression (Some l__max) (Some "/") (Some r__min)) <= max)
      (pd: (SosADL.SosADL.BinaryExpression (Some l__max) (Some "/") (Some r__max)) <= max)
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "/") (Some r))
      has type (SosADL.SosADL.RangeType (Some min) (Some max)) in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ (SosADL.SosADL.RangeType (Some l__min) (Some l__max)))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ (SosADL.SosADL.RangeType (Some r__min) (Some r__max)))
      (p5: range_modulo_min l__min l__max r__min r__max min)
      (p6: range_modulo_max l__min l__max r__min r__max max)
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "mod") (Some r))
      has type (SosADL.SosADL.RangeType (Some min) (Some max)) in Gamma

| type_expression_Implies:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ SosADL.SosADL.BooleanType)
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ SosADL.SosADL.BooleanType)
    ,
     expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "implies") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Or:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ SosADL.SosADL.BooleanType)
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ SosADL.SosADL.BooleanType)
    ,
     expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "or") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Xor:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ SosADL.SosADL.BooleanType)
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ SosADL.SosADL.BooleanType)
    ,
     expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "xor") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_And:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (l__tau: SosADL.SosADL.t_DataType)
      (r: SosADL.SosADL.t_Expression)
      (r__tau: SosADL.SosADL.t_DataType)
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ SosADL.SosADL.BooleanType)
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ SosADL.SosADL.BooleanType)
    ,
     expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "and") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ SosADL.SosADL.RangeType (Some l__min) (Some l__max))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ SosADL.SosADL.RangeType (Some r__min) (Some r__max))
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "=") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ SosADL.SosADL.RangeType (Some l__min) (Some l__max))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ SosADL.SosADL.RangeType (Some r__min) (Some r__max))
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "<>") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ SosADL.SosADL.RangeType (Some l__min) (Some l__max))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ SosADL.SosADL.RangeType (Some r__min) (Some r__max))
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "<") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ SosADL.SosADL.RangeType (Some l__min) (Some l__max))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ SosADL.SosADL.RangeType (Some r__min) (Some r__max))
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some "<=") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ SosADL.SosADL.RangeType (Some l__min) (Some l__max))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ SosADL.SosADL.RangeType (Some r__min) (Some r__max))
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some ">") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

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
      (p1: expression l has type l__tau in Gamma)
      (p2: l__tau </ SosADL.SosADL.RangeType (Some l__min) (Some l__max))
      (p3: expression r has type r__tau in Gamma)
      (p4: r__tau </ SosADL.SosADL.RangeType (Some r__min) (Some r__max))
    ,
      expression node (SosADL.SosADL.BinaryExpression (Some l) (Some ">=") (Some r)) has type SosADL.SosADL.BooleanType in Gamma

| type_expression_Ident:
    forall (Gamma: env)
      (x: string)
      (tau: SosADL.SosADL.t_DataType)
      (p: contains Gamma x (EVariable tau))
    ,
      expression node (SosADL.SosADL.IdentExpression (Some x)) has type tau in Gamma

(** %\note{%According to the current implementation of environment, the
 rule [type_expression_MethodCall] accept any method declaration with
 the correct name and compatible parameter and [self] types. With this
 definition, the type checker can freely choose any such method
 declaration.%}% *)

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
      (p1: expression self has type t in Gamma)
      (p2: binds Gamma (EType typeDecl tau methods))
      (p4: t </ tau)
      (p5: method name defined in methods with tau parameters formalparams returns ret)
      (p6: for each fp p of formalparams params,
           (exists t, SosADL.SosADL.FormalParameter_type fp = Some t
                 /\ (exists tp, (expression p has type tp in Gamma)
                          /\ tp </ t)))
    ,
      expression node (SosADL.SosADL.MethodCall (Some self) (Some name) params) has type ret in Gamma


| type_expression_Tuple:
    forall (Gamma: env)
      (elts: list SosADL.SosADL.t_TupleElement)
      (typ: list SosADL.SosADL.t_FieldDecl)
      (p1: values (SosADL.SosADL.TupleElement_label x) for x of elts are distinct according to option_string_dec)
      (p2: for each e f of elts typ,
         SosADL.SosADL.TupleElement_label e = SosADL.SosADL.FieldDecl_name f)
      (p3: for each e f of elts typ,
         (exists (e': SosADL.SosADL.t_Expression),
            SosADL.SosADL.TupleElement_value e = Some e'
            /\ exists (f': SosADL.SosADL.t_DataType),
                SosADL.SosADL.FieldDecl_type f = Some f'
                /\ expression e' has type f' in Gamma))
    ,
      expression node (SosADL.SosADL.Tuple elts) has type (SosADL.SosADL.TupleType typ) in Gamma

| type_expression_Field:
    forall (Gamma: env)
      (self: SosADL.SosADL.t_Expression)
      (tau: list SosADL.SosADL.t_FieldDecl)
      (name: string)
      (tau__f: SosADL.SosADL.t_DataType)
      (p1: expression self has type (SosADL.SosADL.TupleType tau) in Gamma)
      (p2: field_type tau name = Some tau__f)
    ,
      expression node (SosADL.SosADL.Field (Some self) (Some name)) has type tau__f in Gamma

| type_expression_Sequence:
    forall (Gamma: env)
      (elts: list SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (p1: for each e of elts,
           exists t, (expression e has type t in Gamma)
                /\ t </ tau)
    ,
      expression node (SosADL.SosADL.Sequence elts) has type (SosADL.SosADL.SequenceType (Some tau)) in Gamma

| type_expression_Map:
    forall (Gamma: env)
      (obj: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (x: string)
      (e: SosADL.SosADL.t_Expression)
      (tau__e: SosADL.SosADL.t_DataType)
      (p1: expression obj has type (SosADL.SosADL.SequenceType (Some tau)) in Gamma)
      (p2: expression e has type tau__e in Gamma [| x <- EVariable tau |])
    ,
      expression node (SosADL.SosADL.Map (Some obj) (Some x) (Some e)) has type (SosADL.SosADL.SequenceType (Some tau__e)) in Gamma

| type_expression_Select:
    forall (Gamma: env)
      (obj: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (x: string)
      (e: SosADL.SosADL.t_Expression)
      (p1: expression obj has type (SosADL.SosADL.SequenceType (Some tau)) in Gamma)
      (p2: expression e has type SosADL.SosADL.BooleanType in Gamma [| x <- EVariable tau |])
    ,
      expression node (SosADL.SosADL.Select (Some obj) (Some x) (Some e)) has type (SosADL.SosADL.SequenceType (Some tau)) in Gamma

(** %\todo{%[CallExpression], [UnobservableValue], [Unify], [Relay]
and [Quantify] are not handled yet, but they are not allowed in any kind of expression.%}% *)

where "'expression' e 'has' 'type' t 'in' Gamma" := (type_expression Gamma e t)
and "'expression' 'node' e 'has' 'type' t 'in' Gamma" := (type_expression_node Gamma e t)
.


(** * Conditional statements *)

Inductive smallest: SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> Prop :=
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

Inductive greatest: SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> Prop :=
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

Definition negated_comparison op :=
  match op with
  | "<" => Some ">="
  | "<=" => Some ">"
  | ">" => Some "<="
  | ">=" => Some "<"
  | _ => None
  end.

Definition symmetric_comparison op :=
  match op with
  | "<" => Some ">"
  | "<=" => Some ">="
  | ">" => Some "<"
  | ">=" => Some "<="
  | _ => None
  end.

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
      condition_true Gamma (SosADL.SosADL.UnaryExpression (Some "not") (Some c)) Gamma

| condition_true_and:
    forall (Gamma: env)
      (c1: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (c2: SosADL.SosADL.t_Expression)
      (Gamma2: env)
      (p1: condition_true Gamma c1 Gamma1)
      (p2: condition_true Gamma1 c2 Gamma2)
    ,
      condition_true Gamma (SosADL.SosADL.BinaryExpression (Some c1) (Some "and") (Some c2)) Gamma2

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
      (p1: expression (SosADL.SosADL.IdentExpression (Some x)) has type (SosADL.SosADL.RangeType (Some x_min) (Some x_max)) in Gamma)
      (p2: expression r has type (SosADL.SosADL.RangeType (Some r_min) (Some r_max)) in Gamma)
      (p3: smallest x_max_ x_max (SosADL.SosADL.BinaryExpression (Some r_max) (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))))
      (p4: type (SosADL.SosADL.RangeType (Some x_min) (Some x_max_)) looks fine)
      (p5: condition_true (Gamma [| x <- EVariable (SosADL.SosADL.RangeType (Some x_min) (Some x_max_)) |]) (SosADL.SosADL.BinaryExpression (Some r) (Some ">") (Some (SosADL.SosADL.IdentExpression (Some x)))) Gamma1)
    ,
      condition_true Gamma (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.IdentExpression (Some x))) (Some "<") (Some r)) Gamma1

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
      (p1: expression (SosADL.SosADL.IdentExpression (Some x)) has type (SosADL.SosADL.RangeType (Some x_min) (Some x_max)) in Gamma)
      (p2: expression r has type (SosADL.SosADL.RangeType (Some r_min) (Some r_max)) in Gamma)
      (p3: smallest x_max_ x_max r_max)
      (p4: type (SosADL.SosADL.RangeType (Some x_min) (Some x_max_)) looks fine)
      (p5: condition_true (Gamma [| x <- EVariable (SosADL.SosADL.RangeType (Some x_min) (Some x_max_)) |]) (SosADL.SosADL.BinaryExpression (Some r) (Some ">=") (Some (SosADL.SosADL.IdentExpression (Some x)))) Gamma1)
    ,
      condition_true Gamma (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.IdentExpression (Some x))) (Some "<=") (Some r)) Gamma1

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
      (p1: expression (SosADL.SosADL.IdentExpression (Some x)) has type (SosADL.SosADL.RangeType (Some x_min) (Some x_max)) in Gamma)
      (p2: expression r has type (SosADL.SosADL.RangeType (Some r_min) (Some r_max)) in Gamma)
      (p3: greatest x_min_ x_min r_min)
      (p4: type (SosADL.SosADL.RangeType (Some x_min_) (Some x_max)) looks fine)
      (p5: condition_true (Gamma [| x <- EVariable (SosADL.SosADL.RangeType (Some x_min_) (Some x_max)) |]) (SosADL.SosADL.BinaryExpression (Some r) (Some "<=") (Some (SosADL.SosADL.IdentExpression (Some x)))) Gamma1)
    ,
      condition_true Gamma (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.IdentExpression (Some x))) (Some ">=") (Some r)) Gamma1

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
      (p1: expression (SosADL.SosADL.IdentExpression (Some x)) has type (SosADL.SosADL.RangeType (Some x_min) (Some x_max)) in Gamma)
      (p2: expression r has type (SosADL.SosADL.RangeType (Some r_min) (Some r_max)) in Gamma)
      (p3: greatest x_min_ x_min (SosADL.SosADL.BinaryExpression (Some r_min) (Some "+") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))))
      (p4: type (SosADL.SosADL.RangeType (Some x_min_) (Some x_max)) looks fine)
      (p5: condition_true (Gamma [| x <- EVariable (SosADL.SosADL.RangeType (Some x_min_) (Some x_max)) |]) (SosADL.SosADL.BinaryExpression (Some r) (Some "<") (Some (SosADL.SosADL.IdentExpression (Some x)))) Gamma1)
    ,
      condition_true Gamma (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.IdentExpression (Some x))) (Some ">") (Some r)) Gamma1

| condition_true_sym:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (op: string)
      (r: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: condition_true Gamma (SosADL.SosADL.BinaryExpression (Some r) (symmetric_comparison op) (Some l)) Gamma1)
    ,
      condition_true Gamma (SosADL.SosADL.BinaryExpression (Some l) (Some op) (Some r)) Gamma1

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
      condition_false Gamma (SosADL.SosADL.UnaryExpression (Some "not") (Some c)) Gamma

| condition_false_or:
    forall (Gamma: env)
      (c1: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (c2: SosADL.SosADL.t_Expression)
      (Gamma2: env)
      (p1: condition_false Gamma c1 Gamma1)
      (p2: condition_false Gamma1 c2 Gamma2)
    ,
      condition_false Gamma (SosADL.SosADL.BinaryExpression (Some c1) (Some "or") (Some c2)) Gamma2

| condition_false_cmp:
    forall (Gamma: env)
      (l: SosADL.SosADL.t_Expression)
      (op: string)
      (r: SosADL.SosADL.t_Expression)
      (Gamma1: env)
      (p1: condition_true Gamma (SosADL.SosADL.BinaryExpression (Some l) (negated_comparison op) (Some r)) Gamma1)
    ,
      condition_false Gamma (SosADL.SosADL.BinaryExpression (Some l) (Some op) (Some r)) Gamma1
.


(** ** Mediator *)

(** %\note{%By choice, the elements declared in the mediator are typed
in order by the set rules for [type_mediatorblock].%}% *)

Inductive type_mediator: env -> SosADL.SosADL.t_MediatorDecl -> Prop :=
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


(** ** Architecture behavior*)

(* %\todo{%TBD%}% *)

with type_archbehavior: env ->  SosADL.SosADL.t_ArchBehaviorDecl -> Prop :=

(** ** Assertion *)

(** %\todo{TBD}% *)

with type_assertion: env -> SosADL.SosADL.t_AssertionDecl -> Prop :=

(** ** Protocol *)

(** %\todo{TBD}% *)

with type_protocol: env -> SosADL.SosADL.t_ProtocolDecl -> Prop :=


where "'mediator' m 'well' 'typed' 'in' Gamma" := (type_mediator Gamma m)
and "'mediatorblock' m 'well' 'typed' 'in' Gamma" := (type_mediatorblock Gamma m)
and "'architecture' a 'well' 'typed' 'in' Gamma" := (type_architecture Gamma a)
and "'architectureblock' a 'well' 'typed' 'in' Gamma" := (type_architectureblock Gamma a)
and "'archbehavior' b 'well' 'typed' 'in' Gamma" := (type_archbehavior Gamma b)
and "'assertion' a 'well' 'typed' 'in' Gamma" := (type_assertion Gamma a)
and "'protocol' p 'well' 'typed' 'in' Gamma" := (type_protocol Gamma p)
.

(** ** Body *)

Inductive type_bodyprefix (R: env -> Prop): env -> SosADL.SosADL.t_BehaviorStatement -> Prop :=
(** %\note{%The typing rules enforce that statements [RepeatBehavior],
[ChooseBehavior], [RecursiveCall] and [Done] must be the last
statement of a sequence. [IfThenElse] statement may or may not be the last statement of a sequence.
%}% *)

| type_bodyprefix_DoExpr:
    forall
      (Gamma: env)
      (e: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (p1: expression e has type tau in Gamma)
      (p2: R Gamma)
    ,
      statement (SosADL.SosADL.DoExprBehavior (Some e)) prefixing R well typed in Gamma

| type_bodyprefix_Valuing_inferred:
    forall
      (Gamma: env)
      (x: string)
      (e: SosADL.SosADL.t_Expression)
      (tau__e: SosADL.SosADL.t_DataType)
      (p1: expression e has type tau__e in Gamma)
      (p2: R (Gamma [| x <- EVariable tau__e |]))
    ,
      statement (SosADL.SosADL.ValuingBehavior (Some (SosADL.SosADL.Valuing (Some x) None (Some e)))) prefixing R well typed in Gamma

| type_bodyprefix_Valuing_typed:
    forall
      (Gamma: env)
      (x: string)
      (e: SosADL.SosADL.t_Expression)
      (tau: SosADL.SosADL.t_DataType)
      (tau__e: SosADL.SosADL.t_DataType)
      (p1: expression e has type tau__e in Gamma)
      (p2: tau__e </ tau)
      (p3: R (Gamma [| x <- EVariable tau |]))
    ,
      statement (SosADL.SosADL.ValuingBehavior (Some (SosADL.SosADL.Valuing (Some x) (Some tau) (Some e)))) prefixing R well typed in Gamma


       (*

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

| type_ForEach:
    forall Gamma x tau vals b l,
      (expression vals has type (SosADL.SosADL.SequenceType (Some tau)) in Gamma)
      /\ (body b well typed in Gamma [| x <- EVariable tau |])
      /\ (body l well typed in Gamma)
      ->
      body (SosADL.SosADL.ForEachBehavior (Some x) (Some vals) (Some (SosADL.SosADL.Behavior b)) :: l) well typed in Gamma

| type_TellStatement:
    forall Gamma name e l,
      (expression e has type SosADL.SosADL.BooleanType in Gamma)
      /\ (body l well typed in Gamma)
      ->
      body (SosADL.SosADL.BehaviorStatement_TellAssertion (Some name) (Some e) :: l) well typed in Gamma
*)

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

       (*
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
      /\ (tau </ conn__tau)
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
      /\ (tau </ conn__tau)
      /\ (body l well typed in Gamma)
      ->
      body (SosADL.SosADL.Action (Some (SosADL.SosADL.ComplexName (gd :: conn :: nil)))
                       (Some (SosADL.SosADL.SendAction (Some e))) :: l)
           well typed in Gamma


        *)

where "'statement' b 'prefixing' r 'well' 'typed' 'in' Gamma" := (type_bodyprefix r Gamma b)
.

Inductive type_nonfinalbody: env -> list SosADL.SosADL.t_BehaviorStatement -> Prop :=

| type_nonfinalbody_empty:
    forall
      (Gamma: env)
    ,
      nonfinal body nil well typed in Gamma

| type_nonfinalbody_prefix:
    forall
      (Gamma: env)
      (s: SosADL.SosADL.t_BehaviorStatement)
      (l: list SosADL.SosADL.t_BehaviorStatement)
      (p1: statement s prefixing (fun g => nonfinal body l well typed in g)
                     well typed in Gamma)
    ,
      nonfinal body (s :: l) well typed in Gamma
where "'nonfinal' 'body' b 'well' 'typed' 'in' Gamma" := (type_nonfinalbody Gamma b)
.

Inductive type_finalbody: env -> list SosADL.SosADL.t_BehaviorStatement -> Prop :=

| type_finalbody_prefix:
    forall
      (Gamma: env)
      (s: SosADL.SosADL.t_BehaviorStatement)
      (l: list SosADL.SosADL.t_BehaviorStatement)
      (p1: statement s prefixing (fun g => final body l well typed in g)
                     well typed in Gamma)
    ,
      final body (s :: l) well typed in Gamma

| type_finalbody_Repeat:
    forall
      (Gamma: env)
      (b: list SosADL.SosADL.t_BehaviorStatement)
      (p1: nonfinal body b well typed in Gamma)
    ,
      final body (SosADL.SosADL.RepeatBehavior (Some (SosADL.SosADL.Behavior b)) :: nil) well typed in Gamma

| type_finalbody_IfThenElse_general:
    forall
      (Gamma: env)
      (c: SosADL.SosADL.t_Expression)
      (Gammat: env)
      (t: list SosADL.SosADL.t_BehaviorStatement)
      (Gammae: env)
      (e: list SosADL.SosADL.t_BehaviorStatement)
      (p1: expression c has type SosADL.SosADL.BooleanType in Gamma)
      (p2: condition_true Gamma c Gammat)
      (p3: final body t well typed in Gammat)
      (p4: condition_false Gamma c Gammae)
      (p5: final body e well typed in Gammae)
    ,
      final body (SosADL.SosADL.IfThenElseBehavior (Some c) (Some (SosADL.SosADL.Behavior t)) (Some (SosADL.SosADL.Behavior e)) :: nil)
           well typed in Gamma

| type_finalbody_Done:
    forall
      (Gamma: env)
    ,
      final body (SosADL.SosADL.DoneBehavior :: nil) well typed in Gamma

| type_finalbody_RecursiveCall:
    forall
      (Gamma: env)
    ,
      final body ((SosADL.SosADL.RecursiveCall nil) :: nil) well typed in Gamma

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
      behavior (SosADL.SosADL.BehaviorDecl (Some name) (Some (SosADL.SosADL.Behavior b))) well typed in Gamma

where "'behavior' b 'well' 'typed' 'in' Gamma" := (type_behavior Gamma b)
.

(**
 ** Formal parameters
 *)

Definition formalParameter_to_EVariable p :=
  match SosADL.SosADL.FormalParameter_type p with
  | None => None
  | Some t => Some (EVariable t)
  end.

Inductive type_formalParameter: env -> SosADL.SosADL.t_FormalParameter -> SosADL.SosADL.t_FormalParameter -> env -> Prop :=

| type_FormalParameter_typed:
    forall (Gamma: env)
      (n: string)
      (t: SosADL.SosADL.t_DataType)
      (t1: SosADL.SosADL.t_DataType)
      (Gamma1: env)
      (p1: type t is t1 in Gamma)
    ,
      type_formalParameter Gamma (SosADL.SosADL.FormalParameter (Some n) (Some t))
                           (SosADL.SosADL.FormalParameter (Some n) (Some t1)) Gamma1
.

Definition type_formalParameters Gamma l l1 Gamma1 :=
  @mutually_translate _ type_formalParameter SosADL.SosADL.FormalParameter_name formalParameter_to_EVariable
                      Gamma l l1 Gamma1.

(*
Definition type_formalParameters Gamma l l' Gamma1 :=
  (for each p p' of l l',
   SosADL.SosADL.FormalParameter_name p = SosADL.SosADL.FormalParameter_name p'
   /\ exists t, SosADL.SosADL.FormalParameter_type p = Some t
          /\ exists t', SosADL.SosADL.FormalParameter_type p' = Some t'
                  /\ type t is t' in Gamma)
  /\ @mutually _ (fun gamma p _ => True)
              SosADL.SosADL.FormalParameter_name
              formalParameter_to_EVariable
              Gamma l' Gamma1.
*)

(**
 ** Gates and duties

Gates and duties are typed in a similar way.
 *)

(** *** Connection *)

Inductive type_connection: env -> SosADL.SosADL.t_Connection -> SosADL.SosADL.t_Connection -> env -> Prop :=

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
      type_connection Gamma (SosADL.SosADL.Connection (Some k) (Some name) (Some m) (Some t))
                      (SosADL.SosADL.Connection (Some k) (Some name) (Some m) (Some t1)) Gamma1
.

Definition type_connections Gamma l l1 Gamma1 :=
  @mutually_translate _ type_connection SosADL.SosADL.Connection_name (fun x => Some (EConnection x))
                      Gamma l l1 Gamma1.

Inductive type_gate: env -> SosADL.SosADL.t_GateDecl -> SosADL.SosADL.t_GateDecl -> env -> Prop :=
| type_GateDecl:
    forall (Gamma: env)
      (name: string)
      (conns: list SosADL.SosADL.t_Connection)
      (conns1: list SosADL.SosADL.t_Connection)
      (Gamma2: env)
      (p: SosADL.SosADL.t_ProtocolDecl)
      (Gamma1: env)
      (p1: type_connections Gamma conns conns1 Gamma2)
      (p2: protocol p well typed in Gamma2)
    ,
      type_gate Gamma (SosADL.SosADL.GateDecl (Some name) conns (Some p))
                (SosADL.SosADL.GateDecl (Some name) conns1 (Some p)) Gamma1
.

Definition gateDecl_to_EGateOrDuty g :=
  Some (EGateOrDuty (SosADL.SosADL.GateDecl_connections g)).

Definition type_gates Gamma l Gamma1 :=
  exists l1,
    @mutually_translate _ type_gate SosADL.SosADL.GateDecl_name gateDecl_to_EGateOrDuty
                        Gamma l l1 Gamma1.

(*
Inductive type_duty: env -> SosADL.SosADL.t_DutyDecl -> Prop :=
| type_DutyDecl:
    forall Gamma name conns a p,
      (protocol p well typed in Gamma)
      /\ (values (SosADL.SosADL.Connection_name c) for c of conns are distinct according to option_string_dec)
      /\ (for each c of conns, connection c well typed in Gamma)
      /\ (assertion a well typed in Gamma)
      ->
      duty (SosADL.SosADL.DutyDecl (Some name) conns (Some a) (Some p)) well typed in Gamma
where "'duty' d 'well' 'typed' 'in' Gamma" := (type_duty Gamma d)
.
*)

(** ** Valuings *)
Inductive type_valuing: env -> SosADL.SosADL.t_Valuing -> env -> Prop :=

| type_Valuing_typed:
    forall (Gamma: env)
      (x: string)
      (tau: SosADL.SosADL.t_DataType)
      (e: SosADL.SosADL.t_Expression)
      (tau__e: SosADL.SosADL.t_DataType)
      (p1: expression e has type tau__e in Gamma)
      (p2: tau__e </ tau)
    ,
      valuing (SosADL.SosADL.Valuing (Some x) (Some tau) (Some e))
              well typed in Gamma
                              yields to (Gamma [| x <- EVariable tau |])

| type_Valuing_inferred:
    forall (Gamma: env)
      (x: string)
      (e: SosADL.SosADL.t_Expression)
      (tau__e: SosADL.SosADL.t_DataType)
      (p1: expression e has type tau__e in Gamma)
    ,
      valuing (SosADL.SosADL.Valuing (Some x) None (Some e))
              well typed in Gamma
                              yields to (Gamma [| x <- EVariable tau__e |])

where "'valuing' v 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1" := (type_valuing Gamma v Gamma1)
.

Definition type_valuings Gamma l Gamma1 := @incrementally _ type_valuing Gamma l Gamma1.

(** ** Function declaration *)

Inductive type_function: env -> SosADL.SosADL.t_FunctionDecl -> env -> Prop :=

(** %\note{%Since the language does not allow conditional expression, permitting (mutually) recursive functions is irrelevant.%}% *)

(** %\note{%Since the concrete grammar restricts all the functions to be methods, only this case is taken into account.%}% *)

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
      (p1: Gamma [| dataTypeName |] = Some (EType dataTypeDecl dataTypeReal dataTypeMethods))
      (p2: type rettype is rettype' in Gamma)
      (p3: type_formalParameters Gamma
                                 (SosADL.SosADL.FormalParameter
                                    (Some dataName)
                                    (Some (SosADL.SosADL.NamedType (Some dataTypeName))) :: params)
                                 (SosADL.SosADL.FormalParameter
                                    (Some dataName)
                                    (Some dataTypeReal) :: params')
                                 Gammap)
      (p4: type_valuings Gammap vals Gammav)
      (p5: expression retexpr has type tau in Gammav)
      (p6: tau </ rettype')
      (p7: Gamma1 = Gamma [| dataTypeName <- EType dataTypeDecl dataTypeReal
                                          ((SosADL.SosADL.FunctionDecl
                                              (Some (SosADL.SosADL.FormalParameter
                                                       (Some dataName)
                                                       (Some dataTypeReal)))
                                              (Some name) params' (Some rettype') vals (Some retexpr)) :: dataTypeMethods) |])
    ,
      function (SosADL.SosADL.FunctionDecl
                  (Some (SosADL.SosADL.FormalParameter
                           (Some dataName)
                           (Some (SosADL.SosADL.NamedType (Some dataTypeName)))))
                  (Some name) params (Some rettype) vals (Some retexpr))
               well typed in Gamma
               yields to Gamma1

where "'function' f 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1" := (type_function Gamma f Gamma1)
.

Definition type_functionDecls Gamma l Gamma1 := @incrementally _ type_function Gamma l Gamma1.

(** ** Data type declaration *)

Fixpoint name_is_fresh (e: env) (x: string): bool :=
  match e with
  | h :: r =>
    andb
    match (value h) with
    | EType _ (SosADL.SosADL.NamedType (Some n)) _ => (negb (string_eqb x n))
    | _ => true
    end (name_is_fresh r x)
  | nil => true
  end.

Inductive type_datatypeDecl: env -> SosADL.SosADL.t_DataTypeDecl -> env -> Prop :=
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
             SosADL.SosADL.FunctionDecl_data f = Some p
             /\ SosADL.SosADL.FormalParameter_type p = Some (SosADL.SosADL.NamedType (Some name)))
      (p3: type_functionDecls (Gamma [| name <- EType (SosADL.SosADL.DataTypeDecl (Some name) (Some t) funs) t' nil |]) funs Gamma1)
    ,
      typedecl (SosADL.SosADL.DataTypeDecl (Some name) (Some t) funs) well typed in Gamma yields to Gamma1

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
             SosADL.SosADL.FunctionDecl_data f = Some p
             /\ SosADL.SosADL.FormalParameter_type p = Some (SosADL.SosADL.NamedType (Some name)))
      (p3: type_functionDecls (Gamma [| name <- EType (SosADL.SosADL.DataTypeDecl (Some name) None funs) (SosADL.SosADL.NamedType (Some name')) nil |]) funs Gamma1)
    ,
      typedecl (SosADL.SosADL.DataTypeDecl (Some name) None funs) well typed in Gamma yields to Gamma1

where "'typedecl' t 'well' 'typed' 'in' Gamma 'yields' 'to' Gamma1" := (type_datatypeDecl Gamma t Gamma1)
.

Definition type_datatypeDecls Gamma l Gamma1 := @incrementally _ type_datatypeDecl Gamma l Gamma1.

(** ** System *)

(** %\note{%By choice, the elements declared in the system are typed
in order by the set rules for [type_systemblock].%}% *)

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
      (assrt: option SosADL.SosADL.t_AssertionDecl)
      (p1: type_formalParameters Gamma params params' Gamma1)
      (p2: type_datatypeDecls Gamma1 datatypes Gamma2)
      (p3: type_gates Gamma2 gates Gamma3)
      (p4: behavior bhv well typed in Gamma3)
      (p5: @optionally _ (fun g a => assertion a well typed in g) Gamma3 assrt)
    ,
      system (SosADL.SosADL.SystemDecl (Some name) params datatypes gates (Some bhv) assrt) well typed in Gamma
where "'system' s 'well' 'typed' 'in' Gamma" := (type_system Gamma s)
.

Definition type_systems Gamma l Gamma1 := @incrementally _ (simple_increment _ type_system SosADL.SosADL.SystemDecl_name (fun x => Some (ESystem x))) Gamma l Gamma1.

Definition type_mediators Gamma l Gamma1 := @incrementally _ (simple_increment _ type_mediator SosADL.SosADL.MediatorDecl_name (fun x => Some (EMediator x))) Gamma l Gamma1.
Definition type_architectures Gamma l Gamma1 := @incrementally _ (simple_increment _ type_architecture SosADL.SosADL.ArchitectureDecl_name (fun x => Some (EArchitecture x))) Gamma l Gamma1.

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
| type_SosADL_file:
    forall (i: list SosADL.SosADL.t_Import)
           (d: SosADL.SosADL.t_Unit)
           (p: unit d well typed in empty)
    ,
      SoSADL (SosADL.SosADL.SosADL i (Some d)) well typed
where "'SoSADL' a 'well' 'typed'" := (type_sosADL a)
.

