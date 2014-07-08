Require Import List.
Require Import String.

Axiom environnement: Set -> Set.
Axiom env_contient: forall {A: Set}, environnement A -> string -> A -> Prop.
Axiom env_vide: forall {A: Set}, environnement A.

Axiom type_dans_env: Set.
Axiom fonction_dans_env: Set.
Axiom système_dans_env: Set.
Axiom médiateur_dans_env: Set.
Axiom constituants_dans_env: Set.

Definition environnement_types := environnement type_dans_env.
Definition environnement_fonctions := environnement fonction_dans_env.
Definition environnement_systèmes := environnement système_dans_env.
Definition environnement_médiateurs := environnement médiateur_dans_env.
Definition environnement_constituants := environnement constituants_dans_env.

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
| DataTypeDecl: datatype -> list functionDecl -> datatypeDecl
with datatype: Set :=
| NamedType: string -> datatype
| TupleType: list fieldDecl -> datatype
| SequenceType: datatype -> datatype
| RangeType: expression -> expression -> datatype
with fieldDecl: Set :=
| FieldDecl: string -> datatype -> fieldDecl
with functionDecl: Set :=
with systemDecl: Set :=
with mediatorDecl: Set :=
with architectureDecl: Set :=
with expression: Set :=
.

Definition name_of_fieldDecl f :=
  match f with
    | FieldDecl n _ => n
  end.

Definition type_of_fieldDecl f :=
  match f with
    | FieldDecl _ t => t
  end.

Definition environnement_variables := environnement datatype.

Reserved Notation "'SoSADL' a 'bien' 'typée'" (at level 200, no associativity).
Reserved Notation "'unité' u 'bien' 'typée'" (at level 200, no associativity).
Reserved Notation "'entité' u 'bien' 'typée'" (at level 200, no associativity).
Reserved Notation "'typedecl' t 'bien' 'typé' 'dans' Delta Phi Gamma" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, no associativity).
Reserved Notation "'type' t 'bien' 'typé' 'dans' Delta Phi Gamma" (at level 200, Delta at level 1, Phi at level 1, Gamma at level 1, no associativity).
Reserved Notation "'fonction' f 'bien' 'typée' 'dans' Delta Phi" (at level 200, Delta at level 1, Phi at level 1, no associativity).
Reserved Notation "'système' s 'bien' 'typé' 'dans' Delta Phi" (at level 200, Delta at level 1, Phi at level 1, no associativity).
Reserved Notation "'médiateur' m 'bien' 'typé' 'dans' Delta Phi" (at level 200, Delta at level 1, Phi at level 1, no associativity).
Reserved Notation "'archi' a 'bien' 'typée' 'dans' Delta Phi Sigma Mu" (at level 200, Delta at level 1, Phi at level 1, Sigma at level 1, Mu at level 1, no associativity).
Reserved Notation "'expr' e 'de' 'type' t 'Dans' Delta Phi Gamma Kappa" (at level 200, no associativity, Delta at level 1, Phi at level 1, Gamma at level 1, Kappa at level 1). (* TODO: pourquoi cela ne fonctionne-t-il pas avec le mot-clé 'dans'? *)

Notation "'pour' 'chaque' e 'de' l , p" :=
  (List.Forall (fun e => p) l)
    (at level 200, e ident, right associativity).

Notation "'tous' 'les' e 'pour' x 'de' f 'sont' 'différents'" :=
  (forall x, List.count_occ string_dec (List.map (fun x => e) f) x <= 1)
    (at level 200, x ident).

Axiom env_types: list datatypeDecl -> environnement_types.
Axiom env_fonctions: list functionDecl -> environnement_fonctions.
Axiom env_systèmes: list systemDecl -> environnement_systèmes.
Axiom env_médiateurs: list mediatorDecl -> environnement_médiateurs.



Inductive type_sosADL: sosADL -> Prop :=
| type_SosADL:
    forall i d,
      unité d bien typée
      ->
      SoSADL (SosADL i d) bien typée

with type_unit: unit -> Prop :=
| type_SoS:
    forall n e,
      entité e bien typée
      ->
      unité (SoS n e) bien typée

| type_Library:
    forall n e,
      entité e bien typée
      ->
      unité (Library n e) bien typée

with type_entityBlock: entityBlock -> Prop :=
| type_EntityBlock:
    forall datatypes functions systems mediators architectures,
      (pour chaque d de datatypes, typedecl d bien typé dans (env_types datatypes) (env_fonctions functions) env_vide)
      /\ (pour chaque f de functions, fonction f bien typée dans (env_types datatypes) (env_fonctions functions))
      /\ (pour chaque s de systems, système s bien typé dans (env_types datatypes) (env_fonctions functions))
      /\ (pour chaque m de mediators, médiateur m bien typé dans (env_types datatypes) (env_fonctions functions))
      /\ (pour chaque a de architectures, archi a bien typée dans  (env_types datatypes) (env_fonctions functions) (env_systèmes systems) (env_médiateurs mediators))
      ->
      entité (EntityBlock datatypes functions systems mediators architectures) bien typée

with type_datatypeDecl: environnement_types -> environnement_fonctions -> environnement_variables -> datatypeDecl -> Prop :=
| type_DataTypeDecl:
    forall Delta Phi Gamma t functions,
      (type t bien typé dans Delta Phi Gamma)
      /\ (pour chaque f de functions, fonction f bien typée dans Delta Phi)
      ->
      typedecl (DataTypeDecl t functions) bien typé dans Delta Phi Gamma

with type_datatype: environnement_types -> environnement_fonctions -> environnement_variables -> datatype -> Prop :=
| type_NamedType:
    forall Delta Phi Gamma n,
      (exists t, env_contient Delta n t)
      ->
      type (NamedType n) bien typé dans Delta Phi Gamma

| type_TupleType:
    forall Delta Phi Gamma fields,
      (tous les (name_of_fieldDecl f) pour f de fields sont différents)
      /\ (pour chaque f de fields, type (type_of_fieldDecl f) bien typé dans Delta Phi Gamma)
      ->
      type (TupleType fields) bien typé dans Delta Phi Gamma

| type_SequenceType:
    forall Delta Phi Gamma t,
      type t bien typé dans Delta Phi Gamma
      ->
      type (SequenceType t) bien typé dans Delta Phi Gamma

| type_RangeType:
    forall Delta Phi Gamma min max min__min min__max max__min max__max,
      (expr min de type (RangeType min__min min__max) Dans Delta Phi Gamma env_vide)
      /\ (expr max de type (RangeType max__min max__max) Dans Delta Phi Gamma env_vide)
      ->
      type (RangeType min max) bien typé dans Delta Phi Gamma

with type_function: environnement_types -> environnement_fonctions -> functionDecl -> Prop :=

with type_system: environnement_types -> environnement_fonctions -> systemDecl -> Prop :=

with type_mediator: environnement_types -> environnement_fonctions -> mediatorDecl -> Prop :=

with type_architecture: environnement_types -> environnement_fonctions -> environnement_systèmes -> environnement_médiateurs -> architectureDecl -> Prop :=

with type_expression: environnement_types -> environnement_fonctions -> environnement_variables -> environnement_constituants -> expression -> datatype -> Prop :=


where "'SoSADL' a 'bien' 'typée'" := (type_sosADL a)
and "'unité' u 'bien' 'typée'" := (type_unit u)
and "'entité' e 'bien' 'typée'" := (type_entityBlock e)
and "'typedecl' d 'bien' 'typé' 'dans' Delta Phi Gamma" := (type_datatypeDecl Delta Phi Gamma d)
and "'type' d 'bien' 'typé' 'dans' Delta Phi Gamma" := (type_datatype Delta Phi Gamma d)
and "'fonction' f 'bien' 'typée' 'dans' Delta Phi" := (type_function Delta Phi f)
and "'système' s 'bien' 'typé' 'dans' Delta Phi" := (type_system Delta Phi s)
and "'médiateur' m 'bien' 'typé' 'dans' Delta Phi" := (type_mediator Delta Phi m)
and "'archi' a 'bien' 'typée' 'dans' Delta Phi Sigma Mu" := (type_architecture Delta Phi Sigma Mu a)
and "'expr' e 'de' 'type' t 'Dans' Delta Phi Gamma Kappa" := (type_expression Delta Phi Gamma Kappa e t)
.
