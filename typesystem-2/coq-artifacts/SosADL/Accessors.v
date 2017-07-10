Require Import SosADL.sosADL.

Definition ArchitectureDecl_name ad :=
  match ad with
  | sosADL_ArchitectureDecl_sosADL_ArchitectureDecl assertions behavior datatypes gates name parameters => name
  end.

Definition Connection_name c :=
  match c with
  | sosADL_Connection_sosADL_Connection environment mode name valueType => name
  end.

Definition DutyDecl_connections dd :=
  match dd with
  | sosADL_DutyDecl_sosADL_DutyDecl assertions connections name protocols => connections
  end.

Definition DutyDecl_name dd :=
  match dd with
  | sosADL_DutyDecl_sosADL_DutyDecl assertions connections name protocols => name
  end.

Definition FieldDecl_name fd :=
  match fd with
  | sosADL_FieldDecl_sosADL_FieldDecl name type => name
  end.

Definition FieldDecl_type fd :=
  match fd with
  | sosADL_FieldDecl_sosADL_FieldDecl name type => type
  end.

Definition FormalParameter_name fp :=
  match fp with
  | sosADL_FormalParameter_sosADL_FormalParameter name type => name
  end.

Definition FormalParameter_type fp :=
  match fp with
  | sosADL_FormalParameter_sosADL_FormalParameter name type => type
  end.

Definition FunctionDecl_data fd :=
  match fd with
  | sosADL_FunctionDecl_sosADL_FunctionDecl data expression name parameters type valuing => data
  end.

Definition FunctionDecl_name fd :=
  match fd with
  | sosADL_FunctionDecl_sosADL_FunctionDecl data expression name parameters type valuing => name
  end.

Definition FunctionDecl_parameters fd :=
  match fd with
  | sosADL_FunctionDecl_sosADL_FunctionDecl data expression name parameters type valuing => parameters
  end.

Definition FunctionDecl_type fd :=
  match fd with
  | sosADL_FunctionDecl_sosADL_FunctionDecl data expression name parameters type valuing => type
  end.

Definition GateDecl_connections gd :=
  match gd with
  | sosADL_GateDecl_sosADL_GateDecl connections name protocols => connections
  end.

Definition GateDecl_name gd :=
  match gd with
  | sosADL_GateDecl_sosADL_GateDecl connections name protocols => name
  end.

Definition MediatorDecl_name md :=
  match md with
  | sosADL_MediatorDecl_sosADL_MediatorDecl assertions assumptions behavior datatypes duties name parameters => name
  end.

Definition SystemDecl_name sd :=
  match sd with
  | sosADL_SystemDecl_sosADL_SystemDecl assertions behavior datatypes gates name parameters => name
  end.

Definition TupleElement_label te :=
  match te with
  | sosADL_TupleElement_sosADL_TupleElement label value => label
  end.

Definition TupleElement_value te :=
  match te with
  | sosADL_TupleElement_sosADL_TupleElement label value => value
  end.