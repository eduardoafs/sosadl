Require Import TypeSystem.

Import List.
Import AST.
Import ListNotations.
Import Utils.
Import String.
Import Interpretation.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Ltac apply_type_ReceiveStatement :=
  let t G C X L Gamma :=
      let gd := (eval compute in (Environment.ListBasedEnv.get Gamma G)) in
      match constr:gd with
        | Some (EGateOrDuty ?E) =>
          let typ := (eval compute in (Environment.ListBasedEnv.get E C)) in
          match constr:typ with
            | Some (GDConnection SosADL.ModeTypeInout ?T) =>
              apply (type_ReceiveStatement_InOut Gamma G E C X T L)
            | Some (GDConnection SosADL.ModeTypeIn ?T) =>
              apply (type_ReceiveStatement_In Gamma G E C X T L)
            | _ => fail
          end
        | _ => fail
      end in
  match goal with
      [ |- body (Behavior_statements
                  (SosADL.Behavior
                     ((SosADL.Action
                         (Some (SosADL.ComplexName [?G; ?C]))
                         (Some (SosADL.ReceiveAction (Some ?X)))) :: ?L)))
               well typed in ?Gamma ]
      => t G C X L Gamma
    | [ |- body ((SosADL.Action
                   (Some (SosADL.ComplexName [?G; ?C]))
                   (Some (SosADL.ReceiveAction (Some ?X)))) :: ?L)
               well typed in ?Gamma ]
      => t G C X L Gamma
  end.

Ltac apply_type_SendStatement tau  :=
  let t G C V L Gamma :=
      let gd := (eval compute in (Environment.ListBasedEnv.get Gamma G)) in
      match constr:gd with
        | Some (EGateOrDuty ?E) =>
          let typ := (eval compute in (Environment.ListBasedEnv.get E C)) in
          match constr:typ with
            | Some (GDConnection SosADL.ModeTypeInout ?T) =>
              apply (type_SendStatement_InOut Gamma G E C T V tau L)
            | Some (GDConnection SosADL.ModeTypeOut ?T) =>
              apply (type_SendStatement_Out Gamma G E C T V tau L)
            | _ => fail
          end
        | _ => fail
      end in
  match goal with
      [ |- body (Behavior_statements
                  (SosADL.Behavior
                     ((SosADL.Action
                         (Some (SosADL.ComplexName [?G; ?C]))
                         (Some (SosADL.SendAction (Some ?V)))) :: ?L)))
               well typed in ?Gamma ]
      => t G C V L Gamma
    | [ |- body ((SosADL.Action
                   (Some (SosADL.ComplexName [?G; ?C]))
                   (Some (SosADL.SendAction (Some ?V)))) :: ?L)
        well typed in ?Gamma ]
      => t G C V L Gamma      
  end.

Ltac apply_subtype :=
  match goal with
    | [ |- ?L </ NamedType (Some ?N) under ?Gamma ]
      =>
      let t := (eval compute in (Environment.ListBasedEnv.get Gamma N)) in
      match constr:t with
        | Some (EType (DataTypeDecl (Some N) (Some ?R) ?F))
          =>
          apply (subtype_right Gamma L N R F)
      end
    | [ |- NamedType (Some ?N) </ ?R under ?Gamma ]
      =>
      let t := (eval compute in (Environment.ListBasedEnv.get Gamma N)) in
      match constr:t with
        | Some (EType (DataTypeDecl (Some N) (Some ?L) ?F))
          =>
          apply (subtype_right Gamma N R L F)
      end
  end.
