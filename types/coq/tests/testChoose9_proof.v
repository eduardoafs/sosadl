Require Import TypeSystem.
Require Import tests.testChoose9.

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
  match goal with
      [ |- body (Behavior_statements
                  (SosADL.Behavior
                     ((SosADL.Action
                         (Some (SosADL.ComplexName [?G; ?C]))
                         (Some (SosADL.ReceiveAction (Some ?X)))) :: ?L)))
               well typed in ?Gamma ]
      =>
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
      end
  end.

Ltac apply_type_SendStatement tau  :=
  match goal with
      [ |- body (Behavior_statements
                  (SosADL.Behavior
                     ((SosADL.Action
                         (Some (SosADL.ComplexName [?G; ?C]))
                         (Some (SosADL.SendAction (Some ?V)))) :: ?l)))
               well typed in ?Gamma ]
      =>
      let gd := (eval compute in (Environment.ListBasedEnv.get Gamma G)) in
      match constr:gd with
        | Some (EGateOrDuty ?E) =>
          let typ := (eval compute in (Environment.ListBasedEnv.get E C)) in
          match constr:typ with
            | Some (GDConnection SosADL.ModeTypeInout ?T) =>
              apply (type_SendStatement_InOut Gamma G E C T V tau l)
            | Some (GDConnection SosADL.ModeTypeOut ?T) =>
              apply (type_SendStatement_Out Gamma G E C T V tau l)
            | _ => fail
          end
        | _ => fail
      end
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

Definition type1: t_DataType := RangeType (Some (IntegerValue (Some 3)))
                                         (Some (IntegerValue (Some 4))).

Theorem well_typed: SoSADL ast well typed.
Proof.
  apply type_SosADL.
  apply type_Library.
  apply (type_EntityBlock_system _ _ "test" _ _ _). mysplit.
  - apply type_SystemDecl. mysplit.
    + apply Forall_nil.
    + apply (type_SystemDecl_datatype_None _ _ _ type1 _ _ _ _ _). mysplit.
      * apply type_DataTypeDecl_None.
      * { apply (type_SystemDecl_gate _ _ _ "gate1" _ _ _). mysplit.
          - apply type_GateDecl. mysplit.
            + admit. (* TODO protocol *)
            + decide_nodup (Some_dec _ string_dec).
            + apply Forall_cons.
              * apply type_Connection.
                apply (type_NamedType _ _ (DataTypeDecl (Some "type1") (Some type1) [])).
                reflexivity.
              * { apply Forall_cons.
                  - apply type_Connection.
                    apply (type_NamedType _ _ (DataTypeDecl (Some "type1") (Some type1) [])).
                    reflexivity.
                  - apply Forall_cons.
                    + apply type_Connection.
                      apply (type_NamedType _ _ (DataTypeDecl (Some "type1") (Some type1) [])).
                      reflexivity.
                    + apply Forall_cons.
                      * apply type_Connection.
                        apply (type_NamedType _ _ (DataTypeDecl (Some "type1") (Some type1) [])).
                        reflexivity.
                      * { apply Forall_cons.
                          - apply type_Connection.
                            apply (type_NamedType _ _ (DataTypeDecl (Some "type1") (Some type1) [])).
                            reflexivity.
                          - apply Forall_nil. } }
          - reflexivity.
          - apply type_SystemDecl_None.
            apply type_BehaviorDecl.
            apply type_Choose.
            apply Forall_cons.
            + { apply_type_ReceiveStatement. mysplit.
                - reflexivity.
                - reflexivity.
                - apply type_EmptyBody. }
            + { apply Forall_cons.
                - apply type_Choose.
                  apply Forall_cons.
                  + apply_type_ReceiveStatement. mysplit.
                    * reflexivity.
                    * reflexivity.
                    * apply type_EmptyBody.
                  + apply Forall_cons.
                    * { apply_type_SendStatement (RangeType (Some (IntegerValue (Some 3)))
                                                            (Some (IntegerValue (Some 3)))). mysplit.
                        - reflexivity.
                        - reflexivity.
                        - apply type_expression_IntegerValue.
                        - { apply_subtype. mysplit.
                            - reflexivity.
                            - apply subtype_range. mysplit.
                              + decide_in_Z.
                              + decide_in_Z. }
                        - apply type_EmptyBody. }
                    * apply Forall_nil.
                - apply Forall_cons.
                  + apply_type_SendStatement (RangeType (Some (IntegerValue (Some 4)))
                                                        (Some (IntegerValue (Some 4)))). mysplit.
                    * reflexivity.
                    * reflexivity.
                    * apply type_expression_IntegerValue.
                    * { apply_subtype. mysplit.
                        - reflexivity.
                        - apply subtype_range. mysplit.
                          + decide_in_Z.
                          + decide_in_Z. }
                    * apply type_EmptyBody.
                  + apply Forall_nil. } }
  - reflexivity.
  - apply type_EntityBlock.
Qed.

(*
Local Variables:
mode: coq
coding: utf-8
coq-load-path: ("..")
End:
 *)