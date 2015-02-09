Require Import TypeSystem.
Require Import tests.testChoose10.

Import List.
Import AST.
Import ListNotations.
Import Utils.
Import String.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Theorem well_typed: SoSADL ast well typed.
Proof.
  unfold ast.
  apply type_SosADL.
  apply type_Library.
  apply type_EntityBlock_system with "test"; split.
  - apply type_SystemDecl; split.
    + apply Forall_nil.
    + apply type_SystemDecl_datatype_None
      with (RangeType (Some (IntegerValue (Some 3)))
                      (Some (IntegerValue (Some 4)))); repeat split.
      * apply type_DataTypeDecl_None.
      * { apply type_SystemDecl_gate with "gate1"; repeat split.
          - admit. (* TODO protocol *)
          - simpl. decide_nodup (Some_dec _ string_dec).
          - apply Forall_cons.
            + apply type_Connection.
              apply type_NamedType with (DataTypeDecl (Some "type1")
                                                      (Some (RangeType (Some (IntegerValue (Some 3)))
                                                                       (Some (IntegerValue (Some 4))))) []).
              vm_compute. reflexivity.
            + apply Forall_cons.
              * apply type_Connection.
                apply type_NamedType with (DataTypeDecl (Some "type1") (Some (RangeType (Some (IntegerValue (Some 3)))
                                                                                        (Some (IntegerValue (Some 4))))) []).
                vm_compute. reflexivity.
              * { apply Forall_cons.
                  - apply type_Connection.
                    apply type_NamedType with (DataTypeDecl (Some "type1") (Some (RangeType (Some (IntegerValue (Some 3)))
                                                                                            (Some (IntegerValue (Some 4))))) []).
                    vm_compute. reflexivity.
                  - apply Forall_cons.
                    + apply type_Connection.
                      apply type_NamedType with (DataTypeDecl (Some "type1") (Some (RangeType (Some (IntegerValue (Some 3)))
                                                                                              (Some (IntegerValue (Some 4))))) []).
                      vm_compute. reflexivity.
                    + apply Forall_cons.
                      * apply type_Connection.
                        apply type_NamedType with (DataTypeDecl (Some "type1") (Some (RangeType (Some (IntegerValue (Some 3)))
                                                                                                (Some (IntegerValue (Some 4))))) []).
                        vm_compute. reflexivity.
                      * apply Forall_nil. }
          - apply type_SystemDecl_None.
            apply type_BehaviorDecl.
            apply type_Choose.
            apply Forall_cons.
            + vm_compute.
              apply type_ReceiveStatement_InOut with
              ([{|
                   Environment.ListBasedEnv.key := "connection5";
                   Environment.ListBasedEnv.value := GDConnection
                                                      ModeTypeInout
                                                      (NamedType (Some "type1")) |};
                 {|
                   Environment.ListBasedEnv.key := "connection4";
                   Environment.ListBasedEnv.value := GDConnection
                                                      ModeTypeInout
                                                      (NamedType (Some "type1")) |};
                 {|
                   Environment.ListBasedEnv.key := "connection3";
                   Environment.ListBasedEnv.value := GDConnection
                                                      ModeTypeInout
                                                      (NamedType (Some "type1")) |};
                 {|
                   Environment.ListBasedEnv.key := "connection2";
                   Environment.ListBasedEnv.value := GDConnection
                                                      ModeTypeInout
                                                      (NamedType (Some "type1")) |};
                 {|
                   Environment.ListBasedEnv.key := "connection1";
                   Environment.ListBasedEnv.value := GDConnection
                                                      ModeTypeInout
                                                      (NamedType (Some "type1")) |}])
                   (NamedType (Some "type1")); repeat split.
              * apply type_EmptyBody.
            + apply Forall_cons.
              vm_compute.
              apply type_Valuing_None with (RangeType (Some (IntegerValue (Some 0)))
                                                      (Some (IntegerValue (Some 0)))); repeat split.
              * apply type_expression_IntegerValue.
              * { apply type_Choose.
                  apply Forall_cons.
                  - apply type_ReceiveStatement_InOut with
                    ([{|
                         Environment.ListBasedEnv.key := "connection5";
                         Environment.ListBasedEnv.value := GDConnection
                                                            ModeTypeInout
                                                            (NamedType (Some "type1")) |};
                       {|
                         Environment.ListBasedEnv.key := "connection4";
                         Environment.ListBasedEnv.value := GDConnection
                                                            ModeTypeInout
                                                            (NamedType (Some "type1")) |};
                       {|
                         Environment.ListBasedEnv.key := "connection3";
                         Environment.ListBasedEnv.value := GDConnection
                                                            ModeTypeInout
                                                            (NamedType (Some "type1")) |};
                       {|
                         Environment.ListBasedEnv.key := "connection2";
                         Environment.ListBasedEnv.value := GDConnection
                                                            ModeTypeInout
                                                            (NamedType (Some "type1")) |};
                       {|
                         Environment.ListBasedEnv.key := "connection1";
                         Environment.ListBasedEnv.value := GDConnection
                                                            ModeTypeInout
                                                            (NamedType (Some "type1")) |}])
                      (NamedType (Some "type1")); repeat split.
                    apply type_EmptyBody.
                  - apply Forall_cons.
                    + apply type_SendStatement_InOut with
                      ([{|
                           Environment.ListBasedEnv.key := "connection5";
                           Environment.ListBasedEnv.value := GDConnection
                                                              ModeTypeInout
                                                              (NamedType (Some "type1")) |};
                         {|
                           Environment.ListBasedEnv.key := "connection4";
                           Environment.ListBasedEnv.value := GDConnection
                                                              ModeTypeInout
                                                              (NamedType (Some "type1")) |};
                         {|
                           Environment.ListBasedEnv.key := "connection3";
                           Environment.ListBasedEnv.value := GDConnection
                                                              ModeTypeInout
                                                              (NamedType (Some "type1")) |};
                         {|
                           Environment.ListBasedEnv.key := "connection2";
                           Environment.ListBasedEnv.value := GDConnection
                                                              ModeTypeInout
                                                              (NamedType (Some "type1")) |};
                         {|
                           Environment.ListBasedEnv.key := "connection1";
                           Environment.ListBasedEnv.value := GDConnection
                                                              ModeTypeInout
                                                              (NamedType (Some "type1")) |}])
                        (NamedType (Some "type1"))
                        (RangeType (Some (IntegerValue (Some 3)))
                                   (Some (IntegerValue (Some 3)))); repeat split.
                      * apply type_expression_IntegerValue.
                      * { apply subtype_right with (RangeType (Some (IntegerValue (Some 3)))
                                                              (Some (IntegerValue (Some 4)))) []; split.
                          - vm_compute. reflexivity.
                          - apply subtype_range; split.
                            + apply Interpretation.In_Z with 3 3.
                              * vm_compute. reflexivity.
                              * vm_compute. reflexivity.
                              * reflexivity.
                            + apply Interpretation.In_Z with 3 4.
                              * vm_compute. reflexivity.
                              * vm_compute. reflexivity.
                              * vm_compute. discriminate. }
                      * apply type_EmptyBody.
                    + apply Forall_nil. }
              * { apply Forall_cons.
                  - apply type_SendStatement_InOut with
                    ([{|
                         Environment.ListBasedEnv.key := "connection5";
                         Environment.ListBasedEnv.value := GDConnection
                                                            ModeTypeInout
                                                            (NamedType (Some "type1")) |};
                       {|
                         Environment.ListBasedEnv.key := "connection4";
                         Environment.ListBasedEnv.value := GDConnection
                                                            ModeTypeInout
                                                            (NamedType (Some "type1")) |};
                       {|
                         Environment.ListBasedEnv.key := "connection3";
                         Environment.ListBasedEnv.value := GDConnection
                                                            ModeTypeInout
                                                            (NamedType (Some "type1")) |};
                       {|
                         Environment.ListBasedEnv.key := "connection2";
                         Environment.ListBasedEnv.value := GDConnection
                                                            ModeTypeInout
                                                            (NamedType (Some "type1")) |};
                       {|
                         Environment.ListBasedEnv.key := "connection1";
                         Environment.ListBasedEnv.value := GDConnection
                                                            ModeTypeInout
                                                            (NamedType (Some "type1")) |}])
                      (NamedType (Some "type1"))
                      (RangeType (Some (IntegerValue (Some 4)))
                                 (Some (IntegerValue (Some 4)))); repeat split.
                    + apply type_expression_IntegerValue.
                    + apply subtype_right with (RangeType (Some (IntegerValue (Some 3)))
                                                          (Some (IntegerValue (Some 4)))) []; split.
                      * vm_compute. reflexivity.
                      * { apply subtype_range; split.
                          - apply Interpretation.In_Z with 3 4.
                            + vm_compute. reflexivity.
                            + vm_compute. reflexivity.
                            + vm_compute. discriminate.
                          - apply Interpretation.In_Z with 4 4.
                            + vm_compute. reflexivity.
                            + vm_compute. reflexivity.
                            + reflexivity. }
                    + apply type_EmptyBody.
                  - apply Forall_nil. } }
  - split.
    + reflexivity.
    + apply type_EntityBlock.
Qed.

(*
Local Variables:
mode: coq
coding: utf-8
coq-load-path: ("..")
End:
 *)