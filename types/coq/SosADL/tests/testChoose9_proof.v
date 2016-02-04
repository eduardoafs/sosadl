Require Import TypeSystem.
Require Import TypingTactics.
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