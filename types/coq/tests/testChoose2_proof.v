Require Import TypeSystem.
Require Import tests.testChoose2.

Import List.
Import AST.
Import ListNotations.
Import Utils.
Import String.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition type1: t_DataType := RangeType (Some (IntegerValue (Some 1)))
                                         (Some (IntegerValue (Some 1))).

Theorem well_typed: SoSADL ast well typed.
Proof.
  unfold ast.
  apply type_SosADL.
  apply type_Library.
  apply type_EntityBlock_system with "test"; mysplit.
  - apply type_SystemDecl; mysplit.
    + apply Forall_nil.
    + apply type_SystemDecl_datatype_None with type1; mysplit.
      * apply type_DataTypeDecl_None.
      * { apply type_SystemDecl_gate with "gate1"; mysplit.
          - apply type_GateDecl; mysplit.
            + admit. (* TODO protocol *)
            + decide_nodup (Some_dec _ string_dec).
            + apply Forall_cons.
              * apply type_Connection.
                apply type_NamedType with (DataTypeDecl (Some "type1") (Some type1) []).
                reflexivity.
              * apply Forall_nil.
          - reflexivity.
          - apply type_SystemDecl_None.
            apply type_BehaviorDecl.
            apply type_Choose.
            apply Forall_cons.
            + eapply type_ReceiveStatement_InOut; mysplit.
              * reflexivity.
              * reflexivity.
              * apply type_EmptyBody.
            + apply Forall_cons.
              * { eapply type_SendStatement_InOut; mysplit.
                  - reflexivity.
                  - reflexivity.
                  - apply type_expression_IntegerValue.
                  - eapply subtype_right; mysplit.
                    + reflexivity.
                    + apply subtype_refl.
                  - apply type_EmptyBody. }
              * apply Forall_nil. }
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