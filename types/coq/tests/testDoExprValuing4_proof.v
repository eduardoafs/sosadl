Require Import TypeSystem.
Require Import TypingTactics.
Require Import tests.testDoExprValuing4.

Import List.
Import AST.
Import ListNotations.
Import Utils.
Import String.
Import Interpretation.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Axiom type1: t_DataType.

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
              * apply Forall_nil.
          - reflexivity.
          - apply type_SystemDecl_None.
            apply type_BehaviorDecl.
            apply (type_Valuing_Some _ _ _ _ (RangeType (Some (IntegerValue (Some 1)))
                                                        (Some (IntegerValue (Some 1)))) _).
            mysplit.
            + apply type_expression_IntegerValue.
            + apply subtype_range. mysplit.
              * decide_in_Z.
              * decide_in_Z.
            + apply (type_DoExpr _ _ (RangeType (Some (BinaryExpression (Some (IntegerValue (Some 0))) (Some "+") (Some (IntegerValue (Some 0)))))
                                                (Some (BinaryExpression (Some (IntegerValue (Some 2))) (Some "+") (Some (IntegerValue (Some 2)))))) _).
              mysplit.
              * apply type_expression_Add.
                { mysplit.
                  - apply type_expression_Ident.
                    reflexivity.
                  - apply type_expression_Ident.
                    reflexivity. }
              * apply type_EmptyBody. }
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