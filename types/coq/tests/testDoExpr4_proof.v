Require Import TypeSystem.
Require Import TypingTactics.
Require Import tests.testDoExpr4.

Import List.
Import AST.
Import ListNotations.
Import Utils.
Import String.
Import Interpretation.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Theorem well_typed: SoSADL ast well typed.
Proof.
  apply type_SosADL.
  apply type_Library.
  apply (type_EntityBlock_system _ _ "test" _ _ _). mysplit.
  - apply type_SystemDecl. mysplit.
    + apply Forall_nil.
    + apply type_SystemDecl_datatype_Some. mysplit.
      * apply type_DataTypeDecl_Some.
        { mysplit.
          - apply type_TupleType.
            mysplit.
            + decide_nodup (Some_dec _ string_dec).
            + apply Forall_cons.
              * do_exists.
                { mysplit.
                  - reflexivity.
                  - apply type_RangeType_trivial.
                    decide_in_Z. }
              * { apply Forall_cons.
                  - do_exists.
                    mysplit.
                    + reflexivity.
                    + apply type_RangeType_trivial.
                      decide_in_Z.
                  - apply Forall_nil. }
          - decide_nodup (Some_dec _ string_dec).
          - apply type_datatypeDecl_f.
            mysplit.
            + apply_type_functiondecl (TupleType
                                         [FieldDecl (Some "z")
                                                    (Some (RangeType (Some (BinaryExpression (Some (IntegerValue (Some 1))) (Some "+") (Some (IntegerValue (Some 0)))))
                                                                     (Some (BinaryExpression (Some (IntegerValue (Some 1))) (Some "+") (Some (IntegerValue (Some 10)))))));
                                           FieldDecl (Some "t")
                                                    (Some (RangeType (Some (BinaryExpression (Some (IntegerValue (Some 2))) (Some "+") (Some (IntegerValue (Some 0)))))
                                                                     (Some (BinaryExpression (Some (IntegerValue (Some 2))) (Some "+") (Some (IntegerValue (Some 10)))))))]).
              mysplit.
              * { apply Forall_cons.
                  - do_exists. mysplit.
                    + reflexivity.
                    + apply type_RangeType_trivial.
                      decide_in_Z.
                  - apply Forall_nil. }
              * apply type_expression_where_empty.
                apply type_expression_Tuple.
                { mysplit.
                  - decide_nodup (Some_dec _ string_dec).
                  - apply Forall2_cons.
                    + reflexivity.
                    + apply Forall2_cons.
                      * reflexivity.
                      * apply Forall2_nil.
                  - apply Forall2_cons.
                    + do_exists.
                      { mysplit.
                        - reflexivity.
                        - do_exists. mysplit.
                          + reflexivity.
                          + apply type_expression_Add.
                            mysplit.
                            * apply (type_expression_Field _ _ [FieldDecl (Some "z") (Some (RangeType (Some (IntegerValue (Some 1))) (Some (IntegerValue (Some 1)))))] _ _).
                              { mysplit.
                                - apply (type_expression_Ident _ _ (NamedType (Some "type1")) _).
                                  mysplit.
                                  + reflexivity.
                                  + apply_subtype. mysplit.
                                    * reflexivity.
                                    * apply subtype_tuple.
                                      { apply Forall_cons.
                                        - do_exists. mysplit.
                                          + reflexivity.
                                          + do_exists. mysplit.
                                            * reflexivity.
                                            * exists (RangeType (Some (IntegerValue (Some 1)))
                                                           (Some (IntegerValue (Some 1)))).
                                              { mysplit.
                                                - apply First_Field.
                                                - apply subtype_refl. }
                                        - apply Forall_nil. }
                                - apply First_Field. }
                            * apply_type_expression_ident_trivial.
                              { mysplit.
                                - reflexivity.
                                - apply subtype_refl. } }
                    + apply Forall2_cons.
                      * do_exists.
                        { mysplit.
                          - reflexivity.
                          - do_exists.
                            mysplit.
                            + reflexivity.
                            + apply type_expression_Add.
                              mysplit.
                              * apply (type_expression_Field _ _ [FieldDecl (Some "t") (Some (RangeType (Some (IntegerValue (Some 2))) (Some (IntegerValue (Some 2)))))] _ _).
                                { mysplit.
                                  - apply (type_expression_Ident _ _ (NamedType (Some "type1")) _).
                                    mysplit.
                                    + reflexivity.
                                    + apply_subtype. mysplit.
                                      * reflexivity.
                                      * apply subtype_tuple.
                                        { apply Forall_cons.
                                          - do_exists. mysplit.
                                            + reflexivity.
                                            + do_exists. mysplit.
                                              * reflexivity.
                                              * exists (RangeType (Some (IntegerValue (Some 2)))
                                                             (Some (IntegerValue (Some 2)))).
                                                { mysplit.
                                                  - apply Next_Field.
                                                    apply First_Field.
                                                  - apply subtype_refl. }
                                          - apply Forall_nil. }
                                  - apply First_Field. }
                              * apply_type_expression_ident_trivial.
                                { mysplit.
                                  - reflexivity.
                                  - apply subtype_refl. } }
                      * apply Forall2_nil. }
              * reflexivity.
              * apply subtype_tuple.
                { mysplit.
                  - apply Forall_cons.
                    + do_exists. mysplit.
                      * reflexivity.
                      * { do_exists. mysplit.
                          - reflexivity.
                          - exists (RangeType
                                 (Some
                                    (BinaryExpression (Some (IntegerValue (Some 1)))
                                                      (Some "+") (Some (IntegerValue (Some 0)))))
                                 (Some
                                    (BinaryExpression (Some (IntegerValue (Some 1)))
                                                      (Some "+") (Some (IntegerValue (Some 10)))))).
                            mysplit.
                            + apply First_Field.
                            + apply subtype_range. mysplit.
                              * decide_in_Z.
                              * decide_in_Z. }
                    + apply Forall_cons.
                      * { do_exists. mysplit.
                          - reflexivity.
                          - do_exists. mysplit.
                            + reflexivity.
                            + exists (RangeType
                                   (Some
                                      (BinaryExpression (Some (IntegerValue (Some 2))) 
                                                        (Some "+") (Some (IntegerValue (Some 0)))))
                                   (Some
                                      (BinaryExpression (Some (IntegerValue (Some 2))) 
                                                        (Some "+") (Some (IntegerValue (Some 10)))))).
                              mysplit.
                              * apply Next_Field.
                                apply First_Field.
                              * { apply subtype_range. mysplit.
                                  - decide_in_Z.
                                  - decide_in_Z. } }
                      * apply Forall_nil. }
            + apply type_datatypeDecl_empty. }             
      * { apply (type_SystemDecl_gate _ _ _ "gate1" _ _ _). mysplit.
          - apply type_GateDecl. mysplit.
            + admit. (* TODO protocol *)
            + decide_nodup (Some_dec _ string_dec).
            + apply Forall_cons.
              * apply type_Connection.
                apply_type_named_type.
                reflexivity.
              * apply Forall_nil.
          - reflexivity.
          - apply type_SystemDecl_None.
            apply type_BehaviorDecl.
            apply (type_Valuing_Some _ _ _ _ (TupleType [FieldDecl (Some "z") (Some (RangeType (Some (IntegerValue (Some 1))) (Some (IntegerValue (Some 1)))));
                                                          FieldDecl (Some "t") (Some (RangeType (Some (IntegerValue (Some 2))) (Some (IntegerValue (Some 2)))))]) _).
            mysplit.
            + apply type_expression_Tuple. mysplit.
              * decide_nodup (Some_dec _ string_dec).
              * { apply Forall2_cons.
                  - reflexivity.
                  - apply Forall2_cons.
                    + reflexivity.
                    + apply Forall2_nil. }
              * { apply Forall2_cons.
                  - do_exists. mysplit.
                    + reflexivity.
                    + do_exists. mysplit.
                      * reflexivity.
                      * apply type_expression_IntegerValue.
                  - apply Forall2_cons.
                    + do_exists. mysplit.
                      * reflexivity.
                      * do_exists.
                        { mysplit.
                          - reflexivity.
                          - apply type_expression_IntegerValue. }
                    + apply Forall2_nil. }
            + apply_subtype. mysplit.
              * reflexivity.
              * apply subtype_refl.
            + apply (type_DoExpr _ _ (RangeType (Some (IntegerValue (Some 1)))
                                                (Some (IntegerValue (Some 11)))) _).
              mysplit.
              * apply (type_expression_Field _ _ [FieldDecl (Some "z") (Some (RangeType (Some (IntegerValue (Some 1)))
                                                                                        (Some (IntegerValue (Some 11)))));
                                                   FieldDecl (Some "t") (Some (RangeType (Some (IntegerValue (Some 2)))
                                                                                       (Some (IntegerValue (Some 12)))))] _ _).
                { mysplit.
                  - apply_type_expression_methodcall "type1".
                    mysplit.
                    + apply_type_expression_ident_trivial.
                      mysplit.
                      * reflexivity.
                      * apply subtype_refl.
                    + reflexivity.
                    + apply Exists_cons_hd. mysplit.
                      * reflexivity.
                      * reflexivity.
                      * reflexivity.
                    + apply Forall2_cons.
                      * do_exists.
                        { mysplit.
                          - reflexivity.
                          - exists (RangeType (Some (IntegerValue (Some 5))) (Some (IntegerValue (Some 5)))).
                            mysplit.
                            + apply type_expression_IntegerValue.
                            + apply subtype_range. mysplit.
                              * decide_in_Z.
                              * decide_in_Z. }
                      * apply Forall2_nil.
                  - apply First_Field. }
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