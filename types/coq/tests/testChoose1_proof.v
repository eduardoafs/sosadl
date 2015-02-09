Require Import TypeSystem.
Require Import testChoose1.

Import List.
Import AST.
Import ListNotations.
Import Utils.
Import String.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Variable type1: t_DataType.

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
          - admit. (* TODO protocol *)
          - reflexivity.
          - apply type_SystemDecl_None.
            apply type_BehaviorDecl.
            apply type_Choose.
            apply Forall_cons.
            + apply type_Done.
            + apply Forall_cons.
              * apply type_Done.
              * apply Forall_nil. }
  - reflexivity.
  - apply type_EntityBlock.
Qed.

Axiom protocol_admitted: forall Gamma p, protocol p well typed in Gamma.

Theorem well_typed_2: SoSADL ast well typed.
Proof.
  refine
    (type_SosADL
       _ _ (type_Library
              _ _ (type_EntityBlock_system
                     _ _ "test" _ _ _
                     (conj
                        (type_SystemDecl
                           _ _ _ _ _ _ _
                           (conj
                              (Forall_nil _)
                              (type_SystemDecl_datatype_None
                                 _ _ _ type1 _ _ _ _ _
                                 (conj
                                    (type_DataTypeDecl_None _ _)
                                    (type_SystemDecl_gate
                                       _ _ _ "gate1" _ _ _
                                       (conj
                                          (type_GateDecl
                                             _ _ _ _
                                             (conj
                                                (protocol_admitted _ _)
                                                (conj
                                                   _ (* nodup *)
                                                   (Forall_cons
                                                      _
                                                      (type_Connection
                                                         _ _ _ _ _
                                                         (type_NamedType
                                                            _ _ _
                                                            _ (* reflexivity *)))
                                                      (Forall_nil _)))))
                                          (conj
                                             eq_refl
                                             (type_SystemDecl_None
                                                _ _ _
                                                (type_BehaviorDecl
                                                   _ _ _
                                                   (type_Choose
                                                      _ _
                                                      (Forall_cons
                                                         _
                                                         _ (* type_Done *)
                                                         (Forall_cons
                                                            _
                                                            _ (* type_Done *)
                                                            (Forall_nil _)))))))))))))
                        (conj
                           eq_refl
                           (type_EntityBlock _)))))).
decide_nodup (Some_dec _ (string_dec)).
reflexivity.
apply type_Done.
apply type_Done.
Defined.

(*
Local Variables:
mode: coq
coding: utf-8
coq-load-path: ("..")
End:
 *)