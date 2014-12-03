Require Import TypeSystem.
Require Import testDone.

Import List.
Import AST.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Theorem well_typed: SoSADL ast well typed.
Proof.
  unfold ast.
  (* repeat (try constructor; try split). *)
  apply type_SosADL.
  apply type_Library.
  apply type_EntityBlock_system with "test"; split.
  - apply type_SystemDecl; split.
    + apply Forall_nil.
    + apply type_SystemDecl_datatype with "type1"; repeat split.
      * apply type_DataTypeDecl_None.
      * { apply type_SystemDecl_gate with "gate1"; repeat split.
          - admit.
          - simpl. apply NoDup_cons.
            + auto.
            + apply NoDup_nil.
          - apply Forall_cons.
            + apply type_Connection.
              * { apply type_NamedType with (DataTypeDecl (Some "type1") None []).
                  - admit. }
            + apply Forall_nil.
          - apply type_SystemDecl_None.
            + apply type_BehaviorDecl.
              * apply type_Done. }
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