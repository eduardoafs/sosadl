Require Import TypeSystem.
Require Import tests.testDone.

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
  (* repeat (try constructor; try split). *)
  apply type_SosADL.
  apply type_Library.
  apply type_EntityBlock_system with "test"; split.
  - apply type_SystemDecl; split.
    + apply Forall_nil.
    + apply type_SystemDecl_datatype_None with BooleanType; repeat split.
      * apply type_DataTypeDecl_None.
      * { apply type_SystemDecl_gate with "gate1"; repeat split.
          - admit. (* TODO protocol *)
          - simpl. decide_nodup (Some_dec _ string_dec).
          - apply Forall_cons.
            + apply type_Connection.
              apply type_NamedType with (DataTypeDecl (Some "type1") (Some BooleanType) []).
              vm_compute. reflexivity.
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