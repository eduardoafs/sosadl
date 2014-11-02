Require Import TypeSystem.
Require Import testDone.

Import List.
Import AbstractSoSADL.AST.

Theorem well_typed: SoSADL ast well typed.
Proof.
  unfold ast.
  (* repeat (try constructor; try split). *)
  apply type_SosADL.
  apply type_Library.
  apply type_EntityBlock_system; split.
  - apply type_SystemDecl; split.
    + apply Forall_nil.
    + apply type_SystemDecl_datatype; split.
      * apply type_DataTypeDecl_None.
      * apply type_SystemDecl_None.
        {
          apply type_BehaviorDecl; split.
          - apply Forall_nil.
          - apply type_Done.
        }
  - apply type_EntityBlock.
Qed.

(*
Local Variables:
mode: coq
coding: utf-8
coq-load-path: ("..")
End:
 *)