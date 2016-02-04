Require Import SosADL.TypeSystem.

Import List.
Import AST.
Import ListNotations.
Import Utils.
Import String.
Import Interpretation.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(** printing Delta $\Delta$ #&Delta;# *)
(** printing Phi $\Phi$ #&Phi;# *)
(** printing Gamma $\Gamma$ #&Gamma;# *)
(** printing tau $\tau$ #&tau;# *)
(** printing Pi $\Pi$ #&Pi;# *)
(** printing empty $\emptyset$ #&empty;# *)

(** The following tactics help write typing proofs by-hand, especially
in the cases when some information need be gather from the typing
environment.  *)

Ltac apply_type_ReceiveStatement :=
  let t G C X L Gamma :=
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
      end in
  match goal with
      [ |- body (Behavior_statements
                  (SosADL.Behavior
                     ((SosADL.Action
                         (Some (SosADL.ComplexName [?G; ?C]))
                         (Some (SosADL.ReceiveAction (Some ?X)))) :: ?L)))
               well typed in ?Gamma ]
      => t G C X L Gamma
    | [ |- body ((SosADL.Action
                   (Some (SosADL.ComplexName [?G; ?C]))
                   (Some (SosADL.ReceiveAction (Some ?X)))) :: ?L)
               well typed in ?Gamma ]
      => t G C X L Gamma
  end.

Ltac apply_type_SendStatement tau  :=
  let t G C V L Gamma :=
      let gd := (eval compute in (Environment.ListBasedEnv.get Gamma G)) in
      match constr:gd with
        | Some (EGateOrDuty ?E) =>
          let typ := (eval compute in (Environment.ListBasedEnv.get E C)) in
          match constr:typ with
            | Some (GDConnection SosADL.ModeTypeInout ?T) =>
              apply (type_SendStatement_InOut Gamma G E C T V tau L)
            | Some (GDConnection SosADL.ModeTypeOut ?T) =>
              apply (type_SendStatement_Out Gamma G E C T V tau L)
            | _ => fail
          end
        | _ => fail
      end in
  match goal with
      [ |- body (Behavior_statements
                  (SosADL.Behavior
                     ((SosADL.Action
                         (Some (SosADL.ComplexName [?G; ?C]))
                         (Some (SosADL.SendAction (Some ?V)))) :: ?L)))
               well typed in ?Gamma ]
      => t G C V L Gamma
    | [ |- body ((SosADL.Action
                   (Some (SosADL.ComplexName [?G; ?C]))
                   (Some (SosADL.SendAction (Some ?V)))) :: ?L)
        well typed in ?Gamma ]
      => t G C V L Gamma      
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
          apply (subtype_left Gamma N R L F)
      end
  end.
  
Ltac do_exists :=
  let d v :=
      match (eval vm_compute in v) with
        | Some ?v' => exists v'
      end in
  match goal with
      [ |- exists x, ?v = Some x /\ _ ] => d v
    | [ |- exists x, Some x = ?v /\ _ ] => d v
  end.

(*
Ltac apply_type_functiondecl tau :=
  let t DN DTN N P T V E Gamma :=
      let et := (eval compute in (Environment.ListBasedEnv.get Gamma DTN)) in
      match constr:et with
        | Some (EType (DataTypeDecl (Some ?EDTN) (Some ?EDTT) ?EDTF)) =>
          apply (type_FunctionDecl Gamma N DN DTN P T V E tau EDTN EDTT EDTF) 
      end in
  match goal with
    | [ |- function (FunctionDecl (Some ?DN) (Some (?DTN)) (Some ?N) ?P (Some ?T) ?V (Some ?E)) well typed in ?Gamma ]
      =>
      t DN DTN N P T V E Gamma
  end.
*)

Ltac apply_type_expression_ident_trivial :=
  match goal with
      [ |- expression (IdentExpression (Some ?N)) has type ?T in ?Gamma ]
      =>
      apply (type_expression_Ident Gamma N T T)
  end.

Ltac apply_type_named_type :=
  match goal with
      [ |- type (NamedType (Some ?N)) well typed in ?Gamma ]
      =>
      match (eval vm_compute in (Environment.ListBasedEnv.get Gamma N)) with
        | Some (EType ?E)
          =>
          apply (type_NamedType _ _ E)
      end
  end.

(*
Fixpoint find_function (l: list t_FunctionDecl) (n: string) {struct l}: option t_FunctionDecl :=
  match l with
    | [] => None
    | hd :: tl =>
      match hd with
        | FunctionDecl _ _ (Some f) p _ _ _ =>
          if string_dec n f then
            Some hd
          else
            find_function tl n
        | _ => find_function tl n
      end
  end.
*)

(*
Ltac apply_type_expression_methodcall tau :=
  match goal with
      [ |- expression (MethodCall (Some ?T) (Some ?N) ?P) has type ?R in ?Gamma ]
      =>
      match (eval vm_compute in (Environment.ListBasedEnv.get Gamma tau)) with
        | Some (EType ?D)
          =>
          match constr:D with
            | DataTypeDecl _ _ ?F
              =>
              match (eval vm_compute in (find_function F N)) with
                | Some (FunctionDecl _ _ _ ?FP _ _ _)
                  =>
                  apply (type_expression_MethodCall Gamma T tau D N FP P R)
              end
          end
      end
  end.



*)