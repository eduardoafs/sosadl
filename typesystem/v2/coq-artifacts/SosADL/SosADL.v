Require Import String.
Require Import ZArith.

Set Parsing Explicit.

Inductive sosADL_UnobservableBehavior: Type :=
| sosADL_UnobservableBehavior_sosADL_UnobservableBehavior: sosADL_UnobservableBehavior
.

Inductive sosADL_ReceiveAnyProtocolAction: Type :=
| sosADL_ReceiveAnyProtocolAction_sosADL_ReceiveAnyProtocolAction: sosADL_ReceiveAnyProtocolAction
.

Inductive sosADL_Quantifier: Type :=
| sosADL_Quantifier_QuantifierExists: sosADL_Quantifier
| sosADL_Quantifier_QuantifierForall: sosADL_Quantifier
.

Inductive sosADL_Multiplicity: Type :=
| sosADL_Multiplicity_MultiplicityAll: sosADL_Multiplicity
| sosADL_Multiplicity_MultiplicityAny: sosADL_Multiplicity
| sosADL_Multiplicity_MultiplicityLone: sosADL_Multiplicity
| sosADL_Multiplicity_MultiplicityNone: sosADL_Multiplicity
| sosADL_Multiplicity_MultiplicityOne: sosADL_Multiplicity
| sosADL_Multiplicity_MultiplicitySome: sosADL_Multiplicity
.

Inductive sosADL_ModeType: Type :=
| sosADL_ModeType_ModeTypeIn: sosADL_ModeType
| sosADL_ModeType_ModeTypeInout: sosADL_ModeType
| sosADL_ModeType_ModeTypeOut: sosADL_ModeType
.

Inductive sosADL_IntegerType: Type :=
| sosADL_IntegerType_sosADL_IntegerType: sosADL_IntegerType
.

Inductive sosADL_DoneProtocol: Type :=
| sosADL_DoneProtocol_sosADL_DoneProtocol: sosADL_DoneProtocol
.

Inductive sosADL_DoneBehavior: Type :=
| sosADL_DoneBehavior_sosADL_DoneBehavior: sosADL_DoneBehavior
.

Inductive sosADL_BooleanType: Type :=
| sosADL_BooleanType_sosADL_BooleanType: sosADL_BooleanType
.

Inductive sosADL_AnyAction: Type :=
| sosADL_AnyAction_sosADL_AnyAction: sosADL_AnyAction
.

Inductive sosADL_Any: Type :=
| sosADL_Any_sosADL_Any: sosADL_Any
.

Definition ecore_ETreeIterator: (Type -> Type) := (fun (_: Type) => False).

Definition ecore_EString: Type := string.

Definition ecore_EResource: Type := False.

Definition ecore_EJavaObject: Type := False.

Definition ecore_EJavaClass: (Type -> Type) := (fun (_: Type) => False).

Definition ecore_EInvocationTargetException: Type := False.

Definition ecore_EInt: Type := Z.

Definition ecore_EEList: (Type -> Type) := list.

Definition ecore_EBoolean: Type := bool.

Definition _URI: (Type -> Type) := (fun (_: Type) => nat).

Definition _Set: (Type -> Type) := (fun (_: Type) => False).

Definition _Option: (Type -> Type) := option.

Inductive sosADL_UntellAssertion: Type :=
| sosADL_UntellAssertion_sosADL_UntellAssertion: (forall (name: (_Option ecore_EString)), sosADL_UntellAssertion)
.

Inductive sosADL_ReceiveProtocolAction: Type :=
| sosADL_ReceiveProtocolAction_sosADL_ReceiveProtocolAction: (forall (variable: (_Option ecore_EString)), sosADL_ReceiveProtocolAction)
.

Inductive sosADL_ReceiveAction: Type :=
| sosADL_ReceiveAction_sosADL_ReceiveAction: (forall (variable: (_Option ecore_EString)), sosADL_ReceiveAction)
.

Inductive sosADL_NamedType: Type :=
| sosADL_NamedType_sosADL_NamedType: (forall (name: (_Option ecore_EString)), sosADL_NamedType)
.

Inductive sosADL_IntegerValue: Type :=
| sosADL_IntegerValue_sosADL_IntegerValue: (forall (absInt: (_Option ecore_EInt)), sosADL_IntegerValue)
.

Inductive sosADL_Import: Type :=
| sosADL_Import_sosADL_Import: (forall (importedLibrary: (_Option ecore_EString)), sosADL_Import)
.

Inductive sosADL_IdentExpression: Type :=
| sosADL_IdentExpression_sosADL_IdentExpression: (forall (ident: (_Option ecore_EString)), sosADL_IdentExpression)
.

Inductive sosADL_ElementInConstituent: Type :=
| sosADL_ElementInConstituent_sosADL_ElementInConstituent: (forall (constituent: (_Option ecore_EString)), (forall (variable: (_Option ecore_EString)), sosADL_ElementInConstituent))
.

Inductive ecore_EStringToStringMapEntry: Type :=
| ecore_EStringToStringMapEntry_ecore_EStringToStringMapEntry: (forall (key: (_Option ecore_EString)), (forall (value: (_Option ecore_EString)), ecore_EStringToStringMapEntry))
.

Definition _List: (Type -> Type) := list.

Inductive sosADL_ComplexName: Type :=
| sosADL_ComplexName_sosADL_ComplexName: (forall (name: (_List ecore_EString)), sosADL_ComplexName)
.

Inductive sosADL_Unify: Type :=
| sosADL_Unify_sosADL_Unify: (forall (connLeft: (_Option sosADL_ComplexName)), (forall (connRight: (_Option sosADL_ComplexName)), (forall (multLeft: (_Option sosADL_Multiplicity)), (forall (multRight: (_Option sosADL_Multiplicity)), sosADL_Unify))))
.

Inductive sosADL_Relay: Type :=
| sosADL_Relay_sosADL_Relay: (forall (connLeft: (_Option sosADL_ComplexName)), (forall (connRight: (_Option sosADL_ComplexName)), sosADL_Relay))
.

Inductive sosADL_Expression: Type :=
| sosADL_Expression_sosADL_Any: sosADL_Expression
| sosADL_Expression_sosADL_BinaryExpression: (forall (left: (_Option sosADL_Expression)), (forall (op: (_Option ecore_EString)), (forall (right: (_Option sosADL_Expression)), sosADL_Expression)))
| sosADL_Expression_sosADL_CallExpression: (forall (function: (_Option ecore_EString)), (forall (parameters: (_List sosADL_Expression)), sosADL_Expression))
| sosADL_Expression_sosADL_Expression: sosADL_Expression
| sosADL_Expression_sosADL_Field: (forall (field: (_Option ecore_EString)), (forall (object: (_Option sosADL_Expression)), sosADL_Expression))
| sosADL_Expression_sosADL_IdentExpression: (forall (ident: (_Option ecore_EString)), sosADL_Expression)
| sosADL_Expression_sosADL_IntegerValue: (forall (absInt: (_Option ecore_EInt)), sosADL_Expression)
| sosADL_Expression_sosADL_Map: (forall (expression: (_Option sosADL_Expression)), (forall (object: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), sosADL_Expression)))
| sosADL_Expression_sosADL_MethodCall: (forall (method: (_Option ecore_EString)), (forall (object: (_Option sosADL_Expression)), (forall (parameters: (_List sosADL_Expression)), sosADL_Expression)))
| sosADL_Expression_sosADL_Quantify: (forall (bindings: (_Option sosADL_Expression)), (forall (elements: (_List sosADL_ElementInConstituent)), (forall (quantifier: (_Option sosADL_Quantifier)), sosADL_Expression)))
| sosADL_Expression_sosADL_Relay: (forall (connLeft: (_Option sosADL_ComplexName)), (forall (connRight: (_Option sosADL_ComplexName)), sosADL_Expression))
| sosADL_Expression_sosADL_Select: (forall (condition: (_Option sosADL_Expression)), (forall (object: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), sosADL_Expression)))
| sosADL_Expression_sosADL_Sequence: (forall (elements: (_List sosADL_Expression)), sosADL_Expression)
| sosADL_Expression_sosADL_Tuple: (forall (elements: (_List sosADL_TupleElement)), sosADL_Expression)
| sosADL_Expression_sosADL_UnaryExpression: (forall (op: (_Option ecore_EString)), (forall (right: (_Option sosADL_Expression)), sosADL_Expression))
| sosADL_Expression_sosADL_Unify: (forall (connLeft: (_Option sosADL_ComplexName)), (forall (connRight: (_Option sosADL_ComplexName)), (forall (multLeft: (_Option sosADL_Multiplicity)), (forall (multRight: (_Option sosADL_Multiplicity)), sosADL_Expression))))
 with sosADL_TupleElement: Type :=
| sosADL_TupleElement_sosADL_TupleElement: (forall (label: (_Option ecore_EString)), (forall (value: (_Option sosADL_Expression)), sosADL_TupleElement))
.

Inductive sosADL_UnaryExpression: Type :=
| sosADL_UnaryExpression_sosADL_UnaryExpression: (forall (op: (_Option ecore_EString)), (forall (right: (_Option sosADL_Expression)), sosADL_UnaryExpression))
.

Inductive sosADL_Tuple: Type :=
| sosADL_Tuple_sosADL_Tuple: (forall (elements: (_List sosADL_TupleElement)), sosADL_Tuple)
.

Inductive sosADL_TellAssertion: Type :=
| sosADL_TellAssertion_sosADL_TellAssertion: (forall (expression: (_Option sosADL_Expression)), (forall (name: (_Option ecore_EString)), sosADL_TellAssertion))
.

Inductive sosADL_Sequence: Type :=
| sosADL_Sequence_sosADL_Sequence: (forall (elements: (_List sosADL_Expression)), sosADL_Sequence)
.

Inductive sosADL_SendProtocolAction: Type :=
| sosADL_SendProtocolAction_sosADL_SendProtocolAction: (forall (expression: (_Option sosADL_Expression)), sosADL_SendProtocolAction)
.

Inductive sosADL_SendAction: Type :=
| sosADL_SendAction_sosADL_SendAction: (forall (expression: (_Option sosADL_Expression)), sosADL_SendAction)
.

Inductive sosADL_Select: Type :=
| sosADL_Select_sosADL_Select: (forall (condition: (_Option sosADL_Expression)), (forall (object: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), sosADL_Select)))
.

Inductive sosADL_RecursiveCall: Type :=
| sosADL_RecursiveCall_sosADL_RecursiveCall: (forall (parameters: (_List sosADL_Expression)), sosADL_RecursiveCall)
.

Inductive sosADL_RangeType: Type :=
| sosADL_RangeType_sosADL_RangeType: (forall (vmax: (_Option sosADL_Expression)), (forall (vmin: (_Option sosADL_Expression)), sosADL_RangeType))
.

Inductive sosADL_Quantify: Type :=
| sosADL_Quantify_sosADL_Quantify: (forall (bindings: (_Option sosADL_Expression)), (forall (elements: (_List sosADL_ElementInConstituent)), (forall (quantifier: (_Option sosADL_Quantifier)), sosADL_Quantify)))
.

Inductive sosADL_ProtocolActionSuite: Type :=
| sosADL_ProtocolActionSuite_sosADL_ProtocolActionSuite: sosADL_ProtocolActionSuite
| sosADL_ProtocolActionSuite_sosADL_ReceiveAnyProtocolAction: sosADL_ProtocolActionSuite
| sosADL_ProtocolActionSuite_sosADL_ReceiveProtocolAction: (forall (variable: (_Option ecore_EString)), sosADL_ProtocolActionSuite)
| sosADL_ProtocolActionSuite_sosADL_SendProtocolAction: (forall (expression: (_Option sosADL_Expression)), sosADL_ProtocolActionSuite)
.

Inductive sosADL_ProtocolAction: Type :=
| sosADL_ProtocolAction_sosADL_ProtocolAction: (forall (complexName: (_Option sosADL_ComplexName)), (forall (suite: (_Option sosADL_ProtocolActionSuite)), sosADL_ProtocolAction))
.

Inductive sosADL_MethodCall: Type :=
| sosADL_MethodCall_sosADL_MethodCall: (forall (method: (_Option ecore_EString)), (forall (object: (_Option sosADL_Expression)), (forall (parameters: (_List sosADL_Expression)), sosADL_MethodCall)))
.

Inductive sosADL_Map: Type :=
| sosADL_Map_sosADL_Map: (forall (expression: (_Option sosADL_Expression)), (forall (object: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), sosADL_Map)))
.

Inductive sosADL_Field: Type :=
| sosADL_Field_sosADL_Field: (forall (field: (_Option ecore_EString)), (forall (object: (_Option sosADL_Expression)), sosADL_Field))
.

Inductive sosADL_DoExprProtocol: Type :=
| sosADL_DoExprProtocol_sosADL_DoExprProtocol: (forall (expression: (_Option sosADL_Expression)), sosADL_DoExprProtocol)
.

Inductive sosADL_DoExprBehavior: Type :=
| sosADL_DoExprBehavior_sosADL_DoExprBehavior: (forall (expression: (_Option sosADL_Expression)), sosADL_DoExprBehavior)
.

Inductive sosADL_DataType: Type :=
| sosADL_DataType_sosADL_BooleanType: sosADL_DataType
| sosADL_DataType_sosADL_ConnectionType: (forall (mode: (_Option sosADL_ModeType)), (forall (type: (_Option sosADL_DataType)), sosADL_DataType))
| sosADL_DataType_sosADL_DataType: sosADL_DataType
| sosADL_DataType_sosADL_IntegerType: sosADL_DataType
| sosADL_DataType_sosADL_NamedType: (forall (name: (_Option ecore_EString)), sosADL_DataType)
| sosADL_DataType_sosADL_RangeType: (forall (vmax: (_Option sosADL_Expression)), (forall (vmin: (_Option sosADL_Expression)), sosADL_DataType))
| sosADL_DataType_sosADL_SequenceType: (forall (type: (_Option sosADL_DataType)), sosADL_DataType)
| sosADL_DataType_sosADL_TupleType: (forall (fields: (_List sosADL_FieldDecl)), sosADL_DataType)
 with sosADL_FieldDecl: Type :=
| sosADL_FieldDecl_sosADL_FieldDecl: (forall (name: (_Option ecore_EString)), (forall (type: (_Option sosADL_DataType)), sosADL_FieldDecl))
.

Inductive sosADL_Valuing: Type :=
| sosADL_Valuing_sosADL_Valuing: (forall (expression: (_Option sosADL_Expression)), (forall (name: (_Option ecore_EString)), (forall (type: (_Option sosADL_DataType)), sosADL_Valuing)))
.

Inductive sosADL_ValuingProtocol: Type :=
| sosADL_ValuingProtocol_sosADL_ValuingProtocol: (forall (valuing: (_Option sosADL_Valuing)), sosADL_ValuingProtocol)
.

Inductive sosADL_ValuingBehavior: Type :=
| sosADL_ValuingBehavior_sosADL_ValuingBehavior: (forall (valuing: (_Option sosADL_Valuing)), sosADL_ValuingBehavior)
.

Inductive sosADL_TupleType: Type :=
| sosADL_TupleType_sosADL_TupleType: (forall (fields: (_List sosADL_FieldDecl)), sosADL_TupleType)
.

Inductive sosADL_SequenceType: Type :=
| sosADL_SequenceType_sosADL_SequenceType: (forall (type: (_Option sosADL_DataType)), sosADL_SequenceType)
.

Inductive sosADL_FormalParameter: Type :=
| sosADL_FormalParameter_sosADL_FormalParameter: (forall (name: (_Option ecore_EString)), (forall (type: (_Option sosADL_DataType)), sosADL_FormalParameter))
.

Inductive sosADL_FunctionDecl: Type :=
| sosADL_FunctionDecl_sosADL_FunctionDecl: (forall (data: (_Option sosADL_FormalParameter)), (forall (expression: (_Option sosADL_Expression)), (forall (name: (_Option ecore_EString)), (forall (parameters: (_List sosADL_FormalParameter)), (forall (type: (_Option sosADL_DataType)), (forall (valuing: (_List sosADL_Valuing)), sosADL_FunctionDecl))))))
.

Inductive sosADL_DataTypeDecl: Type :=
| sosADL_DataTypeDecl_sosADL_DataTypeDecl: (forall (datatype: (_Option sosADL_DataType)), (forall (functions: (_List sosADL_FunctionDecl)), (forall (name: (_Option ecore_EString)), sosADL_DataTypeDecl)))
.

Inductive sosADL_ConnectionType: Type :=
| sosADL_ConnectionType_sosADL_ConnectionType: (forall (mode: (_Option sosADL_ModeType)), (forall (type: (_Option sosADL_DataType)), sosADL_ConnectionType))
.

Inductive sosADL_Connection: Type :=
| sosADL_Connection_sosADL_Connection: (forall (environment: (_Option ecore_EBoolean)), (forall (mode: (_Option sosADL_ModeType)), (forall (name: (_Option ecore_EString)), (forall (valueType: (_Option sosADL_DataType)), sosADL_Connection))))
.

Inductive sosADL_Constituent: Type :=
| sosADL_Constituent_sosADL_Constituent: (forall (name: (_Option ecore_EString)), (forall (value: (_Option sosADL_Expression)), sosADL_Constituent))
.

Inductive sosADL_BinaryExpression: Type :=
| sosADL_BinaryExpression_sosADL_BinaryExpression: (forall (left: (_Option sosADL_Expression)), (forall (op: (_Option ecore_EString)), (forall (right: (_Option sosADL_Expression)), sosADL_BinaryExpression)))
.

Inductive sosADL_Assert: Type :=
| sosADL_Assert_sosADL_AskAssertion: (forall (expression: (_Option sosADL_Expression)), (forall (name: (_Option ecore_EString)), sosADL_Assert))
| sosADL_Assert_sosADL_Assert: (forall (name: (_Option ecore_EString)), sosADL_Assert)
| sosADL_Assert_sosADL_TellAssertion: (forall (expression: (_Option sosADL_Expression)), (forall (name: (_Option ecore_EString)), sosADL_Assert))
| sosADL_Assert_sosADL_UntellAssertion: (forall (name: (_Option ecore_EString)), sosADL_Assert)
.

Inductive sosADL_Protocol: Type :=
| sosADL_Protocol_sosADL_Protocol: (forall (statements: (_List sosADL_ProtocolStatement)), sosADL_Protocol)
 with sosADL_ProtocolStatement: Type :=
| sosADL_ProtocolStatement_sosADL_AnyAction: sosADL_ProtocolStatement
| sosADL_ProtocolStatement_sosADL_AssertProtocol: (forall (assertion: (_Option sosADL_Assert)), sosADL_ProtocolStatement)
| sosADL_ProtocolStatement_sosADL_ChooseProtocol: (forall (branches: (_List sosADL_Protocol)), sosADL_ProtocolStatement)
| sosADL_ProtocolStatement_sosADL_DoExprProtocol: (forall (expression: (_Option sosADL_Expression)), sosADL_ProtocolStatement)
| sosADL_ProtocolStatement_sosADL_DoneProtocol: sosADL_ProtocolStatement
| sosADL_ProtocolStatement_sosADL_ForEachProtocol: (forall (repeated: (_Option sosADL_Protocol)), (forall (setOfValues: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), sosADL_ProtocolStatement)))
| sosADL_ProtocolStatement_sosADL_IfThenElseProtocol: (forall (condition: (_Option sosADL_Expression)), (forall (ifFalse: (_Option sosADL_Protocol)), (forall (ifTrue: (_Option sosADL_Protocol)), sosADL_ProtocolStatement)))
| sosADL_ProtocolStatement_sosADL_ProtocolAction: (forall (complexName: (_Option sosADL_ComplexName)), (forall (suite: (_Option sosADL_ProtocolActionSuite)), sosADL_ProtocolStatement))
| sosADL_ProtocolStatement_sosADL_ProtocolStatement: sosADL_ProtocolStatement
| sosADL_ProtocolStatement_sosADL_RepeatProtocol: (forall (repeated: (_Option sosADL_Protocol)), sosADL_ProtocolStatement)
| sosADL_ProtocolStatement_sosADL_ValuingProtocol: (forall (valuing: (_Option sosADL_Valuing)), sosADL_ProtocolStatement)
.

Inductive sosADL_RepeatProtocol: Type :=
| sosADL_RepeatProtocol_sosADL_RepeatProtocol: (forall (repeated: (_Option sosADL_Protocol)), sosADL_RepeatProtocol)
.

Inductive sosADL_ProtocolDecl: Type :=
| sosADL_ProtocolDecl_sosADL_ProtocolDecl: (forall (body: (_Option sosADL_Protocol)), (forall (name: (_Option ecore_EString)), sosADL_ProtocolDecl))
.

Inductive sosADL_GateDecl: Type :=
| sosADL_GateDecl_sosADL_GateDecl: (forall (connections: (_List sosADL_Connection)), (forall (name: (_Option ecore_EString)), (forall (protocols: (_List sosADL_ProtocolDecl)), sosADL_GateDecl)))
.

Inductive sosADL_IfThenElseProtocol: Type :=
| sosADL_IfThenElseProtocol_sosADL_IfThenElseProtocol: (forall (condition: (_Option sosADL_Expression)), (forall (ifFalse: (_Option sosADL_Protocol)), (forall (ifTrue: (_Option sosADL_Protocol)), sosADL_IfThenElseProtocol)))
.

Inductive sosADL_ForEachProtocol: Type :=
| sosADL_ForEachProtocol_sosADL_ForEachProtocol: (forall (repeated: (_Option sosADL_Protocol)), (forall (setOfValues: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), sosADL_ForEachProtocol)))
.

Inductive sosADL_AssertionDecl: Type :=
| sosADL_AssertionDecl_sosADL_AssertionDecl: (forall (body: (_Option sosADL_Protocol)), (forall (name: (_Option ecore_EString)), sosADL_AssertionDecl))
.

Inductive sosADL_DutyDecl: Type :=
| sosADL_DutyDecl_sosADL_DutyDecl: (forall (assertions: (_List sosADL_AssertionDecl)), (forall (connections: (_List sosADL_Connection)), (forall (name: (_Option ecore_EString)), (forall (protocols: (_List sosADL_ProtocolDecl)), sosADL_DutyDecl))))
.

Inductive sosADL_AssertProtocol: Type :=
| sosADL_AssertProtocol_sosADL_AssertProtocol: (forall (assertion: (_Option sosADL_Assert)), sosADL_AssertProtocol)
.

Inductive sosADL_AssertBehavior: Type :=
| sosADL_AssertBehavior_sosADL_AssertBehavior: (forall (assertion: (_Option sosADL_Assert)), sosADL_AssertBehavior)
.

Inductive sosADL_AskAssertion: Type :=
| sosADL_AskAssertion_sosADL_AskAssertion: (forall (expression: (_Option sosADL_Expression)), (forall (name: (_Option ecore_EString)), sosADL_AskAssertion))
.

Inductive sosADL_ActionSuite: Type :=
| sosADL_ActionSuite_sosADL_ActionSuite: sosADL_ActionSuite
| sosADL_ActionSuite_sosADL_ReceiveAction: (forall (variable: (_Option ecore_EString)), sosADL_ActionSuite)
| sosADL_ActionSuite_sosADL_SendAction: (forall (expression: (_Option sosADL_Expression)), sosADL_ActionSuite)
.

Inductive sosADL_Action: Type :=
| sosADL_Action_sosADL_Action: (forall (complexName: (_Option sosADL_ComplexName)), (forall (suite: (_Option sosADL_ActionSuite)), sosADL_Action))
.

Inductive sosADL_ChooseProtocol: Type :=
| sosADL_ChooseProtocol_sosADL_ChooseProtocol: (forall (branches: (_List sosADL_Protocol)), sosADL_ChooseProtocol)
.

Inductive sosADL_CallExpression: Type :=
| sosADL_CallExpression_sosADL_CallExpression: (forall (function: (_Option ecore_EString)), (forall (parameters: (_List sosADL_Expression)), sosADL_CallExpression))
.

Inductive sosADL_Behavior: Type :=
| sosADL_Behavior_sosADL_Behavior: (forall (statements: (_List sosADL_BehaviorStatement)), sosADL_Behavior)
 with sosADL_BehaviorStatement: Type :=
| sosADL_BehaviorStatement_sosADL_Action: (forall (complexName: (_Option sosADL_ComplexName)), (forall (suite: (_Option sosADL_ActionSuite)), sosADL_BehaviorStatement))
| sosADL_BehaviorStatement_sosADL_AssertBehavior: (forall (assertion: (_Option sosADL_Assert)), sosADL_BehaviorStatement)
| sosADL_BehaviorStatement_sosADL_BehaviorStatement: sosADL_BehaviorStatement
| sosADL_BehaviorStatement_sosADL_ChooseBehavior: (forall (branches: (_List sosADL_Behavior)), sosADL_BehaviorStatement)
| sosADL_BehaviorStatement_sosADL_DoExprBehavior: (forall (expression: (_Option sosADL_Expression)), sosADL_BehaviorStatement)
| sosADL_BehaviorStatement_sosADL_DoneBehavior: sosADL_BehaviorStatement
| sosADL_BehaviorStatement_sosADL_ForEachBehavior: (forall (repeated: (_Option sosADL_Behavior)), (forall (setOfValues: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), sosADL_BehaviorStatement)))
| sosADL_BehaviorStatement_sosADL_IfThenElseBehavior: (forall (condition: (_Option sosADL_Expression)), (forall (ifFalse: (_Option sosADL_Behavior)), (forall (ifTrue: (_Option sosADL_Behavior)), sosADL_BehaviorStatement)))
| sosADL_BehaviorStatement_sosADL_RecursiveCall: (forall (parameters: (_List sosADL_Expression)), sosADL_BehaviorStatement)
| sosADL_BehaviorStatement_sosADL_RepeatBehavior: (forall (repeated: (_Option sosADL_Behavior)), sosADL_BehaviorStatement)
| sosADL_BehaviorStatement_sosADL_UnobservableBehavior: sosADL_BehaviorStatement
| sosADL_BehaviorStatement_sosADL_ValuingBehavior: (forall (valuing: (_Option sosADL_Valuing)), sosADL_BehaviorStatement)
.

Inductive sosADL_RepeatBehavior: Type :=
| sosADL_RepeatBehavior_sosADL_RepeatBehavior: (forall (repeated: (_Option sosADL_Behavior)), sosADL_RepeatBehavior)
.

Inductive sosADL_IfThenElseBehavior: Type :=
| sosADL_IfThenElseBehavior_sosADL_IfThenElseBehavior: (forall (condition: (_Option sosADL_Expression)), (forall (ifFalse: (_Option sosADL_Behavior)), (forall (ifTrue: (_Option sosADL_Behavior)), sosADL_IfThenElseBehavior)))
.

Inductive sosADL_ForEachBehavior: Type :=
| sosADL_ForEachBehavior_sosADL_ForEachBehavior: (forall (repeated: (_Option sosADL_Behavior)), (forall (setOfValues: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), sosADL_ForEachBehavior)))
.

Inductive sosADL_ChooseBehavior: Type :=
| sosADL_ChooseBehavior_sosADL_ChooseBehavior: (forall (branches: (_List sosADL_Behavior)), sosADL_ChooseBehavior)
.

Inductive sosADL_BehaviorDecl: Type :=
| sosADL_BehaviorDecl_sosADL_BehaviorDecl: (forall (body: (_Option sosADL_Behavior)), (forall (name: (_Option ecore_EString)), sosADL_BehaviorDecl))
.

Inductive sosADL_SystemDecl: Type :=
| sosADL_SystemDecl_sosADL_SystemDecl: (forall (assertions: (_List sosADL_AssertionDecl)), (forall (behavior: (_Option sosADL_BehaviorDecl)), (forall (datatypes: (_List sosADL_DataTypeDecl)), (forall (gates: (_List sosADL_GateDecl)), (forall (name: (_Option ecore_EString)), (forall (parameters: (_List sosADL_FormalParameter)), sosADL_SystemDecl))))))
.

Inductive sosADL_MediatorDecl: Type :=
| sosADL_MediatorDecl_sosADL_MediatorDecl: (forall (assertions: (_List sosADL_AssertionDecl)), (forall (assumptions: (_List sosADL_AssertionDecl)), (forall (behavior: (_Option sosADL_BehaviorDecl)), (forall (datatypes: (_List sosADL_DataTypeDecl)), (forall (duties: (_List sosADL_DutyDecl)), (forall (name: (_Option ecore_EString)), (forall (parameters: (_List sosADL_FormalParameter)), sosADL_MediatorDecl)))))))
.

Inductive sosADL_ArchBehaviorDecl: Type :=
| sosADL_ArchBehaviorDecl_sosADL_ArchBehaviorDecl: (forall (bindings: (_Option sosADL_Expression)), (forall (constituents: (_List sosADL_Constituent)), (forall (name: (_Option ecore_EString)), sosADL_ArchBehaviorDecl)))
.

Inductive sosADL_ArchitectureDecl: Type :=
| sosADL_ArchitectureDecl_sosADL_ArchitectureDecl: (forall (assertions: (_List sosADL_AssertionDecl)), (forall (behavior: (_Option sosADL_ArchBehaviorDecl)), (forall (datatypes: (_List sosADL_DataTypeDecl)), (forall (gates: (_List sosADL_GateDecl)), (forall (name: (_Option ecore_EString)), (forall (parameters: (_List sosADL_FormalParameter)), sosADL_ArchitectureDecl))))))
.

Inductive sosADL_EntityBlock: Type :=
| sosADL_EntityBlock_sosADL_EntityBlock: (forall (architectures: (_List sosADL_ArchitectureDecl)), (forall (datatypes: (_List sosADL_DataTypeDecl)), (forall (functions: (_List sosADL_FunctionDecl)), (forall (mediators: (_List sosADL_MediatorDecl)), (forall (systems: (_List sosADL_SystemDecl)), sosADL_EntityBlock)))))
.

Inductive sosADL_Unit: Type :=
| sosADL_Unit_sosADL_Library: (forall (decls: (_Option sosADL_EntityBlock)), (forall (name: (_Option ecore_EString)), sosADL_Unit))
| sosADL_Unit_sosADL_SoS: (forall (decls: (_Option sosADL_EntityBlock)), (forall (name: (_Option ecore_EString)), sosADL_Unit))
| sosADL_Unit_sosADL_Unit: (forall (decls: (_Option sosADL_EntityBlock)), (forall (name: (_Option ecore_EString)), sosADL_Unit))
.

Inductive sosADL_SosADL: Type :=
| sosADL_SosADL_sosADL_SosADL: (forall (content: (_Option sosADL_Unit)), (forall (imports: (_List sosADL_Import)), sosADL_SosADL))
.

Inductive sosADL_SoS: Type :=
| sosADL_SoS_sosADL_SoS: (forall (decls: (_Option sosADL_EntityBlock)), (forall (name: (_Option ecore_EString)), sosADL_SoS))
.

Inductive sosADL_Library: Type :=
| sosADL_Library_sosADL_Library: (forall (decls: (_Option sosADL_EntityBlock)), (forall (name: (_Option ecore_EString)), sosADL_Library))
.

Inductive ecore_EAnnotation: Type :=
| ecore_EAnnotation_ecore_EAnnotation: (forall (contents: (_List ecore_EObject)), (forall (details: (_List ecore_EStringToStringMapEntry)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (references: (_List (_URI ecore_EObject))), (forall (source: (_Option ecore_EString)), ecore_EAnnotation)))))
 with ecore_EAttribute: Type :=
| ecore_EAttribute_ecore_EAttribute: (forall (changeable: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (iD: (_Option ecore_EBoolean)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_EAttribute)))))))))))))))
 with ecore_EClass: Type :=
| ecore_EClass_ecore_EClass: (forall (abstract: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericSuperTypes: (_List ecore_EGenericType)), (forall (eOperations: (_List ecore_EOperation)), (forall (eStructuralFeatures: (_List ecore_EStructuralFeature)), (forall (eSuperTypes: (_List (_URI ecore_EClass))), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (instanceClassName: (_Option ecore_EString)), (forall (instanceTypeName: (_Option ecore_EString)), (forall (interface: (_Option ecore_EBoolean)), (forall (name: (_Option ecore_EString)), ecore_EClass)))))))))))
 with ecore_EClassifier: Type :=
| ecore_EClassifier_ecore_EClass: (forall (abstract: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericSuperTypes: (_List ecore_EGenericType)), (forall (eOperations: (_List ecore_EOperation)), (forall (eStructuralFeatures: (_List ecore_EStructuralFeature)), (forall (eSuperTypes: (_List (_URI ecore_EClass))), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (instanceClassName: (_Option ecore_EString)), (forall (instanceTypeName: (_Option ecore_EString)), (forall (interface: (_Option ecore_EBoolean)), (forall (name: (_Option ecore_EString)), ecore_EClassifier)))))))))))
| ecore_EClassifier_ecore_EDataType: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (instanceClassName: (_Option ecore_EString)), (forall (instanceTypeName: (_Option ecore_EString)), (forall (name: (_Option ecore_EString)), (forall (serializable: (_Option ecore_EBoolean)), ecore_EClassifier))))))
 with ecore_EGenericType: Type :=
| ecore_EGenericType_ecore_EGenericType: (forall (eClassifier: (_Option (_URI ecore_EClassifier))), (forall (eLowerBound: (_Option ecore_EGenericType)), (forall (eTypeArguments: (_List ecore_EGenericType)), (forall (eTypeParameter: (_Option (_URI ecore_ETypeParameter))), (forall (eUpperBound: (_Option ecore_EGenericType)), ecore_EGenericType)))))
 with ecore_EObject: Type :=
| ecore_EObject_ecore_EAnnotation: (forall (contents: (_List ecore_EObject)), (forall (details: (_List ecore_EStringToStringMapEntry)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (references: (_List (_URI ecore_EObject))), (forall (source: (_Option ecore_EString)), ecore_EObject)))))
| ecore_EObject_ecore_EAttribute: (forall (changeable: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (iD: (_Option ecore_EBoolean)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_EObject)))))))))))))))
| ecore_EObject_ecore_EClass: (forall (abstract: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericSuperTypes: (_List ecore_EGenericType)), (forall (eOperations: (_List ecore_EOperation)), (forall (eStructuralFeatures: (_List ecore_EStructuralFeature)), (forall (eSuperTypes: (_List (_URI ecore_EClass))), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (instanceClassName: (_Option ecore_EString)), (forall (instanceTypeName: (_Option ecore_EString)), (forall (interface: (_Option ecore_EBoolean)), (forall (name: (_Option ecore_EString)), ecore_EObject)))))))))))
| ecore_EObject_ecore_EDataType: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (instanceClassName: (_Option ecore_EString)), (forall (instanceTypeName: (_Option ecore_EString)), (forall (name: (_Option ecore_EString)), (forall (serializable: (_Option ecore_EBoolean)), ecore_EObject))))))
| ecore_EObject_ecore_EFactory: (forall (eAnnotations: (_List ecore_EAnnotation)), ecore_EObject)
| ecore_EObject_ecore_EGenericType: (forall (eClassifier: (_Option (_URI ecore_EClassifier))), (forall (eLowerBound: (_Option ecore_EGenericType)), (forall (eTypeArguments: (_List ecore_EGenericType)), (forall (eTypeParameter: (_Option (_URI ecore_ETypeParameter))), (forall (eUpperBound: (_Option ecore_EGenericType)), ecore_EObject)))))
| ecore_EObject_ecore_EObject: ecore_EObject
| ecore_EObject_ecore_EOperation: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eExceptions: (_List (_URI ecore_EClassifier))), (forall (eGenericExceptions: (_List ecore_EGenericType)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eParameters: (_List ecore_EParameter)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), ecore_EObject))))))))))))
| ecore_EObject_ecore_EPackage: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eClassifiers: (_List ecore_EClassifier)), (forall (eSubpackages: (_List ecore_EPackage)), (forall (name: (_Option ecore_EString)), (forall (nsPrefix: (_Option ecore_EString)), (forall (nsURI: (_Option ecore_EString)), ecore_EObject))))))
| ecore_EObject_ecore_EParameter: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), ecore_EObject))))))))
| ecore_EObject_ecore_EReference: (forall (changeable: (_Option ecore_EBoolean)), (forall (containment: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eKeys: (_List (_URI ecore_EAttribute))), (forall (eOpposite: (_Option (_URI ecore_EReference))), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (resolveProxies: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_EObject))))))))))))))))))
| ecore_EObject_ecore_EStringToStringMapEntry: (forall (key: (_Option ecore_EString)), (forall (value: (_Option ecore_EString)), ecore_EObject))
| ecore_EObject_ecore_ETypeParameter: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eBounds: (_List ecore_EGenericType)), (forall (name: (_Option ecore_EString)), ecore_EObject)))
| ecore_EObject_sosADL_Action: (forall (complexName: (_Option sosADL_ComplexName)), (forall (suite: (_Option sosADL_ActionSuite)), ecore_EObject))
| ecore_EObject_sosADL_ActionSuite: ecore_EObject
| ecore_EObject_sosADL_Any: ecore_EObject
| ecore_EObject_sosADL_AnyAction: ecore_EObject
| ecore_EObject_sosADL_ArchBehaviorDecl: (forall (bindings: (_Option sosADL_Expression)), (forall (constituents: (_List sosADL_Constituent)), (forall (name: (_Option ecore_EString)), ecore_EObject)))
| ecore_EObject_sosADL_ArchitectureDecl: (forall (assertions: (_List sosADL_AssertionDecl)), (forall (behavior: (_Option sosADL_ArchBehaviorDecl)), (forall (datatypes: (_List sosADL_DataTypeDecl)), (forall (gates: (_List sosADL_GateDecl)), (forall (name: (_Option ecore_EString)), (forall (parameters: (_List sosADL_FormalParameter)), ecore_EObject))))))
| ecore_EObject_sosADL_AskAssertion: (forall (expression: (_Option sosADL_Expression)), (forall (name: (_Option ecore_EString)), ecore_EObject))
| ecore_EObject_sosADL_Assert: (forall (name: (_Option ecore_EString)), ecore_EObject)
| ecore_EObject_sosADL_AssertBehavior: (forall (assertion: (_Option sosADL_Assert)), ecore_EObject)
| ecore_EObject_sosADL_AssertProtocol: (forall (assertion: (_Option sosADL_Assert)), ecore_EObject)
| ecore_EObject_sosADL_AssertionDecl: (forall (body: (_Option sosADL_Protocol)), (forall (name: (_Option ecore_EString)), ecore_EObject))
| ecore_EObject_sosADL_Behavior: (forall (statements: (_List sosADL_BehaviorStatement)), ecore_EObject)
| ecore_EObject_sosADL_BehaviorDecl: (forall (body: (_Option sosADL_Behavior)), (forall (name: (_Option ecore_EString)), ecore_EObject))
| ecore_EObject_sosADL_BehaviorStatement: ecore_EObject
| ecore_EObject_sosADL_BinaryExpression: (forall (left: (_Option sosADL_Expression)), (forall (op: (_Option ecore_EString)), (forall (right: (_Option sosADL_Expression)), ecore_EObject)))
| ecore_EObject_sosADL_BooleanType: ecore_EObject
| ecore_EObject_sosADL_CallExpression: (forall (function: (_Option ecore_EString)), (forall (parameters: (_List sosADL_Expression)), ecore_EObject))
| ecore_EObject_sosADL_ChooseBehavior: (forall (branches: (_List sosADL_Behavior)), ecore_EObject)
| ecore_EObject_sosADL_ChooseProtocol: (forall (branches: (_List sosADL_Protocol)), ecore_EObject)
| ecore_EObject_sosADL_ComplexName: (forall (name: (_List ecore_EString)), ecore_EObject)
| ecore_EObject_sosADL_Connection: (forall (environment: (_Option ecore_EBoolean)), (forall (mode: (_Option sosADL_ModeType)), (forall (name: (_Option ecore_EString)), (forall (valueType: (_Option sosADL_DataType)), ecore_EObject))))
| ecore_EObject_sosADL_ConnectionType: (forall (mode: (_Option sosADL_ModeType)), (forall (type: (_Option sosADL_DataType)), ecore_EObject))
| ecore_EObject_sosADL_Constituent: (forall (name: (_Option ecore_EString)), (forall (value: (_Option sosADL_Expression)), ecore_EObject))
| ecore_EObject_sosADL_DataType: ecore_EObject
| ecore_EObject_sosADL_DataTypeDecl: (forall (datatype: (_Option sosADL_DataType)), (forall (functions: (_List sosADL_FunctionDecl)), (forall (name: (_Option ecore_EString)), ecore_EObject)))
| ecore_EObject_sosADL_DoExprBehavior: (forall (expression: (_Option sosADL_Expression)), ecore_EObject)
| ecore_EObject_sosADL_DoExprProtocol: (forall (expression: (_Option sosADL_Expression)), ecore_EObject)
| ecore_EObject_sosADL_DoneBehavior: ecore_EObject
| ecore_EObject_sosADL_DoneProtocol: ecore_EObject
| ecore_EObject_sosADL_DutyDecl: (forall (assertions: (_List sosADL_AssertionDecl)), (forall (connections: (_List sosADL_Connection)), (forall (name: (_Option ecore_EString)), (forall (protocols: (_List sosADL_ProtocolDecl)), ecore_EObject))))
| ecore_EObject_sosADL_ElementInConstituent: (forall (constituent: (_Option ecore_EString)), (forall (variable: (_Option ecore_EString)), ecore_EObject))
| ecore_EObject_sosADL_EntityBlock: (forall (architectures: (_List sosADL_ArchitectureDecl)), (forall (datatypes: (_List sosADL_DataTypeDecl)), (forall (functions: (_List sosADL_FunctionDecl)), (forall (mediators: (_List sosADL_MediatorDecl)), (forall (systems: (_List sosADL_SystemDecl)), ecore_EObject)))))
| ecore_EObject_sosADL_Expression: ecore_EObject
| ecore_EObject_sosADL_Field: (forall (field: (_Option ecore_EString)), (forall (object: (_Option sosADL_Expression)), ecore_EObject))
| ecore_EObject_sosADL_FieldDecl: (forall (name: (_Option ecore_EString)), (forall (type: (_Option sosADL_DataType)), ecore_EObject))
| ecore_EObject_sosADL_ForEachBehavior: (forall (repeated: (_Option sosADL_Behavior)), (forall (setOfValues: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), ecore_EObject)))
| ecore_EObject_sosADL_ForEachProtocol: (forall (repeated: (_Option sosADL_Protocol)), (forall (setOfValues: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), ecore_EObject)))
| ecore_EObject_sosADL_FormalParameter: (forall (name: (_Option ecore_EString)), (forall (type: (_Option sosADL_DataType)), ecore_EObject))
| ecore_EObject_sosADL_FunctionDecl: (forall (data: (_Option sosADL_FormalParameter)), (forall (expression: (_Option sosADL_Expression)), (forall (name: (_Option ecore_EString)), (forall (parameters: (_List sosADL_FormalParameter)), (forall (type: (_Option sosADL_DataType)), (forall (valuing: (_List sosADL_Valuing)), ecore_EObject))))))
| ecore_EObject_sosADL_GateDecl: (forall (connections: (_List sosADL_Connection)), (forall (name: (_Option ecore_EString)), (forall (protocols: (_List sosADL_ProtocolDecl)), ecore_EObject)))
| ecore_EObject_sosADL_IdentExpression: (forall (ident: (_Option ecore_EString)), ecore_EObject)
| ecore_EObject_sosADL_IfThenElseBehavior: (forall (condition: (_Option sosADL_Expression)), (forall (ifFalse: (_Option sosADL_Behavior)), (forall (ifTrue: (_Option sosADL_Behavior)), ecore_EObject)))
| ecore_EObject_sosADL_IfThenElseProtocol: (forall (condition: (_Option sosADL_Expression)), (forall (ifFalse: (_Option sosADL_Protocol)), (forall (ifTrue: (_Option sosADL_Protocol)), ecore_EObject)))
| ecore_EObject_sosADL_Import: (forall (importedLibrary: (_Option ecore_EString)), ecore_EObject)
| ecore_EObject_sosADL_IntegerType: ecore_EObject
| ecore_EObject_sosADL_IntegerValue: (forall (absInt: (_Option ecore_EInt)), ecore_EObject)
| ecore_EObject_sosADL_Library: (forall (decls: (_Option sosADL_EntityBlock)), (forall (name: (_Option ecore_EString)), ecore_EObject))
| ecore_EObject_sosADL_Map: (forall (expression: (_Option sosADL_Expression)), (forall (object: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), ecore_EObject)))
| ecore_EObject_sosADL_MediatorDecl: (forall (assertions: (_List sosADL_AssertionDecl)), (forall (assumptions: (_List sosADL_AssertionDecl)), (forall (behavior: (_Option sosADL_BehaviorDecl)), (forall (datatypes: (_List sosADL_DataTypeDecl)), (forall (duties: (_List sosADL_DutyDecl)), (forall (name: (_Option ecore_EString)), (forall (parameters: (_List sosADL_FormalParameter)), ecore_EObject)))))))
| ecore_EObject_sosADL_MethodCall: (forall (method: (_Option ecore_EString)), (forall (object: (_Option sosADL_Expression)), (forall (parameters: (_List sosADL_Expression)), ecore_EObject)))
| ecore_EObject_sosADL_NamedType: (forall (name: (_Option ecore_EString)), ecore_EObject)
| ecore_EObject_sosADL_Protocol: (forall (statements: (_List sosADL_ProtocolStatement)), ecore_EObject)
| ecore_EObject_sosADL_ProtocolAction: (forall (complexName: (_Option sosADL_ComplexName)), (forall (suite: (_Option sosADL_ProtocolActionSuite)), ecore_EObject))
| ecore_EObject_sosADL_ProtocolActionSuite: ecore_EObject
| ecore_EObject_sosADL_ProtocolDecl: (forall (body: (_Option sosADL_Protocol)), (forall (name: (_Option ecore_EString)), ecore_EObject))
| ecore_EObject_sosADL_ProtocolStatement: ecore_EObject
| ecore_EObject_sosADL_Quantify: (forall (bindings: (_Option sosADL_Expression)), (forall (elements: (_List sosADL_ElementInConstituent)), (forall (quantifier: (_Option sosADL_Quantifier)), ecore_EObject)))
| ecore_EObject_sosADL_RangeType: (forall (vmax: (_Option sosADL_Expression)), (forall (vmin: (_Option sosADL_Expression)), ecore_EObject))
| ecore_EObject_sosADL_ReceiveAction: (forall (variable: (_Option ecore_EString)), ecore_EObject)
| ecore_EObject_sosADL_ReceiveAnyProtocolAction: ecore_EObject
| ecore_EObject_sosADL_ReceiveProtocolAction: (forall (variable: (_Option ecore_EString)), ecore_EObject)
| ecore_EObject_sosADL_RecursiveCall: (forall (parameters: (_List sosADL_Expression)), ecore_EObject)
| ecore_EObject_sosADL_Relay: (forall (connLeft: (_Option sosADL_ComplexName)), (forall (connRight: (_Option sosADL_ComplexName)), ecore_EObject))
| ecore_EObject_sosADL_RepeatBehavior: (forall (repeated: (_Option sosADL_Behavior)), ecore_EObject)
| ecore_EObject_sosADL_RepeatProtocol: (forall (repeated: (_Option sosADL_Protocol)), ecore_EObject)
| ecore_EObject_sosADL_Select: (forall (condition: (_Option sosADL_Expression)), (forall (object: (_Option sosADL_Expression)), (forall (variable: (_Option ecore_EString)), ecore_EObject)))
| ecore_EObject_sosADL_SendAction: (forall (expression: (_Option sosADL_Expression)), ecore_EObject)
| ecore_EObject_sosADL_SendProtocolAction: (forall (expression: (_Option sosADL_Expression)), ecore_EObject)
| ecore_EObject_sosADL_Sequence: (forall (elements: (_List sosADL_Expression)), ecore_EObject)
| ecore_EObject_sosADL_SequenceType: (forall (type: (_Option sosADL_DataType)), ecore_EObject)
| ecore_EObject_sosADL_SoS: (forall (decls: (_Option sosADL_EntityBlock)), (forall (name: (_Option ecore_EString)), ecore_EObject))
| ecore_EObject_sosADL_SosADL: (forall (content: (_Option sosADL_Unit)), (forall (imports: (_List sosADL_Import)), ecore_EObject))
| ecore_EObject_sosADL_SystemDecl: (forall (assertions: (_List sosADL_AssertionDecl)), (forall (behavior: (_Option sosADL_BehaviorDecl)), (forall (datatypes: (_List sosADL_DataTypeDecl)), (forall (gates: (_List sosADL_GateDecl)), (forall (name: (_Option ecore_EString)), (forall (parameters: (_List sosADL_FormalParameter)), ecore_EObject))))))
| ecore_EObject_sosADL_TellAssertion: (forall (expression: (_Option sosADL_Expression)), (forall (name: (_Option ecore_EString)), ecore_EObject))
| ecore_EObject_sosADL_Tuple: (forall (elements: (_List sosADL_TupleElement)), ecore_EObject)
| ecore_EObject_sosADL_TupleElement: (forall (label: (_Option ecore_EString)), (forall (value: (_Option sosADL_Expression)), ecore_EObject))
| ecore_EObject_sosADL_TupleType: (forall (fields: (_List sosADL_FieldDecl)), ecore_EObject)
| ecore_EObject_sosADL_UnaryExpression: (forall (op: (_Option ecore_EString)), (forall (right: (_Option sosADL_Expression)), ecore_EObject))
| ecore_EObject_sosADL_Unify: (forall (connLeft: (_Option sosADL_ComplexName)), (forall (connRight: (_Option sosADL_ComplexName)), (forall (multLeft: (_Option sosADL_Multiplicity)), (forall (multRight: (_Option sosADL_Multiplicity)), ecore_EObject))))
| ecore_EObject_sosADL_Unit: (forall (decls: (_Option sosADL_EntityBlock)), (forall (name: (_Option ecore_EString)), ecore_EObject))
| ecore_EObject_sosADL_UnobservableBehavior: ecore_EObject
| ecore_EObject_sosADL_UntellAssertion: (forall (name: (_Option ecore_EString)), ecore_EObject)
| ecore_EObject_sosADL_Valuing: (forall (expression: (_Option sosADL_Expression)), (forall (name: (_Option ecore_EString)), (forall (type: (_Option sosADL_DataType)), ecore_EObject)))
| ecore_EObject_sosADL_ValuingBehavior: (forall (valuing: (_Option sosADL_Valuing)), ecore_EObject)
| ecore_EObject_sosADL_ValuingProtocol: (forall (valuing: (_Option sosADL_Valuing)), ecore_EObject)
 with ecore_EOperation: Type :=
| ecore_EOperation_ecore_EOperation: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eExceptions: (_List (_URI ecore_EClassifier))), (forall (eGenericExceptions: (_List ecore_EGenericType)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eParameters: (_List ecore_EParameter)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), ecore_EOperation))))))))))))
 with ecore_EPackage: Type :=
| ecore_EPackage_ecore_EPackage: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eClassifiers: (_List ecore_EClassifier)), (forall (eSubpackages: (_List ecore_EPackage)), (forall (name: (_Option ecore_EString)), (forall (nsPrefix: (_Option ecore_EString)), (forall (nsURI: (_Option ecore_EString)), ecore_EPackage))))))
 with ecore_EParameter: Type :=
| ecore_EParameter_ecore_EParameter: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), ecore_EParameter))))))))
 with ecore_EReference: Type :=
| ecore_EReference_ecore_EReference: (forall (changeable: (_Option ecore_EBoolean)), (forall (containment: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eKeys: (_List (_URI ecore_EAttribute))), (forall (eOpposite: (_Option (_URI ecore_EReference))), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (resolveProxies: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_EReference))))))))))))))))))
 with ecore_EStructuralFeature: Type :=
| ecore_EStructuralFeature_ecore_EAttribute: (forall (changeable: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (iD: (_Option ecore_EBoolean)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_EStructuralFeature)))))))))))))))
| ecore_EStructuralFeature_ecore_EReference: (forall (changeable: (_Option ecore_EBoolean)), (forall (containment: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eKeys: (_List (_URI ecore_EAttribute))), (forall (eOpposite: (_Option (_URI ecore_EReference))), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (resolveProxies: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_EStructuralFeature))))))))))))))))))
 with ecore_ETypeParameter: Type :=
| ecore_ETypeParameter_ecore_ETypeParameter: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eBounds: (_List ecore_EGenericType)), (forall (name: (_Option ecore_EString)), ecore_ETypeParameter)))
.

Inductive ecore_ETypedElement: Type :=
| ecore_ETypedElement_ecore_EAttribute: (forall (changeable: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (iD: (_Option ecore_EBoolean)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_ETypedElement)))))))))))))))
| ecore_ETypedElement_ecore_EOperation: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eExceptions: (_List (_URI ecore_EClassifier))), (forall (eGenericExceptions: (_List ecore_EGenericType)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eParameters: (_List ecore_EParameter)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), ecore_ETypedElement))))))))))))
| ecore_ETypedElement_ecore_EParameter: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), ecore_ETypedElement))))))))
| ecore_ETypedElement_ecore_EReference: (forall (changeable: (_Option ecore_EBoolean)), (forall (containment: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eKeys: (_List (_URI ecore_EAttribute))), (forall (eOpposite: (_Option (_URI ecore_EReference))), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (resolveProxies: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_ETypedElement))))))))))))))))))
.

Inductive ecore_ENamedElement: Type :=
| ecore_ENamedElement_ecore_EAttribute: (forall (changeable: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (iD: (_Option ecore_EBoolean)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_ENamedElement)))))))))))))))
| ecore_ENamedElement_ecore_EClass: (forall (abstract: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericSuperTypes: (_List ecore_EGenericType)), (forall (eOperations: (_List ecore_EOperation)), (forall (eStructuralFeatures: (_List ecore_EStructuralFeature)), (forall (eSuperTypes: (_List (_URI ecore_EClass))), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (instanceClassName: (_Option ecore_EString)), (forall (instanceTypeName: (_Option ecore_EString)), (forall (interface: (_Option ecore_EBoolean)), (forall (name: (_Option ecore_EString)), ecore_ENamedElement)))))))))))
| ecore_ENamedElement_ecore_EDataType: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (instanceClassName: (_Option ecore_EString)), (forall (instanceTypeName: (_Option ecore_EString)), (forall (name: (_Option ecore_EString)), (forall (serializable: (_Option ecore_EBoolean)), ecore_ENamedElement))))))
| ecore_ENamedElement_ecore_EOperation: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eExceptions: (_List (_URI ecore_EClassifier))), (forall (eGenericExceptions: (_List ecore_EGenericType)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eParameters: (_List ecore_EParameter)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), ecore_ENamedElement))))))))))))
| ecore_ENamedElement_ecore_EPackage: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eClassifiers: (_List ecore_EClassifier)), (forall (eSubpackages: (_List ecore_EPackage)), (forall (name: (_Option ecore_EString)), (forall (nsPrefix: (_Option ecore_EString)), (forall (nsURI: (_Option ecore_EString)), ecore_ENamedElement))))))
| ecore_ENamedElement_ecore_EParameter: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), ecore_ENamedElement))))))))
| ecore_ENamedElement_ecore_EReference: (forall (changeable: (_Option ecore_EBoolean)), (forall (containment: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eKeys: (_List (_URI ecore_EAttribute))), (forall (eOpposite: (_Option (_URI ecore_EReference))), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (resolveProxies: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_ENamedElement))))))))))))))))))
| ecore_ENamedElement_ecore_ETypeParameter: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eBounds: (_List ecore_EGenericType)), (forall (name: (_Option ecore_EString)), ecore_ENamedElement)))
.

Inductive ecore_EModelElement: Type :=
| ecore_EModelElement_ecore_EAnnotation: (forall (contents: (_List ecore_EObject)), (forall (details: (_List ecore_EStringToStringMapEntry)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (references: (_List (_URI ecore_EObject))), (forall (source: (_Option ecore_EString)), ecore_EModelElement)))))
| ecore_EModelElement_ecore_EAttribute: (forall (changeable: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (iD: (_Option ecore_EBoolean)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_EModelElement)))))))))))))))
| ecore_EModelElement_ecore_EClass: (forall (abstract: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericSuperTypes: (_List ecore_EGenericType)), (forall (eOperations: (_List ecore_EOperation)), (forall (eStructuralFeatures: (_List ecore_EStructuralFeature)), (forall (eSuperTypes: (_List (_URI ecore_EClass))), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (instanceClassName: (_Option ecore_EString)), (forall (instanceTypeName: (_Option ecore_EString)), (forall (interface: (_Option ecore_EBoolean)), (forall (name: (_Option ecore_EString)), ecore_EModelElement)))))))))))
| ecore_EModelElement_ecore_EDataType: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (instanceClassName: (_Option ecore_EString)), (forall (instanceTypeName: (_Option ecore_EString)), (forall (name: (_Option ecore_EString)), (forall (serializable: (_Option ecore_EBoolean)), ecore_EModelElement))))))
| ecore_EModelElement_ecore_EFactory: (forall (eAnnotations: (_List ecore_EAnnotation)), ecore_EModelElement)
| ecore_EModelElement_ecore_EOperation: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eExceptions: (_List (_URI ecore_EClassifier))), (forall (eGenericExceptions: (_List ecore_EGenericType)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eParameters: (_List ecore_EParameter)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), ecore_EModelElement))))))))))))
| ecore_EModelElement_ecore_EPackage: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eClassifiers: (_List ecore_EClassifier)), (forall (eSubpackages: (_List ecore_EPackage)), (forall (name: (_Option ecore_EString)), (forall (nsPrefix: (_Option ecore_EString)), (forall (nsURI: (_Option ecore_EString)), ecore_EModelElement))))))
| ecore_EModelElement_ecore_EParameter: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), ecore_EModelElement))))))))
| ecore_EModelElement_ecore_EReference: (forall (changeable: (_Option ecore_EBoolean)), (forall (containment: (_Option ecore_EBoolean)), (forall (defaultValueLiteral: (_Option ecore_EString)), (forall (derived: (_Option ecore_EBoolean)), (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eGenericType: (_Option ecore_EGenericType)), (forall (eKeys: (_List (_URI ecore_EAttribute))), (forall (eOpposite: (_Option (_URI ecore_EReference))), (forall (eType: (_Option (_URI ecore_EClassifier))), (forall (lowerBound: (_Option ecore_EInt)), (forall (name: (_Option ecore_EString)), (forall (ordered: (_Option ecore_EBoolean)), (forall (resolveProxies: (_Option ecore_EBoolean)), (forall (transient: (_Option ecore_EBoolean)), (forall (unique: (_Option ecore_EBoolean)), (forall (unsettable: (_Option ecore_EBoolean)), (forall (upperBound: (_Option ecore_EInt)), (forall (volatile: (_Option ecore_EBoolean)), ecore_EModelElement))))))))))))))))))
| ecore_EModelElement_ecore_ETypeParameter: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eBounds: (_List ecore_EGenericType)), (forall (name: (_Option ecore_EString)), ecore_EModelElement)))
.

Inductive ecore_EFactory: Type :=
| ecore_EFactory_ecore_EFactory: (forall (eAnnotations: (_List ecore_EAnnotation)), ecore_EFactory)
.

Inductive ecore_EDataType: Type :=
| ecore_EDataType_ecore_EDataType: (forall (eAnnotations: (_List ecore_EAnnotation)), (forall (eTypeParameters: (_List ecore_ETypeParameter)), (forall (instanceClassName: (_Option ecore_EString)), (forall (instanceTypeName: (_Option ecore_EString)), (forall (name: (_Option ecore_EString)), (forall (serializable: (_Option ecore_EBoolean)), ecore_EDataType))))))
.

