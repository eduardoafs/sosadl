package org.archware.sosadl.validation.typing;

import java.util.function.Function;

import org.archware.sosadl.sosADL.Behavior;
import org.archware.sosadl.sosADL.BehaviorDecl;
import org.archware.sosadl.sosADL.BehaviorStatement;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.DoExpr;
import org.archware.sosadl.sosADL.Done;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.SosADLPackage;
import org.archware.sosadl.sosADL.Valuing;
import org.archware.sosadl.validation.typing.impl.VariableEnvContent;
import org.archware.sosadl.validation.typing.proof.ProofTerm;
import org.archware.sosadl.validation.typing.proof.Type_behavior;
import org.archware.sosadl.validation.typing.proof.Type_bodyprefix;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_finalbody;
import org.archware.utils.Pair;
import org.eclipse.emf.common.util.EList;

public abstract class TypeCheckerBehavior extends TypeCheckerConnections {

	protected Type_behavior type_behavior(Environment gamma, BehaviorDecl b) {
		if (b.getName() != null && b.getBody() != null) {
			return saveProof(b, createType_BehaviorDecl(gamma, b.getName(), b.getBody().getStatements(),
					type_finalbody(gamma, b.getBody().getStatements(), b.getBody(), 0)));
		} else {
			if (b.getName() == null) {
				error("The behavior must have a name", b, SosADLPackage.Literals.BEHAVIOR_DECL__NAME);
			}
			if (b.getBody() == null) {
				error("The behavior must have a body", b, SosADLPackage.Literals.BEHAVIOR_DECL__BODY);
			}
			return null;
		}
	}

	private Type_finalbody type_finalbody(Environment gamma, EList<BehaviorStatement> b, Behavior behavior, int index) {
		if (b.isEmpty()) {
			error("`done' (or any other final statement) is missing to terminate the body", behavior,
					SosADLPackage.Literals.BEHAVIOR__STATEMENTS, index - 1);
			return null;
		} else {
			BehaviorStatement first = b.get(0);
			EList<BehaviorStatement> l = cdr(b);
			if (first instanceof Done) {
				if (l.isEmpty()) {
					return saveProof(first, createType_finalbody_Done(gamma));
				} else {
					error("The `done' statement is allowed only at tail position", first, null);
					return null;
				}
			} else {
				Type_bodyprefix<Type_finalbody> p1 = type_bodyprefix(gamma, first,
						(g) -> type_finalbody(g, l, behavior, index + 1));
				if (p1 != null) {
					return saveProof(first, createType_finalbody_prefix(gamma, first, l, p1));
				} else {
					return null;
				}
			}
		}
	}

	private <T extends ProofTerm> Type_bodyprefix<T> type_bodyprefix(Environment gamma, BehaviorStatement s,
			Function<Environment, T> tail) {
		if (s instanceof DoExpr) {
			DoExpr de = (DoExpr) s;
			Expression e = de.getExpression();
			if (e != null) {
				Pair<Type_expression, DataType> pt = type_expression(gamma, e);
				if (pt.getA() != null && pt.getB() != null) {
					T p2 = tail.apply(gamma);
					return saveProof(s, createType_bodyprefix_DoExpr(gamma, e, pt.getB(), pt.getA(), p2));
				} else {
					return null;
				}
			} else {
				error("An expression is expected", s, SosADLPackage.Literals.DO_EXPR__EXPRESSION);
				return null;
			}
		} else if (s instanceof Valuing) {
			Valuing v = (Valuing) s;
			String x = v.getVariable();
			Expression e = v.getExpression();
			if (x != null && e != null) {
				Pair<Type_expression, DataType> pt = type_expression(gamma, e);
				if (pt.getA() != null && pt.getB() != null) {
					T p2 = tail.apply(gamma.put(x, new VariableEnvContent(s, pt.getB())));
					DataType tau = v.getType();
					if (tau == null) {
						return saveProof(s,
								createType_bodyprefix_Valuing_inferred(gamma, x, e, pt.getB(), pt.getA(), p2));
					} else {
						return saveProof(s, createType_bodyprefix_Valuing_typed(gamma, x, e, tau, pt.getB(), pt.getA(),
								subtype(pt.getB(), tau, s, SosADLPackage.Literals.VALUING__EXPRESSION).orElse(null),
								p2));
					}
				} else {
					return null;
				}
			} else {
				if (x == null) {
					error("The variable must have a name", s, SosADLPackage.Literals.VALUING__VARIABLE);
				}
				if (e == null) {
					error("The variable must be assigned an expression", s, SosADLPackage.Literals.VALUING__EXPRESSION);
				}
				return null;
			}
		} else {
			error("Unknown statement", s, null);
			return null;
		}
	}

}