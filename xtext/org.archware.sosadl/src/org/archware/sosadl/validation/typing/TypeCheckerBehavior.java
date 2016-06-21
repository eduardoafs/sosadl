package org.archware.sosadl.validation.typing;

import java.util.function.Function;

import org.archware.sosadl.sosADL.Behavior;
import org.archware.sosadl.sosADL.BehaviorDecl;
import org.archware.sosadl.sosADL.BehaviorStatement;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.DoExprBehavior;
import org.archware.sosadl.sosADL.DoneBehavior;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.IfThenElseBehavior;
import org.archware.sosadl.sosADL.RecursiveCall;
import org.archware.sosadl.sosADL.RepeatBehavior;
import org.archware.sosadl.sosADL.SosADLPackage;
import org.archware.sosadl.sosADL.Valuing;
import org.archware.sosadl.sosADL.ValuingBehavior;
import org.archware.sosadl.validation.typing.impl.VariableEnvContent;
import org.archware.sosadl.validation.typing.proof.Condition_false;
import org.archware.sosadl.validation.typing.proof.Condition_true;
import org.archware.sosadl.validation.typing.proof.ProofTerm;
import org.archware.sosadl.validation.typing.proof.Type_behavior;
import org.archware.sosadl.validation.typing.proof.Type_bodyprefix;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_finalbody;
import org.archware.sosadl.validation.typing.proof.Type_nonfinalbody;
import org.archware.utils.Pair;
import org.eclipse.emf.common.util.EList;

public abstract class TypeCheckerBehavior extends TypeCheckerCondition {

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
			if (l.isEmpty()) {
				if (first instanceof DoneBehavior) {
					return saveProof(first,
							p(Type_finalbody.class, gamma, (gamma_) -> createType_finalbody_Done(gamma_)));
				} else if (first instanceof RecursiveCall) {
					RecursiveCall rc = (RecursiveCall) first;
					if (rc.getParameters().isEmpty()) {
						return saveProof(first,
								p(Type_finalbody.class, gamma, (gamma_) -> createType_finalbody_RecursiveCall(gamma_)));
					} else {
						if (!rc.getParameters().isEmpty()) {
							error("The recursive call cannot have any effective parameter", first,
									SosADLPackage.Literals.RECURSIVE_CALL__PARAMETERS);
						}
						return null;
					}
				} else if (first instanceof RepeatBehavior) {
					RepeatBehavior r = (RepeatBehavior) first;
					Behavior rb = r.getRepeated();
					if (rb != null) {
						EList<BehaviorStatement> rbl = rb.getStatements();
						Type_nonfinalbody p1 = type_nonfinalbody(gamma, rbl, rb, 0);
						return saveProof(first, p(Type_finalbody.class, gamma,
								(gamma_) -> createType_finalbody_Repeat(gamma_, rbl, p1)));
					} else {
						error("There must be a repeated behavior", first,
								SosADLPackage.Literals.REPEAT_BEHAVIOR__REPEATED);
						return null;
					}
				} else if (first instanceof IfThenElseBehavior) {
					IfThenElseBehavior ite = (IfThenElseBehavior) first;
					Expression c = ite.getCondition();
					Behavior t = ite.getIfTrue();
					Behavior e = ite.getIfFalse();
					if (c != null && t != null && e != null) {
						Pair<Type_expression, DataType> pt = type_expression(gamma, c);
						Type_expression p1 = pt.getA();
						DataType dt = pt.getB();
						if (p1 != null && dt != null) {
							inference.addConstraint(dt, createBooleanType(), e);
							EList<BehaviorStatement> ts = t.getStatements();
							Pair<Environment, Condition_true> gammat = condition_true(gamma, c, t);
							Type_finalbody p3 = type_finalbody(gammat.getA(), ts, t, 0);
							EList<BehaviorStatement> es = e.getStatements();
							Pair<Environment, Condition_false> gammae = condition_false(gamma, c, e);
							Type_finalbody p5 = type_finalbody(gammae.getA(), es, e, 0);
							return saveProof(first,
									p(Type_finalbody.class, gamma,
											(gamma_) -> p(Type_finalbody.class, gammat.getA(),
													(gammat_) -> p(Type_finalbody.class, gammae.getA(),
															(gammae_) -> createType_finalbody_IfThenElse_general(gamma_,
																	c, gammat_, ts, gammae_, es, p1,
																	gammat.getB(), p3, gammae.getB(), p5)))));
						} else {
							return null;
						}
					} else {
						if (c == null) {
							error("The `if' statement must have a condition", first,
									SosADLPackage.Literals.IF_THEN_ELSE_BEHAVIOR__CONDITION);
						}
						if (t == null) {
							error("The `if' statement must have a `then' clause", first,
									SosADLPackage.Literals.IF_THEN_ELSE_BEHAVIOR__IF_TRUE);
						}
						if (e == null) {
							error("At tail position, the `if' statement must have an `else' clause", first,
									SosADLPackage.Literals.IF_THEN_ELSE_BEHAVIOR__IF_FALSE);
						}
						return null;
					}
				} else {
					error("Statement `" + labelOf(first) + "' is not allowed at tail position", first, null);
					return null;
				}
			} else {
				Type_bodyprefix<Type_finalbody> p1 = type_bodyprefix(gamma, first,
						(g) -> type_finalbody(g, l, behavior, index + 1));
				if (p1 != null) {
					return saveProof(first, p(Type_finalbody.class, gamma,
							(gamma_) -> createType_finalbody_prefix(gamma_, first, l, p1)));
				} else {
					return null;
				}
			}
		}
	}

	private Type_nonfinalbody type_nonfinalbody(Environment gamma, EList<BehaviorStatement> b, Behavior behavior,
			int index) {
		if (b.isEmpty()) {
			return p(Type_nonfinalbody.class, gamma, (gamma_) -> createType_nonfinalbody_empty(gamma_));
		} else {
			BehaviorStatement first = b.get(0);
			EList<BehaviorStatement> l = cdr(b);
			Type_bodyprefix<Type_nonfinalbody> p1 = type_bodyprefix(gamma, first,
					(g) -> type_nonfinalbody(g, l, behavior, index + 1));
			if (p1 != null) {
				return saveProof(first, p(Type_nonfinalbody.class, gamma,
						(gamma_) -> createType_nonfinalbody_prefix(gamma_, first, l, p1)));
			} else {
				return null;
			}
		}
	}

	private <T extends ProofTerm> Type_bodyprefix<T> type_bodyprefix(Environment gamma, BehaviorStatement s,
			Function<Environment, T> tail) {
		if (s instanceof DoExprBehavior) {
			DoExprBehavior de = (DoExprBehavior) s;
			Expression e = de.getExpression();
			if (e != null) {
				Pair<Type_expression, DataType> pt = type_expression(gamma, e);
				if (pt.getA() != null && pt.getB() != null) {
					T p2 = tail.apply(gamma);
					@SuppressWarnings("unchecked")
					Type_bodyprefix<T> proof = p(Type_bodyprefix.class, gamma, (gamma_) -> p(Type_bodyprefix.class,
							pt.getB(), (tau_) -> createType_bodyprefix_DoExpr(gamma_, e, tau_, pt.getA(), p2)));
					return saveProof(s, proof);
				} else {
					return null;
				}
			} else {
				error("An expression is expected", s, SosADLPackage.Literals.DO_EXPR_BEHAVIOR__EXPRESSION);
				return null;
			}
		} else if (s instanceof ValuingBehavior) {
			Valuing v = ((ValuingBehavior) s).getValuing();
			String x = v.getName();
			Expression e = v.getExpression();
			if (x != null && e != null) {
				Pair<Type_expression, DataType> pt = type_expression(gamma, e);
				DataType tau__e = pt.getB();
				if (pt.getA() != null && tau__e != null) {
					DataType tau = v.getType();
					if (tau == null) {
						T p2 = tail.apply(gamma.put(x, new VariableEnvContent(s, tau__e)));
						@SuppressWarnings("unchecked")
						Type_bodyprefix<T> proof = p(Type_bodyprefix.class, gamma,
								(gamma_) -> p(Type_bodyprefix.class, tau__e,
										(tau__e_) -> createType_bodyprefix_Valuing_inferred(gamma_, x, e, tau__e_,
												pt.getA(), p2)));
						return saveProof(s, proof);
					} else {
						T p2 = tail.apply(gamma.put(x, new VariableEnvContent(s, tau)));
						@SuppressWarnings("unchecked")
						Type_bodyprefix<T> proof = p(Type_bodyprefix.class, gamma,
								(gamma_) -> p(Type_bodyprefix.class, tau__e,
										(tau__e_) -> p(Type_bodyprefix.class, tau,
												(tau_) -> createType_bodyprefix_Valuing_typed(gamma_, x, e, tau_,
														tau__e_, pt.getA(),
														subtype(tau__e_, tau_, v,
																SosADLPackage.Literals.VALUING__EXPRESSION)
																		.orElse(null),
														p2))));
						return saveProof(s, proof);
					}
				} else {
					return null;
				}
			} else {
				if (x == null) {
					error("The variable must have a name", v, SosADLPackage.Literals.VALUING__NAME);
				}
				if (e == null) {
					error("The variable must be assigned an expression", v, SosADLPackage.Literals.VALUING__EXPRESSION);
				}
				return null;
			}
		} else {
			error("Statement `" + labelOf(s) + "' must be at tail position", s, null);
			return null;
		}
	}

	private String labelOf(BehaviorStatement s) {
		if (s instanceof ValuingBehavior) {
			return "value";
		} else if (s instanceof RepeatBehavior) {
			return "repeat";
		} else if (s instanceof IfThenElseBehavior) {
			return "if";
		} else if (s instanceof DoExprBehavior) {
			return "do";
		} else if (s instanceof DoneBehavior) {
			return "done";
		} else if (s instanceof RecursiveCall) {
			return "behavior";
		} else {
			return "(unknown statement)";
		}
	}

}