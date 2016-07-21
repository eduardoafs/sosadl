package org.archware.sosadl.validation.typing;

import java.math.BigInteger;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.archware.sosadl.sosADL.Action;
import org.archware.sosadl.sosADL.ActionSuite;
import org.archware.sosadl.sosADL.Behavior;
import org.archware.sosadl.sosADL.BehaviorDecl;
import org.archware.sosadl.sosADL.BehaviorStatement;
import org.archware.sosadl.sosADL.ChooseBehavior;
import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.sosADL.Connection;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.DoExprBehavior;
import org.archware.sosadl.sosADL.DoneBehavior;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.ForEachBehavior;
import org.archware.sosadl.sosADL.IfThenElseBehavior;
import org.archware.sosadl.sosADL.ModeType;
import org.archware.sosadl.sosADL.ReceiveAction;
import org.archware.sosadl.sosADL.RecursiveCall;
import org.archware.sosadl.sosADL.RepeatBehavior;
import org.archware.sosadl.sosADL.SendAction;
import org.archware.sosadl.sosADL.SequenceType;
import org.archware.sosadl.sosADL.SosADLPackage;
import org.archware.sosadl.sosADL.Valuing;
import org.archware.sosadl.sosADL.ValuingBehavior;
import org.archware.sosadl.tv.typeCheckerHelper.TypeVariable;
import org.archware.sosadl.validation.typing.impl.GateOrDutyEnvContent;
import org.archware.sosadl.validation.typing.impl.VariableEnvContent;
import org.archware.sosadl.validation.typing.proof.And;
import org.archware.sosadl.validation.typing.proof.Condition_false;
import org.archware.sosadl.validation.typing.proof.Condition_true;
import org.archware.sosadl.validation.typing.proof.Ex;
import org.archware.sosadl.validation.typing.proof.Forall;
import org.archware.sosadl.validation.typing.proof.Mode_receive;
import org.archware.sosadl.validation.typing.proof.Mode_send;
import org.archware.sosadl.validation.typing.proof.Optionally;
import org.archware.sosadl.validation.typing.proof.Type_behavior;
import org.archware.sosadl.validation.typing.proof.Type_bodyprefix;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_finalbody;
import org.archware.sosadl.validation.typing.proof.Type_finalbody_other;
import org.archware.sosadl.validation.typing.proof.Type_generic_finalbody;
import org.archware.sosadl.validation.typing.proof.Type_nonfinalbody;
import org.archware.sosadl.validation.typing.proof.Type_valuing;
import org.archware.utils.IntPair;
import org.archware.utils.Pair;
import org.archware.utils.StreamUtils;
import org.eclipse.emf.common.util.EList;

public abstract class TypeCheckerBehavior extends TypeCheckerGenericBehavior {

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
		Function<Behavior, EList<BehaviorStatement>> getBlock = Behavior::getStatements;
		BiFunction<Environment, BehaviorStatement, Type_finalbody_other> proveOther = this::final_other;
		BiFunction<Environment, BehaviorStatement, Pair<Environment, Type_bodyprefix>> gp = this::type_bodyprefix;
		BiFunction<Environment, Behavior, Type_nonfinalbody> gnf = this::type_nonfinalbody;
		Function<ChooseBehavior, EList<Behavior>> getBranches = ChooseBehavior::getBranches;
		Function<IfThenElseBehavior, Expression> getCondition = IfThenElseBehavior::getCondition;
		Function<IfThenElseBehavior, Behavior> getThen = IfThenElseBehavior::getIfTrue;
		Function<IfThenElseBehavior, Behavior> getElse = IfThenElseBehavior::getIfFalse;
		Function<RepeatBehavior, Behavior> getRepeated = RepeatBehavior::getRepeated;
		Type_generic_finalbody<Behavior, BehaviorStatement, ChooseBehavior, DoneBehavior, IfThenElseBehavior, RepeatBehavior, Type_finalbody_other, Type_expression, Type_bodyprefix, Type_nonfinalbody> p1 = type_generic_finalbody(
				Behavior.class, BehaviorStatement.class, getBlock, "Behavior", ChooseBehavior.class, getBranches,
				DoneBehavior.class, IfThenElseBehavior.class, getCondition,
				SosADLPackage.Literals.IF_THEN_ELSE_BEHAVIOR__CONDITION, getThen,
				SosADLPackage.Literals.IF_THEN_ELSE_BEHAVIOR__IF_TRUE, getElse,
				SosADLPackage.Literals.IF_THEN_ELSE_BEHAVIOR__IF_FALSE, RepeatBehavior.class, getRepeated,
				SosADLPackage.Literals.REPEAT_BEHAVIOR__REPEATED, Type_finalbody_other.class, proveOther,
				Type_expression.class, this::type_expression, Type_bodyprefix.class, gp, Type_nonfinalbody.class, gnf,
				gamma, b, behavior, SosADLPackage.Literals.PROTOCOL__STATEMENTS, 0);
		Type_finalbody proof = p(Type_finalbody.class, gamma, (gamma_) -> createType_finalbody_generic(gamma_, b, p1));
		return saveProof(behavior, proof);
	}

	private Type_finalbody_other final_other(Environment gamma, BehaviorStatement s) {
		if (s instanceof RecursiveCall) {
			RecursiveCall rc = (RecursiveCall) s;
			if (rc.getParameters().isEmpty()) {
				return saveProof(s,
						p(Type_finalbody_other.class, gamma, (gamma_) -> createType_finalbody_RecursiveCall(gamma_)));
			} else {
				error("Statement `behavior' cannot have any parameter", s,
						SosADLPackage.Literals.RECURSIVE_CALL__PARAMETERS);
				return null;
			}
		} else {
			error("Statement `" + labelOf(s) + "' not allowed at tail position", s, null);
			return null;
		}
	}

	private Type_nonfinalbody type_nonfinalbody(Environment gamma, Behavior behavior) {
		return type_nonfinalbody(gamma, behavior.getStatements(), behavior, 0);
	}

	private Type_nonfinalbody type_nonfinalbody(Environment gamma, EList<BehaviorStatement> b, Behavior behavior,
			int index) {
		if (b.isEmpty()) {
			return p(Type_nonfinalbody.class, gamma, (gamma_) -> createType_nonfinalbody_empty(gamma_));
		} else {
			BehaviorStatement first = b.get(0);
			EList<BehaviorStatement> l = cdr(b);
			Pair<Environment, Type_bodyprefix> p1 = type_bodyprefix(gamma, first);
			if (p1 != null && p1.getA() != null && p1.getB() != null) {
				Type_nonfinalbody p2 = type_nonfinalbody(p1.getA(), l, behavior, index + 1);
				return saveProof(first, p(Type_nonfinalbody.class, gamma, (gamma_) -> p(Type_nonfinalbody.class,
						p1.getA(),
						(gamma1_) -> createType_nonfinalbody_prefix(gamma_, first, gamma1_, l, p1.getB(), p2))));
			} else {
				return null;
			}
		}
	}

	private Pair<Environment, Type_bodyprefix> type_bodyprefix(Environment gamma, BehaviorStatement s) {
		saveEnvironment(s, gamma);
		if (s instanceof DoExprBehavior) {
			DoExprBehavior de = (DoExprBehavior) s;
			Expression e = de.getExpression();
			if (e != null) {
				Pair<Type_expression, DataType> pt = type_expression(gamma, e);
				if (pt.getA() != null && pt.getB() != null) {
					Type_bodyprefix proof = p(Type_bodyprefix.class, gamma, (gamma_) -> p(Type_bodyprefix.class,
							pt.getB(), (tau_) -> createType_bodyprefix_DoExpr(gamma_, e, tau_, pt.getA())));
					return new Pair<>(gamma, saveProof(s, proof));
				} else {
					return null;
				}
			} else {
				error("An expression is expected", s, SosADLPackage.Literals.DO_EXPR_BEHAVIOR__EXPRESSION);
				return null;
			}
		} else if (s instanceof ValuingBehavior) {
			Valuing v = ((ValuingBehavior) s).getValuing();
			Pair<Type_valuing<Type_expression>, Environment> pe = type_valuing(this::type_expression, gamma, v);
			Environment gamma1 = pe.getB();
			Type_valuing<Type_expression> p1 = pe.getA();
			if (pe != null && p1 != null && gamma1 != null) {
				Type_bodyprefix proof = p(Type_bodyprefix.class, gamma, (gamma_) -> p(Type_bodyprefix.class, gamma1,
						(gamma1_) -> createType_bodyprefix_Valuing(gamma_, v, gamma1_, p1)));
				return new Pair<>(gamma1, saveProof(s, proof));
			} else {
				return null;
			}
		} else if (s instanceof IfThenElseBehavior) {
			IfThenElseBehavior ite = (IfThenElseBehavior) s;
			Expression c = ite.getCondition();
			Behavior t = ite.getIfTrue();
			Behavior oe = ite.getIfFalse();
			if (c != null && t != null) {
				Pair<Type_expression, DataType> pt = type_expression(gamma, c);
				Type_expression p1 = pt.getA();
				DataType dt = pt.getB();
				if (p1 != null && dt != null) {
					inference.addConstraint(dt, createBooleanType(), c);
					EList<BehaviorStatement> ts = t.getStatements();
					Pair<Environment, Condition_true> gammat = condition_true(gamma, c, t);
					Type_nonfinalbody p3 = type_nonfinalbody(gammat.getA(), ts, t, 0);
					Optionally<Behavior, Ex<Environment, And<Condition_false, Type_nonfinalbody>>> p4 = proveOptionally(
							gamma, oe, (g, e) -> {
								Pair<Environment, Condition_false> gammae = condition_false(g, c, e);
								@SuppressWarnings("unchecked")
								Ex<Environment, And<Condition_false, Type_nonfinalbody>> proof = p(Ex.class,
										gammae.getA(), (gammae_) -> createEx_intro(gammae_, createConj(gammae.getB(),
												type_nonfinalbody(gammae_, e.getStatements(), e, 0))));
								return proof;
							});
					return new Pair<>(gamma,
							saveProof(s,
									p(Type_bodyprefix.class, gamma,
											(gamma_) -> p(Type_bodyprefix.class, gammat.getA(),
													(gammat_) -> createType_bodyprefix_IfThenElse(gamma_, c, gammat_,
															ts, oe, p1, gammat.getB(), p3, p4)))));
				} else {
					return null;
				}
			} else {
				if (c == null) {
					error("The `if' statement must have a condition", s,
							SosADLPackage.Literals.IF_THEN_ELSE_BEHAVIOR__CONDITION);
				}
				if (t == null) {
					error("The `if' statement must have a `then' clause", s,
							SosADLPackage.Literals.IF_THEN_ELSE_BEHAVIOR__IF_TRUE);
				}
				return null;
			}
		} else if (s instanceof ChooseBehavior) {
			ChooseBehavior c = (ChooseBehavior) s;
			EList<Behavior> branches = c.getBranches();
			Forall<Behavior, Type_nonfinalbody> p1 = proveForall(branches,
					(x) -> type_nonfinalbody(gamma, x.getStatements(), x, 0));
			return new Pair<>(gamma, saveProof(s,
					p(Type_bodyprefix.class, gamma, (gamma_) -> createType_bodyprefix_Choose(gamma_, branches, p1))));
		} else if (s instanceof ForEachBehavior) {
			ForEachBehavior f = (ForEachBehavior) s;
			String x = f.getVariable();
			Expression vals = f.getSetOfValues();
			Behavior r = f.getRepeated();
			if (x != null && vals != null && r != null) {
				Pair<Type_expression, DataType> pt = type_expression(gamma, vals);
				Type_expression p1 = pt.getA();
				DataType tauVals = pt.getB();
				if (p1 != null && tauVals != null) {
					TypeVariable tau__x = createFreshTypeVariable(s, SosADLPackage.Literals.FOR_EACH_BEHAVIOR__VARIABLE,
							TypeInferenceSolver::upperOrLowerSolver);
					TypeInferenceSolver.streamVariables(tauVals).forEach((a) -> inference.addDependency(tau__x, a));
					inference.addConstraint(tauVals, createSequenceType(tau__x), s,
							SosADLPackage.Literals.FOR_EACH_BEHAVIOR__SET_OF_VALUES);
					Environment gamma1 = gamma.put(x, new VariableEnvContent(s, tau__x));
					EList<BehaviorStatement> b = r.getStatements();
					Type_nonfinalbody p2 = type_nonfinalbody(gamma1, b, r, 0);
					return new Pair<>(gamma,
							saveProof(s,
									p(Type_bodyprefix.class, gamma, (gamma_) -> p(Type_bodyprefix.class, tauVals,
											(tauVals_) -> p(Type_bodyprefix.class, tau__x,
													(tau__x_) -> createType_bodyprefix_ForEach(gamma_, x, vals,
															((SequenceType) tauVals_).getType(), tau__x_, b, p1, p2,
															subtype(((SequenceType) tauVals_).getType(), tau__x_, s,
																	SosADLPackage.Literals.FOR_EACH_BEHAVIOR__SET_OF_VALUES)
																			.orElse(null)))))));
				} else {
					return null;
				}
			} else {
				if (x == null) {
					error("A variable name must be given", s, SosADLPackage.Literals.FOR_EACH_BEHAVIOR__VARIABLE);
				}
				if (vals == null) {
					error("A sequence expression is expected", s,
							SosADLPackage.Literals.FOR_EACH_BEHAVIOR__SET_OF_VALUES);
				}
				if (r == null) {
					error("A body is expected", s, SosADLPackage.Literals.FOR_EACH_BEHAVIOR__REPEATED);
				}
				return null;
			}
		} else if (s instanceof Action) {
			Action a = (Action) s;
			ComplexName cn = a.getComplexName();
			ActionSuite as = a.getSuite();
			if (cn != null && as != null) {
				if (cn.getName().size() == 2) {
					String gd = cn.getName().get(0);
					String conn = cn.getName().get(1);
					EnvContent gdEc = gamma.get(gd);
					if (gdEc != null) {
						if (gdEc instanceof GateOrDutyEnvContent) {
							GateOrDutyEnvContent ec = (GateOrDutyEnvContent) gdEc;
							EList<Connection> endpoints = ec.getConnections();
							Pair<BigInteger, Connection> rankedConnection = lookupForConnection(endpoints, conn);
							if (rankedConnection != null) {
								BigInteger rank = rankedConnection.getA();
								Connection connection = rankedConnection.getB();
								boolean is_env = connection.isEnvironment();
								ModeType mode = connection.getMode();
								DataType conn__tau = connection.getValueType();
								if (mode != null && conn__tau != null) {
									if (as instanceof SendAction) {
										SendAction sa = (SendAction) as;
										return type_bodyprefix_Send(gamma, s, cn, gd, conn, endpoints, rank, is_env,
												mode, conn__tau, sa);
									} else if (as instanceof ReceiveAction) {
										ReceiveAction ra = (ReceiveAction) as;
										return type_bodyprefix_Receive(gamma, s, cn, gd, conn, endpoints, rank, is_env,
												mode, conn__tau, ra);
									} else {
										error("Unknown action command", s, SosADLPackage.Literals.ACTION__SUITE);
										return null;
									}
								} else {
									throw new IllegalArgumentException();
								}
							} else {
								error("No connection named `" + conn + "' in gate or duty `" + gd + "'", cn,
										SosADLPackage.Literals.COMPLEX_NAME__NAME, 1);
								return null;
							}
						} else {
							error("`" + gd + "' is neither a gate nor a duty", cn,
									SosADLPackage.Literals.COMPLEX_NAME__NAME, 0);
							return null;
						}
					} else {
						error("Gate or duty named `" + gd + "' is undefined", cn,
								SosADLPackage.Literals.COMPLEX_NAME__NAME, 0);
						return null;
					}
				} else {
					error("`via' must be followed by a name of form `<gate-or-duty> :: <connection>'", s,
							SosADLPackage.Literals.ACTION__COMPLEX_NAME);
					return null;
				}
			} else {
				if (cn == null) {
					error("A complex name must be provided", s, SosADLPackage.Literals.ACTION__COMPLEX_NAME);
				}
				if (as == null) {
					error("An action command (either send or receive) is expected", s,
							SosADLPackage.Literals.ACTION__SUITE);
				}
				return null;
			}
		} else {
			error("Statement `" + labelOf(s) + "' must be at tail position", s, null);
			return null;
		}
	}

	private Pair<Environment, Type_bodyprefix> type_bodyprefix_Receive(Environment gamma, BehaviorStatement s,
			ComplexName cn, String gd, String conn, EList<Connection> endpoints, BigInteger rank, boolean is_env,
			ModeType mode, DataType conn__tau, ReceiveAction ra) {
		String x = ra.getVariable();
		if (x != null) {
			Mode_receive p3 = proveReceiveMode(mode, conn, cn);
			if (p3 != null) {
				Environment gamma1 = gamma.put(x, new VariableEnvContent(ra, conn__tau));
				Type_bodyprefix proof = p(Type_bodyprefix.class, gamma,
						(gamma_) -> p(Type_bodyprefix.class, gamma1,
								(gamma1_) -> p(Type_bodyprefix.class, conn__tau,
										(conn__tau_) -> createType_bodyprefix_Receive(gamma_, gd, endpoints, is_env,
												conn, mode, conn__tau_, x, gamma1_, createReflexivity(),
												createEx_intro(rank, createReflexivity()), p3, createReflexivity()))));
				return new Pair<>(gamma1, saveProof(s, proof));
			} else {
				return null;
			}
		} else {
			error("A variable name is expected in the `receive' command", ra,
					SosADLPackage.Literals.RECEIVE_ACTION__VARIABLE);
			return null;
		}
	}

	private Pair<Environment, Type_bodyprefix> type_bodyprefix_Send(Environment gamma, BehaviorStatement s,
			ComplexName cn, String gd, String conn, EList<Connection> endpoints, BigInteger rank, boolean is_env,
			ModeType mode, DataType conn__tau, SendAction sa) {
		Expression e = sa.getExpression();
		if (e != null) {
			Mode_send p3 = proveSendMode(mode, conn, cn);
			Pair<Type_expression, DataType> pt = type_expression(gamma, e);
			Type_expression p4 = pt.getA();
			DataType tau__e = pt.getB();
			if (p3 != null && p4 != null && tau__e != null) {
				inference.addConstraint(tau__e, conn__tau, sa, SosADLPackage.Literals.SEND_ACTION__EXPRESSION);
				Type_bodyprefix proof = p(Type_bodyprefix.class, gamma,
						(gamma_) -> p(Type_bodyprefix.class, conn__tau,
								(conn__tau_) -> p(Type_bodyprefix.class, tau__e,
										(tau__e_) -> createType_bodyprefix_Send(gamma_, gd, endpoints, is_env, conn,
												mode, conn__tau_, e, tau__e_, createReflexivity(),
												createEx_intro(rank, createReflexivity()), p3, p4,
												subtype(tau__e_, conn__tau_, sa,
														SosADLPackage.Literals.SEND_ACTION__EXPRESSION)
																.orElse(null)))));
				return new Pair<>(gamma, saveProof(s, proof));
			} else {
				return null;
			}
		} else {
			error("An expression is expected after `send'", sa, SosADLPackage.Literals.SEND_ACTION__EXPRESSION);
			return null;
		}
	}

	private Mode_send proveSendMode(ModeType mode, String conn, ComplexName cn) {
		switch (mode) {
		case MODE_TYPE_OUT:
			return createMode_send_out();
		case MODE_TYPE_INOUT:
			return createMode_send_inout();
		case MODE_TYPE_IN:
			error("Connection `" + conn + "' is a `in' connection that cannot be used by a `send' action", cn,
					SosADLPackage.Literals.COMPLEX_NAME__NAME, 1);
			return null;
		}
		throw new IllegalArgumentException();
	}

	private Mode_receive proveReceiveMode(ModeType mode, String conn, ComplexName cn) {
		switch (mode) {
		case MODE_TYPE_OUT:
			error("Connection `" + conn + "' is a `out' connection that cannot be used by a `receive' action", cn,
					SosADLPackage.Literals.COMPLEX_NAME__NAME, 1);
			return null;
		case MODE_TYPE_INOUT:
			return createMode_receive_inout();
		case MODE_TYPE_IN:
			return createMode_receive_in();
		}
		throw new IllegalArgumentException();
	}

	private Pair<BigInteger, Connection> lookupForConnection(EList<Connection> endpoints, String conn) {
		List<IntPair<Connection>> l = StreamUtils.indexed(endpoints.stream())
				.filter((p) -> conn.equals(p.getB().getName())).collect(Collectors.toList());
		if (l.size() >= 2) {
			throw new IllegalArgumentException("several connections named `" + conn + "' in the environment");
		}
		return l.stream().findAny().map((p) -> new Pair<>(BigInteger.valueOf(p.getA()), p.getB())).orElse(null);
	}

	private String labelOf(BehaviorStatement s) {
		if (s instanceof ValuingBehavior) {
			return "value";
		} else if (s instanceof RepeatBehavior) {
			return "repeat";
		} else if (s instanceof IfThenElseBehavior) {
			return "if";
		} else if (s instanceof ChooseBehavior) {
			return "choose";
		} else if (s instanceof ForEachBehavior) {
			return "foreach";
		} else if (s instanceof DoExprBehavior) {
			return "do";
		} else if (s instanceof DoneBehavior) {
			return "done";
		} else if (s instanceof RecursiveCall) {
			return "behavior";
		} else if (s instanceof Action) {
			return "via";
		} else {
			return "(unknown statement)";
		}
	}

}