package org.archware.sosadl.validation.typing;

import org.archware.sosadl.sosADL.AssertionDecl;
import org.archware.sosadl.sosADL.ChooseProtocol;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.DoExprProtocol;
import org.archware.sosadl.sosADL.DoneProtocol;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.ForEachProtocol;
import org.archware.sosadl.sosADL.IfThenElseProtocol;
import org.archware.sosadl.sosADL.Protocol;
import org.archware.sosadl.sosADL.ProtocolAction;
import org.archware.sosadl.sosADL.ProtocolDecl;
import org.archware.sosadl.sosADL.ProtocolStatement;
import org.archware.sosadl.sosADL.RepeatProtocol;
import org.archware.sosadl.sosADL.SosADLPackage;
import org.archware.sosadl.sosADL.ValuingProtocol;
import org.archware.sosadl.validation.typing.proof.Condition_false;
import org.archware.sosadl.validation.typing.proof.Condition_true;
import org.archware.sosadl.validation.typing.proof.Forall;
import org.archware.sosadl.validation.typing.proof.Type_assertion;
import org.archware.sosadl.validation.typing.proof.Type_bodyprotocol;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_finalprotocol;
import org.archware.sosadl.validation.typing.proof.Type_nonfinalprotocol;
import org.archware.sosadl.validation.typing.proof.Type_protocol;
import org.archware.utils.Pair;
import org.eclipse.emf.common.util.EList;

public abstract class TypeCheckerProtocol extends TypeCheckerBehavior {

	private Type_finalprotocol type_finalprotocol(Environment gamma, EList<ProtocolStatement> b, Protocol behavior,
			int index) {
		if (b.isEmpty()) {
			error("`done' (or any other final statement) is missing to terminate the protocol", behavior,
					SosADLPackage.Literals.BEHAVIOR__STATEMENTS, index - 1);
			return null;
		} else {
			ProtocolStatement first = b.get(0);
			EList<ProtocolStatement> l = cdr(b);
			if (l.isEmpty()) {
				saveEnvironment(first, gamma);
				if (first instanceof DoneProtocol) {
					return saveProof(first,
							p(Type_finalprotocol.class, gamma, (gamma_) -> createType_finalprotocol_Done(gamma_)));
				} else if (first instanceof RepeatProtocol) {
					RepeatProtocol r = (RepeatProtocol) first;
					Protocol rb = r.getRepeated();
					if (rb != null) {
						EList<ProtocolStatement> rbl = rb.getStatements();
						Type_nonfinalprotocol p1 = type_nonfinalprotocol(gamma, rbl, rb, 0);
						return saveProof(first, p(Type_finalprotocol.class, gamma,
								(gamma_) -> createType_finalprotocol_Repeat(gamma_, rbl, p1)));
					} else {
						error("There must be a repeated protocol", first,
								SosADLPackage.Literals.REPEAT_PROTOCOL__REPEATED);
						return null;
					}
				} else if (first instanceof IfThenElseProtocol) {
					IfThenElseProtocol ite = (IfThenElseProtocol) first;
					Expression c = ite.getCondition();
					Protocol t = ite.getIfTrue();
					Protocol e = ite.getIfFalse();
					if (c != null && t != null && e != null) {
						// TODO type_expression
						Pair<Type_expression, DataType> pt = type_expression(gamma, c);
						Type_expression p1 = pt.getA();
						DataType dt = pt.getB();
						if (p1 != null && dt != null) {
							inference.addConstraint(dt, createBooleanType(), c);
							EList<ProtocolStatement> ts = t.getStatements();
							Pair<Environment, Condition_true> gammat = condition_true(gamma, c, t);
							Type_finalprotocol p3 = type_finalprotocol(gammat.getA(), ts, t, 0);
							EList<ProtocolStatement> es = e.getStatements();
							Pair<Environment, Condition_false> gammae = condition_false(gamma, c, e);
							Type_finalprotocol p5 = type_finalprotocol(gammae.getA(), es, e, 0);
							return saveProof(first,
									p(Type_finalprotocol.class, gamma,
											(gamma_) -> p(Type_finalprotocol.class, gammat.getA(),
													(gammat_) -> p(Type_finalprotocol.class, gammae.getA(),
															(gammae_) -> createType_finalprotocol_IfThenElse(gamma_, c,
																	gammat_, ts, gammae_, es, p1, gammat.getB(), p3,
																	gammae.getB(), p5)))));
						} else {
							return null;
						}
					} else {
						if (c == null) {
							error("The `if' protocol must have a condition", first,
									SosADLPackage.Literals.IF_THEN_ELSE_PROTOCOL__CONDITION);
						}
						if (t == null) {
							error("The `if' protocol must have a `then' clause", first,
									SosADLPackage.Literals.IF_THEN_ELSE_PROTOCOL__IF_TRUE);
						}
						if (e == null) {
							error("At tail position, the `if' protocol must have an `else' clause", first,
									SosADLPackage.Literals.IF_THEN_ELSE_PROTOCOL__IF_FALSE);
						}
						return null;
					}
				} else if (first instanceof ChooseProtocol) {
					ChooseProtocol c = (ChooseProtocol) first;
					EList<Protocol> branches = c.getBranches();
					Forall<Protocol, Type_finalprotocol> p1 = proveForall(branches,
							(x) -> type_finalprotocol(gamma, x.getStatements(), x, 0));
					return saveProof(first, p(Type_finalprotocol.class, gamma,
							(gamma_) -> createType_finalprotocol_Choose(gamma_, branches, p1)));
				} else {
					error("Protocol statement `" + labelOf(first) + "' is not allowed at tail position", first, null);
					return null;
				}
			} else {
				Pair<Environment, Type_bodyprotocol> p1 = type_bodyprotocol(gamma, first);
				if (p1 != null && p1.getA() != null && p1.getB() != null) {
					Type_finalprotocol p2 = type_finalprotocol(p1.getA(), l, behavior, index + 1);
					return saveProof(first, p(Type_finalprotocol.class, gamma, (gamma_) -> p(Type_finalprotocol.class,
							p1.getA(),
							(gamma1_) -> createType_finalprotocol_prefix(gamma_, first, gamma1_, l, p1.getB(), p2))));
				} else {
					return null;
				}
			}
		}
	}

	private Type_nonfinalprotocol type_nonfinalprotocol(Environment gamma, EList<ProtocolStatement> b,
			Protocol behavior, int index) {
		if (b.isEmpty()) {
			return p(Type_nonfinalprotocol.class, gamma, (gamma_) -> createType_nonfinalprotocol_empty(gamma_));
		} else {
			ProtocolStatement first = b.get(0);
			EList<ProtocolStatement> l = cdr(b);
			Pair<Environment, Type_bodyprotocol> p1 = type_bodyprotocol(gamma, first);
			if (p1 != null && p1.getA() != null && p1.getB() != null) {
				Type_nonfinalprotocol p2 = type_nonfinalprotocol(p1.getA(), l, behavior, index + 1);
				return saveProof(first, p(Type_nonfinalprotocol.class, gamma, (gamma_) -> p(Type_nonfinalprotocol.class,
						p1.getA(),
						(gamma1_) -> createType_nonfinalprotocol_prefix(gamma_, first, gamma1_, l, p1.getB(), p2))));
			} else {
				return null;
			}
		}
	}

	private Pair<Environment, Type_bodyprotocol> type_bodyprotocol(Environment gamma, ProtocolStatement first) {
		// TODO Auto-generated method stub
		return null;
	}

	protected Type_protocol type_protocol(Environment gamma, ProtocolDecl protocol) {
		saveEnvironment(protocol, gamma);
		String name = protocol.getName();
		Protocol p = protocol.getBody();
		if (name != null && p != null) {
			EList<ProtocolStatement> l = p.getStatements();
			Type_finalprotocol p1 = type_finalprotocol(gamma, l, p, 0);
			return saveProof(protocol,
					p(Type_protocol.class, gamma, (gamma_) -> createType_ProtocolDecl(gamma_, name, l, p1)));
		} else {
			if (name == null) {
				error("The protocol must have a name", protocol, SosADLPackage.Literals.PROTOCOL_DECL__NAME);
			}
			if (p == null) {
				error("The protocol must have a body", protocol, SosADLPackage.Literals.PROTOCOL_DECL__BODY);
			}
			return null;
		}
	}

	protected Type_assertion type_assertion(Environment gamma, AssertionDecl assertion) {
		saveEnvironment(assertion, gamma);
		String name = assertion.getName();
		Protocol p = assertion.getBody();
		if (name != null && p != null) {
			EList<ProtocolStatement> l = p.getStatements();
			Type_finalprotocol p1 = type_finalprotocol(gamma, l, p, 0);
			return saveProof(assertion,
					p(Type_assertion.class, gamma, (gamma_) -> createType_AssertionDecl(gamma_, name, l, p1)));
		} else {
			if (name == null) {
				error("The assertion must have a name", assertion, SosADLPackage.Literals.ASSERTION_DECL__NAME);
			}
			if (p == null) {
				error("The assertion must have a body", assertion, SosADLPackage.Literals.ASSERTION_DECL__BODY);
			}
			return null;
		}
	}

	private String labelOf(ProtocolStatement s) {
		if (s instanceof ValuingProtocol) {
			return "value";
		} else if (s instanceof RepeatProtocol) {
			return "repeat";
		} else if (s instanceof IfThenElseProtocol) {
			return "if";
		} else if (s instanceof ChooseProtocol) {
			return "choose";
		} else if (s instanceof ForEachProtocol) {
			return "foreach";
		} else if (s instanceof DoExprProtocol) {
			return "do";
		} else if (s instanceof DoneProtocol) {
			return "done";
		} else if (s instanceof ProtocolAction) {
			return "via";
		} else {
			return "(unknown statement)";
		}
	}

}