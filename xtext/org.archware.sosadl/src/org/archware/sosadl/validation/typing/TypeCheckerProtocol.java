package org.archware.sosadl.validation.typing;

import java.util.function.BiFunction;
import java.util.function.Function;

import org.archware.sosadl.sosADL.AssertionDecl;
import org.archware.sosadl.sosADL.ChooseProtocol;
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
import org.archware.sosadl.validation.typing.proof.Type_assertion;
import org.archware.sosadl.validation.typing.proof.Type_bodyprotocol;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_finalprotocol;
import org.archware.sosadl.validation.typing.proof.Type_finalprotocol_other;
import org.archware.sosadl.validation.typing.proof.Type_generic_finalbody;
import org.archware.sosadl.validation.typing.proof.Type_nonfinalprotocol;
import org.archware.sosadl.validation.typing.proof.Type_protocol;
import org.archware.utils.Pair;
import org.eclipse.emf.common.util.EList;

public abstract class TypeCheckerProtocol extends TypeCheckerBehavior {

	private Type_finalprotocol type_finalprotocol(Environment gamma, EList<ProtocolStatement> b, Protocol behavior,
			int index) {
		Function<Protocol, EList<ProtocolStatement>> getBlock = Protocol::getStatements;
		BiFunction<Environment, ProtocolStatement, Type_finalprotocol_other> proveOther = this::final_other;
		BiFunction<Environment, ProtocolStatement, Pair<Environment, Type_bodyprotocol>> gp = this::type_bodyprotocol;
		BiFunction<Environment, Protocol, Type_nonfinalprotocol> gnf = this::type_nonfinalprotocol;
		Function<ChooseProtocol, EList<Protocol>> getBranches = ChooseProtocol::getBranches;
		Function<IfThenElseProtocol, Expression> getCondition = IfThenElseProtocol::getCondition;
		Function<IfThenElseProtocol, Protocol> getThen = IfThenElseProtocol::getIfTrue;
		Function<IfThenElseProtocol, Protocol> getElse = IfThenElseProtocol::getIfFalse;
		Function<RepeatProtocol, Protocol> getRepeated = RepeatProtocol::getRepeated;
		Type_generic_finalbody<Protocol, ProtocolStatement, ChooseProtocol, DoneProtocol, IfThenElseProtocol, RepeatProtocol, Type_finalprotocol_other, Type_expression, Type_bodyprotocol, Type_nonfinalprotocol> p1 = type_generic_finalbody(
				Protocol.class, ProtocolStatement.class, getBlock, "Protocol", ChooseProtocol.class, getBranches,
				DoneProtocol.class, IfThenElseProtocol.class, getCondition,
				SosADLPackage.Literals.IF_THEN_ELSE_PROTOCOL__CONDITION, getThen,
				SosADLPackage.Literals.IF_THEN_ELSE_PROTOCOL__IF_TRUE, getElse,
				SosADLPackage.Literals.IF_THEN_ELSE_PROTOCOL__IF_FALSE, RepeatProtocol.class, getRepeated,
				SosADLPackage.Literals.REPEAT_PROTOCOL__REPEATED, Type_finalprotocol_other.class, proveOther,
				Type_expression.class, this::type_expression, Type_bodyprotocol.class, gp, Type_nonfinalprotocol.class,
				gnf, gamma, b, behavior, SosADLPackage.Literals.PROTOCOL__STATEMENTS, 0);
		Type_finalprotocol proof = p(Type_finalprotocol.class, gamma,
				(gamma_) -> createType_finalprotocol_generic(gamma_, b, p1));
		return saveProof(behavior, proof);
	}

	private Type_finalprotocol_other final_other(Environment gamma, ProtocolStatement s) {
		error("Protocol statement `" + labelOf(s) + "' not allowed at tail position", s, null);
		return null;
	}

	private Type_nonfinalprotocol type_nonfinalprotocol(Environment gamma, Protocol p) {
		return type_nonfinalprotocol(gamma, p.getStatements(), p, 0);
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