package org.archware.sosadl.validation.typing;

import org.archware.sosadl.sosADL.AssertionDecl;
import org.archware.sosadl.sosADL.Protocol;
import org.archware.sosadl.sosADL.ProtocolDecl;
import org.archware.sosadl.sosADL.ProtocolStatement;
import org.archware.sosadl.sosADL.SosADLPackage;
import org.archware.sosadl.validation.typing.proof.Type_assertion;
import org.archware.sosadl.validation.typing.proof.Type_finalprotocol;
import org.archware.sosadl.validation.typing.proof.Type_protocol;
import org.eclipse.emf.common.util.EList;

public abstract class TypeCheckerProtocol extends TypeCheckerExpression {

	private Type_finalprotocol type_finalprotocol(Environment gamma, EList<ProtocolStatement> l) {
		// TODO Auto-generated method stub
		return null;
	}

	protected Type_protocol type_protocol(Environment gamma, ProtocolDecl protocol) {
		saveEnvironment(protocol, gamma);
		String name = protocol.getName();
		Protocol p = protocol.getBody();
		if (name != null && p != null) {
			EList<ProtocolStatement> l = p.getStatements();
			Type_finalprotocol p1 = type_finalprotocol(gamma, l);
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
			Type_finalprotocol p1 = type_finalprotocol(gamma, l);
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

}