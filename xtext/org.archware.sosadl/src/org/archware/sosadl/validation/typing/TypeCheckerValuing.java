package org.archware.sosadl.validation.typing;

import java.util.Optional;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.SosADLPackage;
import org.archware.sosadl.sosADL.Valuing;
import org.archware.sosadl.validation.typing.impl.VariableEnvContent;
import org.archware.sosadl.validation.typing.proof.Incrementally;
import org.archware.sosadl.validation.typing.proof.Subtype;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_valuing;
import org.archware.utils.Pair;
import org.eclipse.emf.common.util.EList;

public abstract class TypeCheckerValuing extends TypeCheckerCondition {

	public TypeCheckerValuing() {
		super();
	}

	protected Pair<Type_valuing, Environment> type_valuing(Environment gamma, Valuing v) {
		Expression e = v.getExpression();
		String x = v.getName();
		if (e != null && x != null) {
			Pair<Type_expression, DataType> pt1 = type_expression(gamma, e);
			Type_expression p1 = pt1.getA();
			DataType tau__e = pt1.getB();
			if (p1 != null && tau__e != null) {
				DataType tau = v.getType();
				if (tau != null) {
					return new Pair<>(saveProof(v, p(Type_valuing.class, gamma, (gamma_) -> p(Type_valuing.class, tau,
							(tau_) -> p(Type_valuing.class, tau__e, (tau__e_) -> {
								Optional<Subtype> st = subtype(tau__e_, tau_, v,
										SosADLPackage.Literals.VALUING__EXPRESSION);
								return createType_Valuing_typed(gamma_, x, tau_, e, tau__e_, p1, st.orElse(null));
							})))), gamma.put(x, new VariableEnvContent(v, tau)));
				} else {
					return new Pair<>(
							saveProof(v,
									p(Type_valuing.class, gamma,
											(gamma_) -> p(Type_valuing.class,
													tau__e, (tau__e_) -> createType_Valuing_inferred(gamma_, x, e,
															tau__e_, p1)))),
							gamma.put(x, new VariableEnvContent(v, tau__e)));
				}
			} else {
				return new Pair<>(null, gamma);
			}
		} else {
			if (v.getExpression() == null) {
				error("The valuing must contain an expression", v, SosADLPackage.Literals.VALUING__EXPRESSION);
			}
			if (v.getName() == null) {
				error("The valuing must contain a variable name", v, SosADLPackage.Literals.VALUING__NAME);
			}
			return new Pair<>(null, gamma);
		}
	}

	protected Pair<Incrementally<Valuing, Type_valuing>, Environment> type_valuings(Environment gamma,
			EList<Valuing> l) {
		return proveIncrementally(gamma, l, this::type_valuing);
	}

}