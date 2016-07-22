package org.archware.sosadl.validation.typing;

import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.proof.Condition_false;
import org.archware.sosadl.validation.typing.proof.Condition_true;
import org.archware.sosadl.validation.typing.proof.Forall;
import org.archware.sosadl.validation.typing.proof.ProofTerm;
import org.archware.sosadl.validation.typing.proof.Type_generic_finalbody;
import org.archware.sosadl.validation.typing.proof.Type_generic_nonfinalbody;
import org.archware.sosadl.validation.typing.proof.Type_generic_prefixstatement;
import org.archware.utils.Pair;
import org.eclipse.emf.common.util.ECollections;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;

public abstract class TypeCheckerGenericBehavior0 extends TypeCheckerValuing {

	protected <Body extends EObject, Statement extends EObject, Command extends EObject, Action extends EObject, Choose extends EObject, DoExpr extends EObject, ForEach extends EObject, IfThenElse extends EObject, Valuin extends EObject, Send extends EObject, Receive extends EObject, O extends ProofTerm, E extends ProofTerm, NP extends ProofTerm> Pair<Environment, Type_generic_prefixstatement<Body, Statement, Command, Action, Choose, DoExpr, ForEach, IfThenElse, Valuin, Send, Receive, O, E, NP>> type_generic_prefix(
			Class<Body> body, Class<Statement> statement, Class<Command> command, String block, Class<Action> action,
			Class<Choose> choose, Class<DoExpr> doExpr, Class<ForEach> forEach, Class<IfThenElse> ifThenElse,
			Class<Valuin> valuing, Class<Send> send, Class<Receive> receive, Class<O> other,
			BiFunction<Environment, Statement, Pair<Environment, O>> proveOther, Class<E> type_expression,
			Class<NP> type_nonfinalbody, Environment gamma, Statement s) {
		saveEnvironment(s, gamma);
		if (false) {
			return null;
		} else {
			Pair<Environment, O> p1 = proveOther.apply(gamma, s);
			if (p1 != null && p1.getA() != null && p1.getB() != null) {
				Environment gamma1 = p1.getA();
				@SuppressWarnings("unchecked")
				Type_generic_prefixstatement<Body, Statement, Command, Action, Choose, DoExpr, ForEach, IfThenElse, Valuin, Send, Receive, O, E, NP> proof = p(
						Type_generic_prefixstatement.class, gamma,
						(gamma_) -> p(Type_generic_prefixstatement.class, gamma1,
								(gamma1_) -> createType_generic_otherprefix(block, action, choose, doExpr, forEach,
										ifThenElse, valuing, send, receive, other, type_expression, type_nonfinalbody,
										gamma_, s, gamma1_, p1.getB())));
				return new Pair<>(gamma1, saveProof(s, proof));
			} else {
				return null;
			}
		}
	}

}
