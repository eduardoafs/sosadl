package org.archware.sosadl.validation.typing;

import java.util.Collection;
import java.util.Optional;
import java.util.concurrent.ConcurrentLinkedDeque;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Stream;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.FieldDecl;
import org.archware.sosadl.sosADL.SosADL;
import org.archware.sosadl.tv.typeCheckerHelper.TypeVariable;
import org.archware.sosadl.validation.typing.impl.VariableEnvContent;
import org.archware.sosadl.validation.typing.proof.ProofTerm;
import org.archware.sosadl.validation.typing.proof.ProofTermPlaceHolder;
import org.archware.sosadl.validation.typing.proof.Type_sosADL;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;

public abstract class TypeCheckerInference extends TypeCheckerUtils {

	protected TypeInferenceSolver inference = new TypeInferenceSolver(this);
	private Collection<Runnable> delayedTasks = new ConcurrentLinkedDeque<>();

	/**
	 * Performs the whole type-checking of a SoSADL specification.
	 * 
	 * @param file the SoSADL model.
	 */
	public void typecheck(SosADL file) {
		try {
			type_sosADL(file);
			solveConstraints();
		} catch(Throwable t) {
			t.printStackTrace();
			error("Bug in the type checker", file, null);
			throw t;
		}
	}

	protected abstract Type_sosADL type_sosADL(SosADL file);

	/**
	 * Solves the constraints for all the accumulated type variables.
	 * 
	 * <p>
	 * This method calls the type inference solver.
	 * If successful, it then invokes the delayed task recorded for each type variable.
	 */
	protected void solveConstraints() {
		inference.solve();
		if(inference.isSolved()) {
			delayedTasks.forEach((t) -> t.run());
		}
	}

	protected TypeVariable createFreshTypeVariable(EObject co, EStructuralFeature csf, BinaryOperator<Optional<DataType>> solver) {
		return inference.createFreshTypeVariable(solver, co, csf);
	}
	
	private Stream<DataType> streamEnvironmentTypes(Environment gamma) {
		return gamma.stream().filter((x) -> x instanceof VariableEnvContent).map((x) -> (VariableEnvContent)x)
				.map(VariableEnvContent::getType);
	}
	
	protected Environment getSubstitute(Environment gamma) {
		return gamma.deepClone(this::getSubstitute);
	}
	
	private EnvContent getSubstitute(EnvContent c) {
		if(c instanceof VariableEnvContent) {
			return new VariableEnvContent(((VariableEnvContent) c).getBinder(), getSubstitute(((VariableEnvContent) c).getType()));
		} else {
			return c;
		}
	}

	protected <T extends ProofTerm> T proofTerm(Environment gamma, DataType x, Class<T> itf, BiFunction<Environment, DataType, T> factory) {
		return proofTerm(gamma, itf, (g) -> {
			DataType t = getSubstitute(x);
			return factory.apply(g, t);
		}, x);
	}

	protected <T extends ProofTerm> T proofTerm(Environment gamma, Class<T> itf, Function<Environment, T> factory, DataType... x) {
		return proofTerm(gamma, itf, factory, Stream.of(x));
	}

	protected <T extends ProofTerm> T proofTerm(Environment gamma, Class<T> itf, Function<Environment, T> factory, Stream<DataType> x) {
		boolean xv = x.anyMatch(TypeInferenceSolver::containsVariable);
		boolean gv = streamEnvironmentTypes(gamma).anyMatch(TypeInferenceSolver::containsVariable);
		if(xv || gv) {
			ProofTermPlaceHolder<T> ptph = ProofTermPlaceHolder.create(itf);
			delayedTasks.add(() -> {
				ptph.fillWith(factory.apply(getSubstitute(gamma)));
			});
			return ptph.cast();
		} else {
			return factory.apply(gamma);
		}
	}

	protected DataType getSubstitute(DataType t) {
		return inference.deepSubstitute(t);
	}

	protected FieldDecl getSubstitute(FieldDecl f) {
		return createFieldDecl(f.getName(), getSubstitute(f.getType()));
	}

	protected DataType deepSubstitute(DataType t) {
		return getSubstitute(t);
	}

	protected FieldDecl deepSubstitute(FieldDecl f) {
		return getSubstitute(f);
	}

}