package org.archware.sosadl.validation.typing;

import java.util.Collection;
import java.util.Optional;
import java.util.concurrent.ConcurrentLinkedDeque;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Stream;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.FieldDecl;
import org.archware.sosadl.sosADL.SosADL;
import org.archware.sosadl.tv.typeCheckerHelper.TypeVariable;
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

	protected <T extends ProofTerm> T proofTerm(DataType x, Class<T> itf, Function<DataType, T> factory) {
		return proofTerm(itf, () -> {
			DataType t = getSubstitute(x);
			return factory.apply(t);
		}, x);
	}

	protected <T extends ProofTerm> T proofTerm(Class<T> itf, Supplier<T> factory, DataType... x) {
		if(Stream.of(x).anyMatch(TypeInferenceSolver::containsVariable)) {
			ProofTermPlaceHolder<T> ptph = ProofTermPlaceHolder.create(itf);
			delayedTasks.add(() -> {
				ptph.fillWith(factory.get());
			});
			return ptph.cast();
		} else {
			return factory.get();
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