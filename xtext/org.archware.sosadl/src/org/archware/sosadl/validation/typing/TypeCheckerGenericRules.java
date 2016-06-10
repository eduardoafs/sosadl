package org.archware.sosadl.validation.typing;

import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

import org.archware.sosadl.validation.typing.proof.Forall;
import org.archware.sosadl.validation.typing.proof.Forall2;
import org.archware.sosadl.validation.typing.proof.Incrementally;
import org.archware.sosadl.validation.typing.proof.Mutually;
import org.archware.sosadl.validation.typing.proof.Optionally;
import org.archware.sosadl.validation.typing.proof.ProofTerm;
import org.archware.sosadl.validation.typing.proof.Simple_increment;
import org.archware.utils.Pair;
import org.archware.utils.TriFunction;
import org.eclipse.emf.ecore.EObject;

public abstract class TypeCheckerGenericRules extends TypeCheckerInference {

	protected static <S, T extends EObject, P extends ProofTerm> Forall<T, P> proveForall(List<S> l, Function<S,T> f,
			Function<S,P> prover) {
				if(l.isEmpty()) {
					return createForall_nil();
				} else {
					return createForall_cons(f.apply(l.get(0)), prover.apply(l.get(0)), proveForall(cdr(l), f, prover));
				}
			}

	protected static <T extends EObject, P extends ProofTerm> Forall<T, P> proveForall(List<T> l, Function<T,P> prover) {
		return proveForall(l, (x) -> x, prover);
	}

	protected static <T1 extends EObject, T2 extends EObject, P extends ProofTerm> Forall2<T1,T2,P> proveForall2(List<? extends T1> l,
			List<? extends T2> m, BiFunction<T1, T2, ? extends P> prover) {
				if(l.isEmpty() && m.isEmpty()) {
					return createForall2_nil();
				} else {
					return createForall2_cons(l.get(0), m.get(0), prover.apply(l.get(0), m.get(0)), proveForall2(cdr(l), cdr(m), prover));
				}
			}

	protected static <T, T1 extends EObject, T2 extends EObject, P extends ProofTerm> Forall2<T1,T2,P> proveForall2(List<T> zipped,
			Function<T, T1> left, Function<T, T2> right, Function<T, P> prover) {
				if(zipped.isEmpty()) {
					return createForall2_nil();
				} else {
					return createForall2_cons(left.apply(zipped.get(0)),
							right.apply(zipped.get(0)),
							prover.apply(zipped.get(0)),
							proveForall2(cdr(zipped), left, right, prover));
				}
			}

	protected static <T extends EObject, P extends ProofTerm> Pair<Incrementally<T,P>,Environment> proveIncrementally(Environment gamma, List<T> l,
			BiFunction<Environment, T, Pair<P, Environment>> prover) {
				if(l.isEmpty()) {
					return new Pair<>(createIncrementally_nil(gamma), gamma);
				} else {
					Pair<P, Environment> pi = prover.apply(gamma,  l.get(0));
					Environment gammai = pi.getB();
					Pair<Incrementally<T, P>, Environment> pn = proveIncrementally(gammai, cdr(l), prover);
					Environment gamma1 = pn.getB();
					return new Pair<>(createIncrementally_cons(gamma, l.get(0), gammai, cdr(l), gamma1, pi.getA(), pn.getA()), gamma1);
				}
			}

	protected static <T extends EObject, P extends ProofTerm> Pair<Simple_increment<T,P>,Environment> proveSimpleIncrement(Environment gamma, T x,
			BiFunction<Environment, T, P> prover, String n, Function<T, ? extends String> name, String c, Function<T, ? extends EnvContent> content) {
				Environment gamma1 = augment_env(gamma, name.apply(x), content.apply(x));
				return new Pair<>(createSimple_increment_step(n, c, gamma, x, gamma1, createReflexivity(), prover.apply(gamma, x)), gamma1);
			}

	private static Environment augment_env(Environment gamma, String name, EnvContent content) {
		if(name == null) {
			return gamma;
		} else if(content == null) {
			return gamma;
		} else {
			return gamma.put(name, content);
		}
	}

	protected <T extends EObject, P extends ProofTerm> Pair<Mutually<T,P>, Environment> proveMutually(Environment gamma, List<T> l, TriFunction<Environment, T, Environment, P> prover,
			String n, Function<T, ? extends String> name, String c, Function<T, ? extends EnvContent> content) {
				if(noDuplicate(l.stream().map(name))) {
					Environment gamma1 = fold_right((x, g) -> augment_env(g, name.apply(x), content.apply(x)), gamma, l);
					return new Pair<>(createMutually_all_explicit(n, c, gamma, l, gamma1, createReflexivity(), createReflexivity(), proveForall(l, (x) -> prover.apply(gamma,  x,  gamma1))), gamma1);
				} else {
					l.stream().filter((p) -> l.stream().map(name).filter((x) -> x.equals(name.apply(p))).count() >= 2)
					.forEach((f) -> error("Multiple definitions of `" + name.apply(f) + "'", f, null));
					return new Pair<>(null, gamma);
				}
			}

	protected <T extends EObject, P extends ProofTerm> Optionally<T, P> proveOptionally(Environment gamma, T x, BiFunction<Environment,T,P> prover) {
		if(x == null) {
			return createOptionally_None(gamma);
		} else {
			return createOptionally_Some(gamma, x, prover.apply(gamma, x));
		}
	}

	public TypeCheckerGenericRules() {
		super();
	}

}