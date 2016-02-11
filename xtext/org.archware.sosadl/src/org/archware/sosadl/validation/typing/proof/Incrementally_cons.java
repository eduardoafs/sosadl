package org.archware.sosadl.validation.typing.proof;

import java.util.List;

import org.archware.sosadl.validation.typing.EnvContent;
import org.archware.sosadl.validation.typing.Environment;

public class Incrementally_cons<T,P> implements Incrementally<T,P> {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final T x;
	
	private final String n;
	
	private final EnvContent c;
	
	@Mandatory private final Environment gammai;
	
	private final List<T> l;
	
	@Mandatory private final Environment gamma1;
	
	@Mandatory private final P p1;
	
	@Mandatory private final Equality p2;

	@Mandatory private final Equality p3;

	@Mandatory private final Equality p4;

	@Mandatory private final Incrementally<T,P> p5;

	public Incrementally_cons(Environment gamma, T x, String n, EnvContent c, Environment gammai, List<T> l,
			Environment gamma1, P p1, Equality p2, Equality p3, Equality p4, Incrementally<T, P> p5) {
		super();
		this.gamma = gamma;
		this.x = x;
		this.n = n;
		this.c = c;
		this.gammai = gammai;
		this.l = l;
		this.gamma1 = gamma1;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
		this.p4 = p4;
		this.p5 = p5;
	}

	public Environment getGamma() {
		return gamma;
	}

	public T getX() {
		return x;
	}

	public String getN() {
		return n;
	}

	public EnvContent getC() {
		return c;
	}

	public Environment getGammai() {
		return gammai;
	}

	public List<T> getL() {
		return l;
	}

	public Environment getGamma1() {
		return gamma1;
	}

	public P getP1() {
		return p1;
	}

	public Equality getP2() {
		return p2;
	}

	public Equality getP3() {
		return p3;
	}

	public Equality getP4() {
		return p4;
	}

	public Incrementally<T, P> getP5() {
		return p5;
	}

}
