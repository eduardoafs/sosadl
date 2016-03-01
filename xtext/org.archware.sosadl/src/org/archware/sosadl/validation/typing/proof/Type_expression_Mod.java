package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.Environment;

public class Type_expression_Mod implements Type_expression_node {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final Expression l;
	
	@Mandatory private final DataType l__tau;
	
	@Mandatory private final Expression l__min;
	
	@Mandatory private final Expression l__max;
	
	@Mandatory private final Expression r;
	
	@Mandatory private final DataType r__tau;
	
	@Mandatory private final Expression r__min;
	
	@Mandatory private final Expression r__max;
	
	@Mandatory private final Expression min;

	@Mandatory private final Expression max;
	
	@Mandatory private final Type_expression p1;
	
	@Mandatory private final Subtype p2;
	
	@Mandatory private final Type_expression p3;
	
	@Mandatory private final Subtype p4;

	@Mandatory private final Range_modulo_min p5;
	
	@Mandatory private final Range_modulo_max p6;

	public Type_expression_Mod(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Expression min, Expression max,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4, Range_modulo_min p5, Range_modulo_max p6) {
		super();
		this.gamma = gamma;
		this.l = l;
		this.l__tau = l__tau;
		this.l__min = l__min;
		this.l__max = l__max;
		this.r = r;
		this.r__tau = r__tau;
		this.r__min = r__min;
		this.r__max = r__max;
		this.min = min;
		this.max = max;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
		this.p4 = p4;
		this.p5 = p5;
		this.p6 = p6;
	}

	public Environment getGamma() {
		return gamma;
	}

	public Expression getL() {
		return l;
	}

	public DataType getL__tau() {
		return l__tau;
	}

	public Expression getL__min() {
		return l__min;
	}

	public Expression getL__max() {
		return l__max;
	}

	public Expression getR() {
		return r;
	}

	public DataType getR__tau() {
		return r__tau;
	}

	public Expression getR__min() {
		return r__min;
	}

	public Expression getR__max() {
		return r__max;
	}

	public Expression getMin() {
		return min;
	}

	public Expression getMax() {
		return max;
	}

	public Type_expression getP1() {
		return p1;
	}

	public Subtype getP2() {
		return p2;
	}

	public Type_expression getP3() {
		return p3;
	}

	public Subtype getP4() {
		return p4;
	}

	public Range_modulo_min getP5() {
		return p5;
	}

	public Range_modulo_max getP6() {
		return p6;
	}

}
