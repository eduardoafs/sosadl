package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.Environment;

public class Type_RangeType_trivial implements Type_datatype {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final Expression min;
	
	@Mandatory private final Expression max;
	
	@Mandatory private final Constexpr_expression p1;

	@Mandatory private final Constexpr_expression p2;
	
	@Mandatory private final Expression_le p3;

	public Type_RangeType_trivial(Environment gamma, Expression min, Expression max, Constexpr_expression p1,
			Constexpr_expression p2, Expression_le p3) {
		super();
		this.gamma = gamma;
		this.min = min;
		this.max = max;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
	}

	public Environment getGamma() {
		return gamma;
	}

	public Expression getMin() {
		return min;
	}

	public Expression getMax() {
		return max;
	}

	public Constexpr_expression getP1() {
		return p1;
	}

	public Constexpr_expression getP2() {
		return p2;
	}

	public Expression_le getP3() {
		return p3;
	}

}
