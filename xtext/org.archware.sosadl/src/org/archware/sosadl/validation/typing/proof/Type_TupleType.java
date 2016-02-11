package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.FieldDecl;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_TupleType implements Type_datatype {
	@Mandatory private final Environment gamma;
	
	private final EList<FieldDecl> fields;
	
	@Mandatory private final Mutually<FieldDecl, Ex<DataType, And<Equality, Type_datatype>>> p1;

	public Type_TupleType(Environment gamma, EList<FieldDecl> fields,
			Mutually<FieldDecl, Ex<DataType, And<Equality, Type_datatype>>> p1) {
		super();
		this.gamma = gamma;
		this.fields = fields;
		this.p1 = p1;
	}

	public Environment getGamma() {
		return gamma;
	}

	public EList<FieldDecl> getFields() {
		return fields;
	}

	public Mutually<FieldDecl, Ex<DataType, And<Equality, Type_datatype>>> getP1() {
		return p1;
	}

}
