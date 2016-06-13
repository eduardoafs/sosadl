package org.archware.sosadl.validation.typing;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ConcurrentLinkedDeque;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.function.BiFunction;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.FieldDecl;
import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.sosADL.IdentExpression;
import org.archware.sosadl.sosADL.IntegerValue;
import org.archware.sosadl.sosADL.Map;
import org.archware.sosadl.sosADL.MethodCall;
import org.archware.sosadl.sosADL.RangeType;
import org.archware.sosadl.sosADL.Sequence;
import org.archware.sosadl.sosADL.SequenceType;
import org.archware.sosadl.sosADL.SosADLPackage;
import org.archware.sosadl.sosADL.Tuple;
import org.archware.sosadl.sosADL.TupleElement;
import org.archware.sosadl.sosADL.TupleType;
import org.archware.sosadl.sosADL.UnaryExpression;
import org.archware.sosadl.tv.typeCheckerHelper.TypeVariable;
import org.archware.sosadl.validation.typing.impl.TypeEnvContent;
import org.archware.sosadl.validation.typing.impl.VariableEnvContent;
import org.archware.sosadl.validation.typing.proof.And;
import org.archware.sosadl.validation.typing.proof.Equality;
import org.archware.sosadl.validation.typing.proof.Ex;
import org.archware.sosadl.validation.typing.proof.Forall;
import org.archware.sosadl.validation.typing.proof.Forall2;
import org.archware.sosadl.validation.typing.proof.Range_modulo_max;
import org.archware.sosadl.validation.typing.proof.Range_modulo_min;
import org.archware.sosadl.validation.typing.proof.Subtype;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_expression_node;
import org.archware.utils.DecaFunction;
import org.archware.utils.IntPair;
import org.archware.utils.ListUtils;
import org.archware.utils.OptionalUtils;
import org.archware.utils.Pair;
import org.archware.utils.PentaFunction;
import org.archware.utils.StreamUtils;
import org.archware.utils.TreDecaFunction;
import org.archware.utils.TriFunction;
import org.eclipse.emf.common.util.ECollections;
import org.eclipse.xtext.xbase.lib.ListExtensions;

public abstract class TypeCheckerExpression extends TypeCheckerDataType {

	protected abstract class AbstractUnaryTypeInfo<P extends Type_expression_node> extends StringBasedUnaryTypeInfo<P> {
			private final PentaFunction<Environment, Expression, DataType, Type_expression, Subtype, P> prover;
				
			public AbstractUnaryTypeInfo(String operator, PentaFunction<Environment, Expression, DataType, Type_expression, Subtype, P> prover) {
				super(operator);
				this.prover = prover;
			}
	
			@Override
			public Type_expression_node prove(Environment gamma, UnaryExpression e, Type_expression pOperand, DataType tOperand) {
				return p(Type_expression_node.class, gamma,
						(gamma_) -> p(Type_expression_node.class, tOperand,
								(tOperand_) -> prover.apply(gamma_, e.getRight(), tOperand_, pOperand,
										createSubtype_refl(tOperand_))));
			}
		}

	private <T> T range_modulo_min(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Supplier<T> pos, Supplier<T> zero,
			Supplier<T> neg, Supplier<T> divByZero) {
				if(isLe(createIntegerValue(1), rmin)) {
					if(isLe(createIntegerValue(0), lmin)) {
						return zero.get();
					} else {
						return pos.get();
					}
				} else if(isLe(rmax, createOpposite(createIntegerValue(1)))) {
					if(isLe(createIntegerValue(0), lmin)) {
						return zero.get();
					} else {
						return neg.get();
					}
				} else {
					return divByZero.get();
				}
			}

	private <T> T range_modulo_max(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Supplier<T> pos, Supplier<T> zero,
			Supplier<T> neg, Supplier<T> divByZero) {
				if(isLe(createIntegerValue(1), rmin)) {
					if(isLe(lmax, createIntegerValue(0))) {
						return zero.get();
					} else {
						return pos.get();
					}
				} else if(isLe(rmax, createOpposite(createIntegerValue(1)))) {
					if(isLe(lmax, createIntegerValue(0))) {
						return zero.get();
					} else {
						return neg.get();
					}
				} else {
					return divByZero.get();
				}
			}

	private final UnaryTypeInfo2<?> unop2Same = new SynthetizingUnaryTypeInfo<>("+",
				(g,e,t,p,s) -> createType_expression_Same(g, e, t, ((RangeType)t).getVmin(), ((RangeType)t).getVmax(), p, s),
				(e, t) -> Optional.ofNullable(t).flatMap((x) -> toRangeType(e, t)).map((x) -> (DataType) x));

	private Optional<RangeType> toRangeType(UnaryExpression e, DataType t) {
		if(t instanceof RangeType) {
			return Optional.of((RangeType)t);
		} else {
			error("The operand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(t), e, SosADLPackage.Literals.UNARY_EXPRESSION__RIGHT);
			return Optional.empty();
		}
	}

	private final UnaryTypeInfo2<?> unop2Opposite = new SynthetizingUnaryTypeInfo<>("-",
				(g,e,t,p,s) -> createType_expression_Opposite(g, e, t, ((RangeType)t).getVmin(), ((RangeType)t).getVmax(), p, s),
				(e, t) -> Optional.ofNullable(t)
				.flatMap((x) -> toRangeType(e, x))
				.map((x) -> createRangeType(createOpposite(x.getVmax()),
						createOpposite(x.getVmin()))));
	private final UnaryTypeInfo2<?> unop2Not = new BooleanUnaryTypeInfo<>("not",
				this::createType_expression_Not);
	private final UnaryTypeInfo2<?>[] unaryTypeInformations2 = new UnaryTypeInfo2[] {
				unop2Same,
				unop2Opposite,
				unop2Not
		};

	protected abstract class AbstractBinaryTypeInfo<P extends Type_expression_node> extends StringBasedBinaryTypeInfo<P> {
			private final DecaFunction<Environment,
			Expression, DataType, Type_expression, Subtype,
			Expression, DataType, Type_expression, Subtype,
			DataType, P> prover;
				
			public AbstractBinaryTypeInfo(String operator, DecaFunction<Environment, Expression, DataType, Type_expression, Subtype, Expression, DataType, Type_expression, Subtype, DataType, P> prover) {
				super(operator);
				this.prover = prover;
			}
	
			@Override
			public Type_expression_node prove(Environment gamma, BinaryExpression e, Type_expression pLeft, DataType tLeft, Type_expression pRight, DataType tRight, DataType r) {
				return p(Type_expression_node.class, gamma,
						(gamma_) -> p(Type_expression_node.class, tLeft,
								(tLeft_) -> p(Type_expression_node.class, tRight,
										(tRight_) -> p(Type_expression_node.class, r,
												(r_) -> prover.apply(gamma_, e.getLeft(), tLeft_, pLeft, createSubtype_refl(tLeft_),
														e.getRight(), tRight_, pRight, createSubtype_refl(tRight_), r_)))));
			}
		}

	private final BinaryTypeInfo2<?> binop2Add = new SynthetizingBinaryTypeInfo<>("+",
					(g, le, lt, lp, ls, re, rt, rp, rs, r) ->
						createType_expression_Add(g, le, lt, ((RangeType)lt).getVmin(), ((RangeType)lt).getVmax(),
								re, rt, ((RangeType)rt).getVmin(), ((RangeType)rt).getVmax(),
								lp, ls, rp, rs),
					this::binopSolverAdd);

	private Optional<DataType> binopSolverAdd(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				return Optional.of(createRangeType(
						createBinaryExpression(((RangeType)l).getVmin(), "+", ((RangeType)r).getVmin()),
						createBinaryExpression(((RangeType)l).getVmax(), "+", ((RangeType)r).getVmax())));
			} else {
				error("The right-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(r), e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
				return Optional.empty();
			}
		} else {
			error("The left-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(l), e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			return Optional.empty();
		}
	}

	private final BinaryTypeInfo2<?> binop2Sub = new SynthetizingBinaryTypeInfo<>("-",
				(g, le, lt, lp, ls, re, rt, rp, rs, r) ->
					createType_expression_Sub(g, le, lt, ((RangeType)lt).getVmin(), ((RangeType)lt).getVmax(),
							re, rt, ((RangeType)rt).getVmin(), ((RangeType)rt).getVmax(),
							lp, ls, rp, rs),
				this::binopSolverSub);

	private Optional<DataType> binopSolverSub(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				return Optional.of(createRangeType(
						createBinaryExpression(((RangeType)l).getVmin(), "-", ((RangeType)r).getVmax()),
						createBinaryExpression(((RangeType)l).getVmax(), "-", ((RangeType)r).getVmin())));
			} else {
				error("The right-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(r), e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
				return Optional.empty();
			}
		} else {
			error("The left-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(l), e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			return Optional.empty();
		}
	}

	private final BinaryTypeInfo2<?> binop2Mul = new SynthetizingBinaryTypeInfo<>("*",
				this::binopProverMul,
				this::binopSolverMul);

	private Type_expression_node binopProverMul(Environment g, Expression le, DataType ldt, Type_expression lp, Subtype ls, Expression re,
			DataType rdt, Type_expression rp, Subtype rs, DataType rd) {
				RangeType lt = (RangeType) ldt;
				RangeType rt = (RangeType) rdt;
				RangeType r = (RangeType) rd;
				Expression c1 = createBinaryExpression(lt.getVmin(), "*", rt.getVmin());
				Expression c2 = createBinaryExpression(lt.getVmin(), "*", rt.getVmax());
				Expression c3 = createBinaryExpression(lt.getVmax(), "*", rt.getVmin());
				Expression c4 = createBinaryExpression(lt.getVmax(), "*", rt.getVmax());
				return createType_expression_Mul(g,
						le, lt, lt.getVmin(), lt.getVmax(),
						re, rt, rt.getVmin(), rt.getVmax(),
						r.getVmin(), r.getVmax(), lp, ls, rp, rs,
						expression_le(r.getVmin(), c1),
						expression_le(r.getVmin(), c2),
						expression_le(r.getVmin(), c3),
						expression_le(r.getVmin(), c4),
						expression_le(c1, r.getVmax()),
						expression_le(c2, r.getVmax()),
						expression_le(c3, r.getVmax()),
						expression_le(c4, r.getVmax()));
			}

	private Optional<DataType> binopSolverMul(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				RangeType lt = (RangeType) l;
				RangeType rt = (RangeType) r;
				Expression c1 = createBinaryExpression(lt.getVmin(), "*", rt.getVmin());
				Expression c2 = createBinaryExpression(lt.getVmin(), "*", rt.getVmax());
				Expression c3 = createBinaryExpression(lt.getVmax(), "*", rt.getVmin());
				Expression c4 = createBinaryExpression(lt.getVmax(), "*", rt.getVmax());
				Expression mi = min(min(c1, c2), min(c3, c4));
				Expression ma = max(max(c1, c2), max(c3, c4));
				return Optional.of(createRangeType(mi, ma));
			} else {
				error("The right-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(r), e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
				return Optional.empty();
			}
		} else {
			error("The left-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(l), e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			return Optional.empty();
		}
	}

	private final BinaryTypeInfo2<?> binop2Div = new SynthetizingBinaryTypeInfo<>("/",
				this::binopProverDiv,
				this::binopSolverDiv);

	private Type_expression_node binopProverDiv(Environment g, Expression le, DataType dlt, Type_expression lp, Subtype ls, Expression re,
			DataType drt, Type_expression rp, Subtype rs, DataType dr) {
				RangeType lt = (RangeType) dlt;
				RangeType rt = (RangeType) drt;
				RangeType r = (RangeType) dr;
				if(isLe(createIntegerValue(1), rt.getVmin())) {
					Expression c1 = createBinaryExpression(lt.getVmin(), "/", rt.getVmin());
					Expression c2 = createBinaryExpression(lt.getVmin(), "/", rt.getVmax());
					Expression c3 = createBinaryExpression(lt.getVmax(), "/", rt.getVmin());
					Expression c4 = createBinaryExpression(lt.getVmax(), "/", rt.getVmax());
					return createType_expression_Div_pos(g,
							le, lt, lt.getVmin(), lt.getVmax(),
							re, rt, rt.getVmin(), rt.getVmax(),
							r.getVmin(), r.getVmax(), lp, ls, rp, rs,
							expression_le(createIntegerValue(1), rt.getVmin()),
							expression_le(r.getVmin(), c1),
							expression_le(r.getVmin(), c2),
							expression_le(r.getVmin(), c3),
							expression_le(r.getVmin(), c4),
							expression_le(c1, r.getVmax()),
							expression_le(c2, r.getVmax()),
							expression_le(c3, r.getVmax()),
							expression_le(c4, r.getVmax()));
				} else if (isLe(rt.getVmax(), createOpposite(createIntegerValue(1)))) {
					Expression c1 = createBinaryExpression(lt.getVmin(), "/", rt.getVmin());
					Expression c2 = createBinaryExpression(lt.getVmin(), "/", rt.getVmax());
					Expression c3 = createBinaryExpression(lt.getVmax(), "/", rt.getVmin());
					Expression c4 = createBinaryExpression(lt.getVmax(), "/", rt.getVmax());
					return createType_expression_Div_neg(g,
							le, lt, lt.getVmin(), lt.getVmax(),
							re, rt, rt.getVmin(), rt.getVmax(),
							r.getVmin(), r.getVmax(), lp, ls, rp, rs,
							expression_le(rt.getVmax(), createOpposite(createIntegerValue(1))),
							expression_le(r.getVmin(), c1),
							expression_le(r.getVmin(), c2),
							expression_le(r.getVmin(), c3),
							expression_le(r.getVmin(), c4),
							expression_le(c1, r.getVmax()),
							expression_le(c2, r.getVmax()),
							expression_le(c3, r.getVmax()),
							expression_le(c4, r.getVmax()));
				} else {
					error("The divisor must be different from 0", re, null);
					return null;
				}
			}

	private Optional<DataType> binopSolverDiv(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				RangeType lt = (RangeType) l;
				RangeType rt = (RangeType) r;
				if(isLe(createIntegerValue(1), rt.getVmin()) || isLe(rt.getVmax(), createOpposite(createIntegerValue(1)))) {
					Expression c1 = createBinaryExpression(lt.getVmin(), "/", rt.getVmin());
					Expression c2 = createBinaryExpression(lt.getVmin(), "/", rt.getVmax());
					Expression c3 = createBinaryExpression(lt.getVmax(), "/", rt.getVmin());
					Expression c4 = createBinaryExpression(lt.getVmax(), "/", rt.getVmax());
					Expression mi = min(min(c1, c2), min(c3, c4));
					Expression ma = max(max(c1, c2), max(c3, c4));
					return Optional.of(createRangeType(mi, ma));
				} else {
					//error("The divisor must be different from 0", e.getRight(), null);
					return Optional.empty();
				}
			} else {
				error("The right-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(r), e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
				return Optional.empty();
			}
		} else {
			error("The left-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(l), e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			return Optional.empty();
		}
	}

	private final BinaryTypeInfo2<?> binop2Mod = new SynthetizingBinaryTypeInfo<>("mod",
				this::binopProverMod,
				this::binopSolverMod);

	private Type_expression_node binopProverMod(Environment g, Expression le, DataType dlt, Type_expression lp, Subtype ls, Expression re,
			DataType drt, Type_expression rp, Subtype rs, DataType dr) {
				RangeType lt = (RangeType) dlt;
				RangeType rt = (RangeType) drt;
				RangeType r = (RangeType) dr;
				Range_modulo_min min = range_modulo_min(
						lt.getVmin(), lt.getVmax(),
						rt.getVmin(), rt.getVmax(),
						() -> createRange_modulo_min_pos(lt.getVmin(), lt.getVmax(),
								rt.getVmin(), rt.getVmax(),
								r.getVmin(),
								expression_le(createIntegerValue(1), rt.getVmin()),
								expression_le(r.getVmin(), createBinaryExpression(createIntegerValue(1), "-", rt.getVmax()))),
						() -> createRange_modulo_min_zero(lt.getVmin(), lt.getVmax(),
								rt.getVmin(), rt.getVmax(),
								r.getVmin(),
								expression_le(createIntegerValue(0), lt.getVmin()),
								expression_le(r.getVmin(), createIntegerValue(0))),
						() -> createRange_modulo_min_neg(lt.getVmin(), lt.getVmax(),
								rt.getVmin(), rt.getVmax(),
								r.getVmin(),
								expression_le(rt.getVmax(), createOpposite(createIntegerValue(1))),
								expression_le(r.getVmin(), createBinaryExpression(rt.getVmin(), "+", createIntegerValue(1)))),
						() -> { error("The divisor must be different from 0", re, null); return null; });
				if(min != null) {
					Range_modulo_max max = range_modulo_max(
							lt.getVmin(), lt.getVmax(),
							rt.getVmin(), rt.getVmax(),
							() -> createRange_modulo_max_pos(lt.getVmin(), lt.getVmax(),
									rt.getVmin(), rt.getVmax(),
									r.getVmax(),
									expression_le(createIntegerValue(1), rt.getVmin()),
									expression_le(createBinaryExpression(rt.getVmax(), "-", createIntegerValue(1)), r.getVmax())),
							() -> createRange_modulo_max_zero(lt.getVmin(), lt.getVmax(),
									rt.getVmin(), rt.getVmax(),
									r.getVmax(),
									expression_le(lt.getVmax(), createIntegerValue(0)),
									expression_le(createIntegerValue(0), r.getVmax())),
							() -> createRange_modulo_max_neg(lt.getVmin(), lt.getVmax(),
									rt.getVmin(), rt.getVmax(),
									r.getVmax(),
									expression_le(rt.getVmax(), createOpposite(createIntegerValue(1))),
									expression_le(createBinaryExpression(createOpposite(createIntegerValue(1)), "-", rt.getVmin()), r.getVmax())),
							() -> { error("The divisor must be different from 0", re, null); return null; });
					if(max != null) {
						return createType_expression_Mod(g,
								le, lt, lt.getVmin(), lt.getVmax(),
								re, rt, rt.getVmin(), rt.getVmax(),
								r.getVmin(), r.getVmax(),
								lp, ls, rp, rs, min, max);
					} else {
						return null;
					}
				} else {
					return null;
				}
			}

	private Optional<DataType> binopSolverMod(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				RangeType lt = (RangeType) l;
				RangeType rt = (RangeType) r;
				Expression min = range_modulo_min(
						lt.getVmin(), lt.getVmax(),
						rt.getVmin(), rt.getVmax(),
						() -> createBinaryExpression(createIntegerValue(1), "-", rt.getVmax()),
						() -> createIntegerValue(0),
						() -> createBinaryExpression(rt.getVmin(), "+", createIntegerValue(1)),
						() -> { error("The divisor must be different from 0", e.getRight(), null); return null; });
				if(min != null) {
					Expression max = range_modulo_max(
							lt.getVmin(), lt.getVmax(),
							rt.getVmin(), rt.getVmax(),
							() -> createBinaryExpression(rt.getVmax(), "-", createIntegerValue(1)),
							() -> createIntegerValue(0),
							() -> createBinaryExpression(createOpposite(createIntegerValue(1)), "-", rt.getVmin()),
							() -> { error("The divisor must be different from 0", e.getRight(), null); return null; });
					if(max != null) {
						return Optional.of(createRangeType(min, max));
					} else {
						error("Cannot infer the upper-bound of the range", e, null);
						return Optional.empty();
					}
				} else {
					error("Cannot infer the lower-bound of the range", e, null);
					return Optional.empty();
				}
			} else {
				error("The right-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(r), e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
				return Optional.empty();
			}
		} else {
			error("The left-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(l), e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			return Optional.empty();
		}
	}

	private final BinaryTypeInfo2<?> binop2Implies = new BooleanBinaryTypeInfo<Type_expression_node>("implies",
						(g,l,lt,lp,ls,r,rt,rp,rs,t) -> createType_expression_Implies(g, l, lt, r, rt, lp, ls, rp, rs));
	private final BinaryTypeInfo2<?> binop2Or = new BooleanBinaryTypeInfo<Type_expression_node>("or",
						(g,l,lt,lp,ls,r,rt,rp,rs,t) -> createType_expression_Or(g, l, lt, r, rt, lp, ls, rp, rs));
	private final BinaryTypeInfo2<?> binop2Xor = new BooleanBinaryTypeInfo<Type_expression_node>("xor",
						(g,l,lt,lp,ls,r,rt,rp,rs,t) -> createType_expression_Xor(g, l, lt, r, rt, lp, ls, rp, rs));
	private final BinaryTypeInfo2<?> binop2And = new BooleanBinaryTypeInfo<Type_expression_node>("and",
						(g,l,lt,lp,ls,r,rt,rp,rs,t) -> createType_expression_And(g, l, lt, r, rt, lp, ls, rp, rs));
	private final BinaryTypeInfo2<?> binop2Equal = new CmpBinaryTypeInfo<>("=", this::createType_expression_Equal, this::binopSolverCmp);

	private Optional<DataType> binopSolverCmp(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				return Optional.of(createBooleanType());
			} else {
				error("The right-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(r), e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
				return Optional.empty();
			}
		} else {
			error("The left-hand operatand of `" + e.getOp() + "' must be a range type, found " + TypeInferenceSolver.typeToString(l), e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			return Optional.empty();
		}
	}

	private final BinaryTypeInfo2<?> binop2Diff = new CmpBinaryTypeInfo<>("<>", this::createType_expression_Diff, this::binopSolverCmp);
	private final BinaryTypeInfo2<?> binop2Lt = new CmpBinaryTypeInfo<>("<", this::createType_expression_Lt, this::binopSolverCmp);
	private final BinaryTypeInfo2<?> binop2Le = new CmpBinaryTypeInfo<>("<=", this::createType_expression_Le, this::binopSolverCmp);
	private final BinaryTypeInfo2<?> binop2Gt = new CmpBinaryTypeInfo<>(">", this::createType_expression_Gt, this::binopSolverCmp);
	private final BinaryTypeInfo2<?> binop2Ge = new CmpBinaryTypeInfo<>(">=", this::createType_expression_Ge, this::binopSolverCmp);
	private final BinaryTypeInfo2<?>[] binaryTypeInformations2 = new BinaryTypeInfo2[] {
				binop2Add,
				binop2Sub,
				binop2Mul,
				binop2Div,
				binop2Mod,
				binop2Implies,
				binop2Or,
				binop2Xor,
				binop2And,
				binop2Equal,
				binop2Diff,
				binop2Lt,
				binop2Le,
				binop2Gt,
				binop2Ge
		};

	private static Optional<DataType> chooseBetweenOrElse(Optional<DataType> lb, Optional<DataType> ub, Optional<DataType> other) {
		return OptionalUtils.orElse(lb, OptionalUtils.orElse(ub, other));
	}

	protected Pair<Type_expression, DataType> type_expression(Environment gamma, Expression e) {
		saveEnvironment(e, gamma);
		Pair<Type_expression_node, DataType> p1 = type_expression_node(gamma, e);
		Type_expression_node ten = p1.getA();
		DataType t = p1.getB();
		if(ten != null && t != null) {
			saveProof(e, ten);
			saveType(e, t);
			return new Pair<>(p(Type_expression.class, gamma,
					(gamma_) -> p(Type_expression.class, t,
							(t_) -> createType_expression_and_type(gamma_, e, t_, ten, check_datatype(t_)))), t);
		} else {
			return new Pair<>(null, null);
		}
	}

	protected Pair<Type_expression_node, DataType> type_expression_node(Environment gamma, Expression e) {
		saveEnvironment(e, gamma);
		if(e instanceof IntegerValue) {
			return type_expression_node_IntegerValue(gamma, (IntegerValue) e);
		} else if(e instanceof UnaryExpression) {
			return type_expression_node_UnaryExpression(gamma, (UnaryExpression) e);
		} else if(e instanceof BinaryExpression) {
			return type_expression_node_BinaryExpression(gamma, (BinaryExpression) e);
		} else if (e instanceof IdentExpression) {
			return type_expression_node_IdentExpression(gamma, (IdentExpression)e);
		} else if(e instanceof MethodCall) {
			return type_expression_node_MethodCall(gamma, (MethodCall) e);
		} else if(e instanceof Tuple) {
			return type_expression_node_Tuple(gamma, (Tuple)e);
		} else if(e instanceof Sequence) {
			return type_expression_node_Sequence(gamma, (Sequence) e);
		} else if(e instanceof org.archware.sosadl.sosADL.Field) {
			return type_expression_node_Field(gamma, (org.archware.sosadl.sosADL.Field)e);
		} else if(e instanceof Map) {
			return type_expression_node_Map(gamma, (Map)e);
		} else {
			error("Type error", e, null);
			return new Pair<>(null, null);
		}
	}
	
	private class MapTyper implements Typer {
		private final Environment gamma;
		private final Map m;
		private final Expression obj;
		private final DataType sTau;
		private final String x;
		private final Expression e;
		private final Type_expression p1;
		
		private DataType tau;
		private DataType tau__e;
		private Type_expression p2;
		
		public MapTyper(Environment gamma, Map m, DataType sTau, Type_expression p1) {
			super();
			this.gamma = gamma;
			this.m = m;
			this.obj = m.getObject();
			this.sTau = sTau;
			this.x = m.getVariable();
			this.e = m.getExpression();
			this.p1 = p1;
		}
		
		private DataType getObjType() {
			if(sTau instanceof TypeVariable) {
				return getSubstitute(sTau);
			} else {
				return sTau;
			}
		}
		
		private Optional<DataType> lookupAndReturnType() {
			DataType s = getObjType();
			if(s instanceof SequenceType) {
				SequenceType st = (SequenceType) s;
				tau = st.getType();
				Pair<Type_expression, DataType> pt2 = type_expression(gamma.put(x, new VariableEnvContent(m, tau)), e);
				tau__e = pt2.getB();
				p2 = pt2.getA();
				if(tau__e != null && p2 != null) {
					return Optional.of(createSequenceType(tau__e));
				} else {
					return Optional.empty();
				}
			} else {
				error("The object must be a sequence", m, SosADLPackage.Literals.MAP__OBJECT);
				return Optional.empty();
			}
		}

		@Override
		public Optional<DataType> computeReturnType() {
			if (sTau instanceof TypeVariable) {
				TypeVariable v = createFreshTypeVariable(m, null, (lb,ub) -> lookupAndReturnType());
				inference.addDependency(v, (TypeVariable) sTau);
				return Optional.of(v);
			} else {
				return lookupAndReturnType();
			}
		}

		@Override
		public Type_expression_node computeProof() {
			return p(Type_expression_node.class, gamma, this::buildProof);
		}

		private Type_expression_node buildProof(Environment gamma) {
			return p(Type_expression_node.class, tau,
					(tau_) -> p(Type_expression_node.class, tau__e,
							(tau__e_) -> createType_expression_Map(gamma, obj, tau_, x, e, tau__e_, p1, p2)));
		}
	}
	
	private Pair<Type_expression_node, DataType> type_expression_node_Map(Environment gamma, Map e) {
		if(e.getExpression() != null && e.getObject() != null && e.getVariable() != null) {
			Pair<Type_expression, DataType> pt1 = type_expression(gamma, e.getObject());
			Type_expression p1 = pt1.getA();
			DataType sTau = pt1.getB();
			if(p1 != null && sTau != null) {
				MapTyper typer = new MapTyper(gamma, e, sTau, p1);
				return typeWithTyper(e, typer);
			} else {
				return new Pair<>(null, null);
			}
		} else {
			if(e.getExpression() == null) {
				error("There must be a collected expression", e, SosADLPackage.Literals.MAP__EXPRESSION);
			}
			if(e.getObject() == null) {
				error("The collected expression must be applied to a sequence", e, SosADLPackage.Literals.MAP__OBJECT);
			}
			if(e.getVariable() == null) {
				error("The collected expression must declare a variable", e, SosADLPackage.Literals.MAP__VARIABLE);
			}
			return new Pair<>(null, null);
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_Field(Environment gamma, org.archware.sosadl.sosADL.Field f) {
		if(f.getField() != null && f.getObject() != null) {
			Pair<Type_expression, DataType> p1 = type_expression(gamma, f.getObject());
			if(p1.getA() != null && p1.getB() != null) {
				TypeVariable v = createFreshTypeVariable(f, SosADLPackage.Literals.FIELD__FIELD,
						(lb,ub) -> chooseBetweenOrElse(lb, ub, Optional.of(createBooleanType())));
				TupleType t = createTupleType(Stream.of(createFieldDecl(f.getField(), v)));
				inference.addConstraint(p1.getB(), t, f, SosADLPackage.Literals.FIELD__FIELD);
				return new Pair<>(saveProof(f,
						p(Type_expression_node.class, gamma,
								(gamma_) -> p(Type_expression_node.class, v,
										(v_) -> createType_expression_Field(gamma_,
											f.getObject(), 
											ECollections.asEList(((TupleType)p1.getB()).getFields().stream()
													.map(this::deepSubstitute).collect(Collectors.toList())),
											f.getField(), v_,
											p1.getA(),
											createReflexivity())))), v);
			} else {
				return new Pair<>(null, null);
			}
		} else {
			if(f.getField() == null) {
				error("A field name must be provided", f, SosADLPackage.Literals.FIELD__FIELD);
			}
			if(f.getObject() == null) {
				error("An object expression must be provided", f, SosADLPackage.Literals.FIELD__OBJECT);
			}
			return new Pair<>(null, null);
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_Sequence(Environment gamma, Sequence s) {
		if(s.getElements() == null) {
			error("A sequence must have a list of items", s, null);
			return new Pair<>(null, null);
		} else if(s.getElements().stream().anyMatch((x) -> x == null)) {
			error("All the items of the sequence must be present", s, SosADLPackage.Literals.SEQUENCE__ELEMENTS);
			return new Pair<>(null, null);
		} else {
			List<Pair<Expression, Pair<Type_expression, DataType>>> elts =
					s.getElements().stream().map((x) -> new Pair<>(x, type_expression(gamma, x))).collect(Collectors.toList());
			if(elts.stream().allMatch((x) -> x.getB() != null && x.getB().getA() != null && x.getB().getB() != null)) {
				TypeVariable v = createFreshTypeVariable(s, SosADLPackage.Literals.SEQUENCE__ELEMENTS,
						(lb,ub) -> chooseBetweenOrElse(lb, ub, Optional.of(createBooleanType())));
				elts.forEach((p) -> inference.addConstraint(p.getB().getB(), v, p.getA()));
				DataType t = createSequenceType(v);
				return new Pair<>(saveProof(s,
						p(Type_expression_node.class, gamma,
								(gamma_) -> p(Type_expression_node.class, t,
										(t_) -> {
									Forall<Expression, Ex<DataType, And<Type_expression, Subtype>>> p1 =
											proveForall(elts, Pair::getA,
											(p) -> {
												DataType pbb = deepSubstitute(p.getB().getB());
												return createEx_intro(pbb,
														createConj(p.getB().getA(),
																subtype(pbb, ((SequenceType)t_).getType(), p.getA(), null).orElse(null)));
											});
									return createType_expression_Sequence(gamma_, s.getElements(), ((SequenceType)t_).getType(), p1);
								}))), t);
			} else {
				return new Pair<>(null, null);
			}
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_Tuple(Environment gamma, Tuple t) {
		if(t.getElements() == null) {
			error("A tuple must have a list of elements", t, null);
			return new Pair<>(null, null);
		} else if(t.getElements().stream().anyMatch((x) -> x == null)) {
			error("All the elements of the tuple must be present", t, SosADLPackage.Literals.TUPLE__ELEMENTS);
			return new Pair<>(null, null);
		} else {
			if(noDuplicate(t.getElements().stream().map((f) -> f.getLabel()))) {
				Collection<Pair<TupleElement, Pair<Type_expression, DataType>>> elts =
						t.getElements().stream().map((f) -> new Pair<>(f, type_expression(gamma, f.getValue())))
						.collect(Collectors.toCollection(ConcurrentLinkedQueue::new));
				if(elts.stream().allMatch((p) -> p.getB().getA() != null && p.getB().getB() != null)) {
					List<Pair<TupleElement, Pair<Type_expression, FieldDecl>>> elts2 =
							elts.stream().map((f) -> new Pair<>(f.getA(),
									new Pair<>(f.getB().getA(), createFieldDecl(f.getA().getLabel(), f.getB().getB()))))
							.collect(Collectors.toList());
					TupleType tt = createTupleType(elts2.stream().map((f) -> f.getB().getB()));
					return new Pair<>(saveProof(t,
							p(Type_expression_node.class,gamma,
									(gamma_) -> p(Type_expression_node.class, tt,
											(tt_) -> {
										Forall2<TupleElement, FieldDecl, Ex<Expression, And<Equality,Ex<DataType,And<Equality,Type_expression>>>>> p3 =
												proveForall2(elts2,
													(x) -> x.getA(),
													(x) -> getSubstitute(x.getB().getB()),
													(x) -> createEx_intro(x.getA().getValue(),
															createConj(createReflexivity(),
																	createEx_intro(getSubstitute(x.getB().getB().getType()),
																			createConj(createReflexivity(), x.getB().getA())))));
										return createType_expression_Tuple(gamma_, t.getElements(),
												((TupleType)tt_).getFields(),
												createReflexivity(),
												proveForall2(t.getElements(), ((TupleType)tt_).getFields(),
														(x,y) -> createReflexivity()),
												p3);
									}))),
							saveType(t, tt));
				} else {
					return new Pair<>(null, null);
				}
			} else {
				t.getElements().stream().filter((p) -> t.getElements().stream().map((x) -> x.getLabel())
						.filter((n) -> n.equals(p.getLabel())).count() >= 2)
				.forEach((f) -> error("Multiple fields named `" + f.getLabel() + "'", f, null));
				return new Pair<>(null, null);
			}
		}
	}
	
	private class MethodCallTyper implements Typer {
		private final Environment gamma;
		private final MethodCall mc;
		private final String methodName;
		private final DataType selfType;
		private final Type_expression selfP;
		private final List<Pair<Expression,Pair<Type_expression, DataType>>> params;
		
		private int tecRank;
		private TypeEnvContent tec;
		private int mRank;
		private FunctionDecl decl;
		
		public MethodCallTyper(Environment gamma, MethodCall mc, String methodName, DataType selfType, Type_expression selfP,
				List<Pair<Expression, Pair<Type_expression, DataType>>> params) {
			this.gamma = gamma;
			this.mc = mc;
			this.methodName = methodName;
			this.selfType = selfType;
			this.selfP = selfP;
			this.params = params;
		}
		
		private Optional<DataType> lookupAndReturnType() {
			DataType sSelfType = getSubstitute(selfType);
			List<DataType> sParamsTypes = params.stream().map(Pair::getB).map(Pair::getB)
					.map(TypeCheckerExpression.this::getSubstitute)
					.collect(Collectors.toList());
			Optional<IntPair<Pair<TypeEnvContent, IntPair<FunctionDecl>>>> method = lookupForMethod(gamma, sSelfType,
					methodName, sParamsTypes);
			if(!method.isPresent()) {
				noSuchMethod(mc, sSelfType, methodName, sParamsTypes);
			} else {
				IntPair<Pair<TypeEnvContent, IntPair<FunctionDecl>>> m = method.get();
				tecRank = m.getA();
				tec = m.getB().getA();
				mRank = m.getB().getB().getA();
				decl = m.getB().getB().getB();
				saveBinder(mc, decl);
			}
			return method.map(IntPair::getB).map(Pair::getB).map(IntPair::getB).map(FunctionDecl::getType);
		}
		
		/* (non-Javadoc)
		 * @see org.archware.sosadl.validation.typing.Typer#computeReturnType()
		 */
		@Override
		public Optional<DataType> computeReturnType() {
			if (streamTypes().anyMatch(TypeInferenceSolver::containsVariable)) {
				TypeVariable v = createFreshTypeVariable(mc, null, (lb,ub) -> lookupAndReturnType());
				streamTypes()
				.flatMap(TypeInferenceSolver::streamVariables)
				.forEach((x) -> inference.addDependency(v, x));
				return Optional.of(v);
			} else {
				return lookupAndReturnType();
			}
		}

		private Stream<DataType> streamTypes() {
			return Stream.of(Stream.of(selfType), params.stream().map(Pair::getB).map(Pair::getB))
			.flatMap((i) -> i);
		}
		
		/* (non-Javadoc)
		 * @see org.archware.sosadl.validation.typing.Typer#computeProof()
		 */
		@Override
		public Type_expression_node computeProof() {
			return p(Type_expression_node.class, gamma, this::buildProof);
		}
		
		private Type_expression_node buildProof(Environment gamma) {
			return p(Type_expression_node.class, selfType,
			(selfType_) -> p(Type_expression_node.class, decl.getData().getType(),
					(ddt_) -> p(Type_expression_node.class, params,
							(params_) ->
			createType_expression_MethodCall(gamma, mc.getObject(), selfType_,
					tec.getDataTypeDecl(),
					ddt_,
					tec.getMethods(),
					methodName,
					decl.getParameters(),
					decl.getType(),
					mc.getParameters(),
					selfP,
					createEx_intro(BigInteger.valueOf(tecRank), createReflexivity()),
					subtype(selfType, decl.getData().getType(), mc, null).orElse(null),
					createEx_intro(BigInteger.valueOf(mRank),
							createConj(createReflexivity(), createConj(createReflexivity(), createConj(createReflexivity(), createReflexivity())))),
					proveForall2(decl.getParameters(),
							mc.getParameters(),
							(fp,p) -> {
								Pair<Type_expression, DataType> tp = ListUtils.assoc(params_, p);
								Type_expression pp = tp.getA();
								DataType pt = tp.getB();
								return createEx_intro(fp.getType(),
									createConj(createReflexivity(),
											createEx_intro(pt,
													createConj(pp,
															subtype(pt, fp.getType(), mc, null).orElse(null)))));
								})))));
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_MethodCall(Environment gamma, MethodCall mc) {
		String methodName = mc.getMethod();
		if (methodName != null) {
			Pair<Type_expression, DataType> self = type_expression(gamma, mc.getObject());
			List<Pair<Expression,Pair<Type_expression, DataType>>> params = ListExtensions.map(mc.getParameters(), (p) -> new Pair<>(p, type_expression(gamma, p)));
			DataType selfType = self.getB();
			if(self.getA() != null && selfType != null && params.stream().allMatch((p) -> p.getA() != null && p.getB() != null)) {
				Typer mct = new MethodCallTyper(gamma, mc, methodName, selfType, self.getA(), params);
				return typeWithTyper(mc, mct);
			} else {
				return new Pair<>(null, null);
			}
		} else {
			error("A method name must be provided", mc, SosADLPackage.Literals.METHOD_CALL__METHOD);
			return new Pair<>(null, null);
		}
	}

	private interface Typer {

		Optional<DataType> computeReturnType();

		Type_expression_node computeProof();

	}
	
	private Pair<Type_expression_node, DataType> typeWithTyper(Expression mc, Typer mct) {
		Optional<DataType> oret = mct.computeReturnType();
		if(oret.isPresent()) {
			DataType ret = oret.get();
			return new Pair<>(saveProof(mc, mct.computeProof()), saveType(mc, ret));
		} else {
			return new Pair<>(null, null);
		}
	}

	private void noSuchMethod(MethodCall mc, DataType sSelfType, String methodName, List<DataType> sParamsTypes) {
		error("No method compatible with signature: `" + TypeInferenceSolver.typeToString(sSelfType) + "::" + methodName
				+ "(" + sParamsTypes.stream().map(TypeInferenceSolver::typeToString).collect(Collectors.joining(", ")) + ")'",
				mc, SosADLPackage.Literals.METHOD_CALL__METHOD);
	}

	private Optional<IntPair<Pair<TypeEnvContent, IntPair<FunctionDecl>>>> lookupForMethod(Environment gamma,
			DataType selfType, String methodName, List<DataType> params) {
		Stream<IntPair<TypeEnvContent>> indexedTypes = 
				StreamUtils.indexed(gamma.stream())
			.flatMap((i) -> {
				if (i.getB() instanceof TypeEnvContent) {
					return Stream.of(new IntPair<>(i.getA(), (TypeEnvContent)i.getB()));
				} else {
					return Stream.empty();
				}
			});
		Stream<IntPair<TypeEnvContent>> compatibleIndexedTypes = 
				indexedTypes
				.filter((i) -> isSubtype(selfType, i.getB().getDataType()));
		Optional<IntPair<Pair<TypeEnvContent,IntPair<FunctionDecl>>>> method =
				compatibleIndexedTypes
				.flatMap((i) -> StreamUtils.indexed(i.getB().getMethods().stream())
						.filter((m) -> m.getB().getName().equals(methodName))
						.filter((m) -> params.size() == m.getB().getParameters().size())
						.filter((m) -> StreamUtils.zip(params.stream(), m.getB().getParameters().stream())
								.allMatch((p) -> isSubtype(p.getA(), p.getB().getType())))
						.map((m) -> new IntPair<>(i.getA(), new Pair<>(i.getB(), m))))
				.findFirst();
		return method;
	}

	private Pair<Type_expression_node, DataType> type_expression_node_IdentExpression(Environment gamma, IdentExpression e) {
		if(e.getIdent() == null) {
			error("The identifier must refer to a name", e, SosADLPackage.Literals.IDENT_EXPRESSION__IDENT);
			return new Pair<>(null, null);
		} else {
			EnvContent ec = gamma.get(e.getIdent());
			if(ec == null) {
				error("The name `" + e.getIdent() + "' is undefined in this context", e, SosADLPackage.Literals.IDENT_EXPRESSION__IDENT);
				return new Pair<>(null, null);
			} else if(!(ec instanceof VariableEnvContent)) {
				error("The name `" + e.getIdent() + "' does not refer to a variable in this context", e, SosADLPackage.Literals.IDENT_EXPRESSION__IDENT);
				return new Pair<>(null, null);
			} else {
				VariableEnvContent vec = (VariableEnvContent)ec;
				DataType t = vec.getType();
				saveBinder(e, vec.getBinder());
				return new Pair<>(saveProof(e,
						p(Type_expression_node.class, gamma,
								(gamma_) ->p(Type_expression_node.class, t,
										(t_) -> createType_expression_Ident(gamma_, e.getIdent(), t_, createReflexivity())))),
						saveType(e, t));
			}
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_BinaryExpression(Environment gamma, BinaryExpression e) {
		if(e.getLeft() == null) {
			error("The binary operator must have a left operand", e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			return new Pair<>(null, null);
		} else if(e.getOp() == null) {
			error("The binary operator must have an operator", e, SosADLPackage.Literals.BINARY_EXPRESSION__OP);
			return new Pair<>(null, null);
		} else if(e.getRight() == null) {
			error("The binary operator must have a right operand", e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
			return new Pair<>(null, null);
		} else {
			Pair<Type_expression, DataType> pp1 = type_expression(gamma, e.getLeft());
			Type_expression p1 = pp1.getA();
			DataType t1 = pp1.getB();
			Pair<Type_expression, DataType> pp3 = type_expression(gamma, e.getRight());
			Type_expression p3 = pp3.getA();
			DataType t3 = pp3.getB();
			if(p1 != null && t1 != null && p3 != null && t3 != null) {
				for(BinaryTypeInfo2<?> i : binaryTypeInformations2) {
					if(i.isCandidate(e.getOp(), t1, t3)) {
						Optional<DataType> or = i.immediateType(e, t1, t3);
						if(or.isPresent()) {
							DataType r = or.get();
							return new Pair<>(
									saveProof(e, p(Type_expression_node.class, gamma,
											(gamma_) -> p(Type_expression_node.class, t1,
													(t1_) -> p(Type_expression_node.class, t3,
															(t3_) -> p(Type_expression_node.class, r,
																	(r_) -> i.prove(gamma_, e, p1, t1_, p3, t3_, r_)))))),
									saveType(e, r));
						}
					}
				}
				error("Unknown unary operator with types " + TypeInferenceSolver.typeToString(t1) + " `" + e.getOp() + "' " + TypeInferenceSolver.typeToString(t3),
						e, SosADLPackage.Literals.BINARY_EXPRESSION__OP);
				return new Pair<>(null, null);
			} else {
				return new Pair<>(null, null);
			}
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_UnaryExpression(Environment gamma, UnaryExpression e) {
		if(e.getRight() == null) {
			error("The unary operator must have a right operand", e, SosADLPackage.Literals.UNARY_EXPRESSION__RIGHT);
			return new Pair<>(null, null);
		} else if(e.getOp() == null) {
			error("The unary expression must have an operator", e, SosADLPackage.Literals.UNARY_EXPRESSION__OP);
			return new Pair<>(null, null);
		} else {
			Pair<Type_expression, DataType> pp1 = type_expression(gamma, e.getRight());
			Type_expression p1 = pp1.getA();
			DataType t1 = pp1.getB();
			if(p1 != null && t1 != null) {
				for(UnaryTypeInfo2<?> i : unaryTypeInformations2) {
					if(i.isCandidate(e.getOp(), t1)) {
						Optional<DataType> or = i.immediateType(e, t1);
						if(or.isPresent()) {
							DataType r = or.get();
							return new Pair<>(
									saveProof(e, p(Type_expression_node.class, gamma,
											(gamma_) -> p(Type_expression_node.class, t1,
													(t1_) -> i.prove(gamma_, e, p1, t1_)))),
									saveType(e, r));
						}
					}
				}
				error("Unknown unary operator `" + e.getOp() + "' applied to type " + TypeInferenceSolver.typeToString(t1),
						e, SosADLPackage.Literals.UNARY_EXPRESSION__OP);
				return new Pair<>(null, null);
			} else {
				return new Pair<>(null, null);
			}
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_IntegerValue(Environment gamma, IntegerValue e) {
		DataType t = createRangeType(e, e);
		return new Pair<>(saveProof(e,
				p(Type_expression_node.class, gamma, (gamma_) -> createType_expression_IntegerValue(gamma_, BigInteger.valueOf(((IntegerValue) e).getAbsInt())))),
				saveType(e, t));
	}

	class BooleanUnaryTypeInfo<P extends Type_expression_node> extends AbstractUnaryTypeInfo<P> {
		public BooleanUnaryTypeInfo(String operator, PentaFunction<Environment, Expression, DataType, Type_expression, Subtype, P> prover) {
			super(operator, prover);
		}
		
		@Override
		public Optional<DataType> immediateType(UnaryExpression e, DataType operand) {
			inference.addConstraint(operand, createBooleanType(), e, SosADLPackage.Literals.UNARY_EXPRESSION__RIGHT);
			return Optional.of(TypeChecker.createBooleanType());
		}
	}
	
	class SynthetizingUnaryTypeInfo<P extends Type_expression_node> extends AbstractUnaryTypeInfo<P> {
		private final BiFunction<UnaryExpression, DataType, Optional<DataType>> solver;
		
		public SynthetizingUnaryTypeInfo(String operator,
				PentaFunction<Environment, Expression, DataType, Type_expression, Subtype, P> prover,
				BiFunction<UnaryExpression, DataType, Optional<DataType>> solver) {
			super(operator, prover);
			this.solver = solver;
		}
		
		@Override
		public Optional<DataType> immediateType(UnaryExpression e, DataType operand) {
			if(TypeInferenceSolver.containsVariable(operand)) {
				TypeVariable v = inference.createFreshTypeVariable((lb,ub) -> solver.apply(e, getSubstitute(operand)), e, null);
				TypeInferenceSolver.streamVariables(operand).forEach((x) -> inference.addDependency(v, x));
				return Optional.of(v);
			} else {
				return solver.apply(e, operand);
			}
		}
	}
	
	class SynthetizingBinaryTypeInfo<P extends Type_expression_node> extends AbstractBinaryTypeInfo<P> {
		private final TriFunction<BinaryExpression, DataType, DataType, Optional<DataType>> solver;
		
		public SynthetizingBinaryTypeInfo(String operator,
				DecaFunction<Environment, Expression, DataType, Type_expression, Subtype, Expression, DataType, Type_expression, Subtype, DataType, P> prover,
				TriFunction<BinaryExpression, DataType, DataType, Optional<DataType>> solver) {
			super(operator, prover);
			this.solver = solver;
		}
		
		@Override
		public Optional<DataType> immediateType(BinaryExpression e, DataType left, DataType right) {
			Collection<TypeVariable> vars = Stream.of(left, right)
					.flatMap(TypeInferenceSolver::streamVariables)
					.collect(Collectors.toCollection(ConcurrentLinkedDeque::new));
			if(vars.isEmpty()) {
				return solver.apply(e, left, right);
			} else {
				TypeVariable v = inference.createFreshTypeVariable((lb,ub) -> solver.apply(e, getSubstitute(left), getSubstitute(right)), e, null);
				vars.forEach((x) -> inference.addDependency(v, x));
				return Optional.of(v);
			}
		}
	}
	
	class CmpBinaryTypeInfo<P extends Type_expression_node> extends SynthetizingBinaryTypeInfo<Type_expression_node> {
		public CmpBinaryTypeInfo(String operator, TreDecaFunction<Environment, Expression, DataType, Expression, Expression, Expression, DataType, Expression, Expression, Type_expression, Subtype, Type_expression, Subtype, Type_expression_node> constructor, TriFunction<BinaryExpression, DataType, DataType, Optional<DataType>> solver) {
			super(operator,
					(g,l,lt,lp,ls,r,rt,rp,rs,dr) -> constructor.apply(g,
							l, lt, ((RangeType)lt).getVmin(), ((RangeType)lt).getVmax(),
							r, rt, ((RangeType)rt).getVmin(), ((RangeType)rt).getVmax(),
							lp, ls, rp, rs),
					solver
					);
		}
	}

	class BooleanBinaryTypeInfo<P extends Type_expression_node> extends AbstractBinaryTypeInfo<P> {
		public BooleanBinaryTypeInfo(String operator, DecaFunction<Environment, Expression, DataType, Type_expression, Subtype, Expression, DataType, Type_expression, Subtype, DataType, P> prover) {
			super(operator, prover);
		}

		@Override
		public Optional<DataType> immediateType(BinaryExpression e, DataType left, DataType right) {
			inference.addConstraint(left, createBooleanType(), e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			inference.addConstraint(right, createBooleanType(), e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
			return Optional.of(TypeChecker.createBooleanType());
		}
	}

}