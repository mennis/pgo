package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.*;
import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoCollectionType.PGoChan;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoCollectionType.PGoSlice;
import pgo.model.intermediate.PGoCollectionType.PGoTuple;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoLibFunction;
import pgo.model.intermediate.PGoPrimitiveType.PGoDecimal;
import pgo.model.intermediate.PGoPrimitiveType.PGoNatural;
import pgo.model.intermediate.PGoPrimitiveType.PGoNumber;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.PGoTempData;

/**
 * Converts the TLA ast generated by the TLAExprParser into GoAST
 *
 */
public class TLAExprToGo {
	// the resulting GoAST expression
	private Expression expr;
	// the inferred type of the expression
	private PGoType type;
	// the Go program's imports
	private Imports imports;
	// the intermediate data; includes information about the type of variables
	private PGoTempData data;
	// the variable we are assigning to, if it exists and is relevant
	private PGoVariable assign;

	public TLAExprToGo(PGoTLA tla, Imports imports, PGoTempData data) throws PGoTransException {
		this.imports = imports;
		this.data = data;
		assign = null;
		type = new TLAExprToType(tla, data).getType();
		expr = tla.convert(this);
	}

	public TLAExprToGo(PGoTLA tla, Imports imports, PGoTempData data, PGoVariable assign) throws PGoTransException {
		this.imports = imports;
		this.data = data;
		this.assign = assign;
		type = new TLAExprToType(tla, data, assign).getType();
		expr = tla.convert(this);
	}

	public PGoType getType() {
		return type;
	}

	public Expression toExpression() {
		return expr;
	}

	/**
	 * Convert the TLA expression to a Go AST, while also adding the correct
	 * imports.
	 * 
	 * @param tla
	 *            the TLA expression
	 */
	protected Expression translate(PGoTLAArray tla) throws PGoTransException {
		// TODO (issue #5, 23)
		if (tla.getContents().size() == 1 && tla.getContents().get(0) instanceof PGoTLAVariadic) {
			// maps to or except operator
			return translate((PGoTLAVariadic) tla.getContents().get(0));
		}
		// array or chan, depending on assigned type
		Vector<Expression> contents = new Vector<>();
		for (PGoTLA elt : tla.getContents()) {
			Expression e = new TLAExprToGo(elt, imports, data).toExpression();
			contents.add(e);
		}
		if (type instanceof PGoTuple) {
			return new FunctionCall("pgoutil.NewTuple", contents);
		} else if (type instanceof PGoChan) {
			return new FunctionCall("pgoutil.NewChan", contents);
		}
		assert false;
		return null;
	}

	protected Expression translate(PGoTLAVariadic tla) throws PGoTransException {
		// TODO
		switch (tla.getToken()) {
		case "|->":
			// tla: x \in S, y \in T |-> f(x, y)
			// go: pgoutil.MapsTo(func(x, y type) type { return f(x, y) }, S, T)
			// func params to MapsTo
			Vector<Expression> params = new Vector<>();
			// params for anonymous function
			Vector<ParameterDeclaration> decls = new Vector<>();
			PGoTempData temp = new PGoTempData(data);
			for (PGoTLA arg : tla.getArgs()) {
				assert (arg instanceof PGoTLASetOp);
				PGoTLASetOp in = (PGoTLASetOp) arg;
				assert (in.getToken().equals("\\in"));
				// TODO handle tuples
				assert (in.getLeft() instanceof PGoTLAVariable);
				PGoTLAVariable var = (PGoTLAVariable) in.getLeft();
				PGoType setType = new TLAExprToType(in.getRight(), data).getType();
				assert (setType instanceof PGoSet);
				PGoType containedType = ((PGoSet) setType).getElementType();

				decls.add(new ParameterDeclaration(var.getName(), containedType));
				params.add(new TLAExprToGo(in.getRight(), imports, data).toExpression());

				temp.getLocals().put(var.getName(), PGoVariable.convert(var.getName(), containedType));
			}
			// Create anonymous function for f
			TLAExprToGo trans = new TLAExprToGo(tla.getExpr(), imports, temp);
			AnonymousFunction f = new AnonymousFunction(trans.getType(), decls, new Vector<>(),
					new Vector<Statement>() {
						{
							add(new Return(trans.toExpression()));
						}
					});
			params.add(0, f);
			imports.addImport("pgoutil");
			return new FunctionCall("pgoutil.MapsTo", params);
		case "EXCEPT":
			// tla: f EXCEPT ![x1] = y1, [x2] = y2...
			// TODO
			return null;
		case ":":
			// if we are calling this, it is set constructor or set image
			if (tla.isRightSide()) {
				// set image { f(x, y) : x \in S, y \in T }
				// go func: pgoutil.SetImage(func(x, y type) type { return f(x,
				// y) }, S, T)

				// the set operations
				Vector<Expression> varExprs = new Vector<>(), setExprs = new Vector<>();
				// add temporary typing data used to translate the predicate
				temp = new PGoTempData(data);
				// parameters for anonymous function
				decls = new Vector<ParameterDeclaration>();
				// the SetImage function parameters
				params = new Vector<Expression>();
				for (PGoTLA arg : tla.getArgs()) {
					PGoTLASetOp setOp = (PGoTLASetOp) arg;
					varExprs.add(new TLAExprToGo(setOp.getLeft(), imports, data).toExpression());
					setExprs.add(new TLAExprToGo(setOp.getRight(), imports, data).toExpression());
					// TODO handle tuples
					assert (setOp.getLeft() instanceof PGoTLAVariable);
					PGoTLAVariable var = (PGoTLAVariable) setOp.getLeft();
					PGoType setType = new TLAExprToType(setOp.getRight(), data).getType();
					assert (setType instanceof PGoSet);
					PGoType containedType = ((PGoSet) setType).getElementType();

					decls.add(new ParameterDeclaration(var.getName(), containedType));
					params.add(new TLAExprToGo(setOp.getRight(), imports, data).toExpression());

					temp.getLocals().put(var.getName(), PGoVariable.convert(var.getName(), containedType));
				}
				trans = new TLAExprToGo(tla.getExpr(), imports, temp);
				f = new AnonymousFunction(trans.getType(), decls, new Vector<>(),
						new Vector<Statement>() {
							{
								add(new Return(trans.toExpression()));
							}
						});
				params.add(0, f);
				imports.addImport("pgoutil");
				return new FunctionCall("pgoutil.SetImage", params);
			} else {
				// set constructor { x \in S : P(x) }
				// go func: pgoutil.SetConstructor(S, func(x type) bool { return
				// P(x) })
				// there is only a single set expression S

				assert (tla.getArgs().size() == 1);
				PGoTLASetOp setOp = (PGoTLASetOp) tla.getArgs().get(0);
				TLAExprToGo setTrans = new TLAExprToGo(setOp.getRight(), imports, data);
				assert (setTrans.getType() instanceof PGoSet);
				PGoType varType = ((PGoSet) setTrans.getType()).getElementType();

				// TODO handle tuples
				assert (setOp.getLeft() instanceof PGoTLAVariable);
				PGoTLAVariable var = (PGoTLAVariable) setOp.getLeft();
				temp = new PGoTempData(data);
				temp.getLocals().put(var.getName(), PGoVariable.convert(var.getName(), varType));

				AnonymousFunction P = new AnonymousFunction(
						PGoType.inferFromGoTypeName("bool"),
						new Vector<ParameterDeclaration>() {
							{
								add(new ParameterDeclaration(var.getName(), varType));
							}
						},
						new Vector<>(),
						new Vector<Statement>() {
							{
								add(new Return(new TLAExprToGo(tla.getExpr(), imports, temp).toExpression()));
							}
						});
				imports.addImport("pgoutil");
				return new FunctionCall("pgoutil.SetConstructor", new Vector<Expression>() {
					{
						add(setTrans.toExpression());
						add(P);
					}
				});
			}
		default:
			assert false;
			return null;
		}
	}

	protected Expression translate(PGoTLABool tla) {
		return new Token(String.valueOf(tla.getVal()));
	}

	protected Expression translate(PGoTLABoolOp tla) throws PGoTransException {
		Expression leftRes = new TLAExprToGo(tla.getLeft(), imports, data).toExpression();
		Expression rightRes = new TLAExprToGo(tla.getRight(), imports, data).toExpression();

		// we have already checked types for consistency, so can check just lhs
		PGoType leftType = new TLAExprToType(tla.getLeft(), data).getType();
		if (leftType instanceof PGoSet) {
			imports.addImport("pgoutil");
			Vector<Expression> leftExp = new Vector<>();
			leftExp.add(leftRes);

			switch (tla.getToken()) {
			case "#":
			case "/=":
				Vector<Expression> toks = new Vector<>();
				toks.add(new Token("!"));
				toks.add(new FunctionCall("Equal", leftExp, rightRes));
				return new SimpleExpression(toks);
			case "=":
			case "==":
				return new FunctionCall("Equal", leftExp, rightRes);
			default:
				assert false;
				return null;
			}
		}

		String tok = tla.getToken();
		switch (tok) {
		case "#":
		case "/=":
			tok = "!=";
			break;
		case "/\\":
		case "\\land":
			tok = "&&";
			break;
		case "\\/":
		case "\\lor":
			tok = "||";
			break;
		case "=<":
		case "\\leq":
			tok = "<=";
			break;
		case "\\geq":
			tok = ">=";
			break;
		case "=":
			tok = "==";
			break;
		}

		// if we are comparing number types we may need to do type conversion
		if (leftType instanceof PGoNumber) {
			PGoType rightType = new TLAExprToType(tla.getRight(), data).getType();
			PGoType convertedType = TLAExprToType.compatibleType(leftType, rightType);
			assert (convertedType != null);
			// cast if not plain number
			if (!leftType.equals(convertedType) && !(tla.getLeft() instanceof PGoTLANumber)) {
				leftRes = new TypeConversion(convertedType, leftRes);
			} else if (!rightType.equals(convertedType) && !(tla.getRight() instanceof PGoTLANumber)) {
				// only one of the left or right needs to be cast
				rightRes = new TypeConversion(convertedType, rightRes);
			}
		}

		Vector<Expression> toks = new Vector<Expression>();
		toks.add(leftRes);
		toks.add(new Token(" " + tok + " "));
		toks.add(rightRes);

		return new SimpleExpression(toks);
	}

	protected Expression translate(PGoTLAFunctionCall tla) throws PGoTransException {
		Vector<Expression> params = new Vector<>();
		for (PGoTLA param : tla.getParams()) {
			params.add(new TLAExprToGo(param, imports, data).toExpression());
		}
		// Determine whether this is a PlusCal macro call, TLA definition call,
		// TLA builtin method call, or map/tuple access.
		PGoFunction func = data.findPGoFunction(tla.getName());
		PGoTLADefinition def = data.findTLADefinition(tla.getName());
		PGoLibFunction lfunc = data.findBuiltInFunction(tla.getName());
		PGoVariable var = data.findPGoVariable(tla.getName());
		if (func != null || def != null) {
			return new FunctionCall(tla.getName(), params);
		} else if (lfunc != null) {
			Vector<PGoType> paramTypes = new Vector<>();
			for (PGoTLA param : tla.getParams()) {
				paramTypes.add(new TLAExprToType(param, data).getType());
			}
			String goName = lfunc.getGoName(paramTypes);
			if (lfunc.isObjectMethod(paramTypes)) {
				// the object is the 1st param
				Expression first = params.remove(0);
				return new FunctionCall(goName, params, first);
			} else {
				return new FunctionCall(goName, params);
			}
		} else {
			if (var.getType() instanceof PGoTuple) {
				// also need to cast element to correct type
				assert (params.size() == 1);
				return new TypeAssertion(new FunctionCall("At", params, new Token(tla.getName())), type);
			} else {
				// map
				if (params.size() > 1) {
					// tuple key
					FunctionCall newTup = new FunctionCall("pgoutil.NewTuple", params);
					return new TypeAssertion(new FunctionCall("Get", new Vector<Expression>() {
						{
							add(newTup);
						}
					}, new Token(tla.getName())), type);
				} else {
					return new TypeAssertion(new FunctionCall("Get", params, new Token(tla.getName())), type);
				}
			}
		}
	}

	protected Expression translate(PGoTLAGroup tla) throws PGoTransException {
		Expression inside = new TLAExprToGo(tla.getInner(), imports, data, assign).toExpression();
		return new Group(inside);
	}

	protected Expression translate(PGoTLANumber tla) {
		return new Token(tla.getVal());
	}

	protected Expression translate(PGoTLASequence tla) throws PGoTransException {
		Expression startRes = new TLAExprToGo(tla.getStart(), imports, data).toExpression();
		Expression endRes = new TLAExprToGo(tla.getEnd(), imports, data).toExpression();

		Vector<Expression> args = new Vector<>();
		// we may need to convert natural to int
		PGoType startType = new TLAExprToType(tla.getStart(), data).getType();
		PGoType endType = new TLAExprToType(tla.getEnd(), data).getType();
		// plain numbers are never naturals (int or float only), so we don't
		// need to check if the exprs are plain numbers
		if (startType instanceof PGoNatural) {
			startRes = new TypeConversion("int", startRes);
		}
		if (endType instanceof PGoNatural) {
			endRes = new TypeConversion("int", endRes);
		}
		args.add(startRes);
		args.add(endRes);

		this.imports.addImport("pgoutil");
		return new FunctionCall("pgoutil.Sequence", args);
	}

	protected Expression translate(PGoTLASet tla) throws PGoTransException {
		if (tla.getContents().size() == 1 && tla.getContents().get(0) instanceof PGoTLAVariadic) {
			// this is set constructor/set image: handled with that translation
			// method
			return new TLAExprToGo(tla.getContents().get(0), imports, data, assign).toExpression();
		}
		Vector<Expression> args = new Vector<>();
		for (PGoTLA ptla : tla.getContents()) {
			args.add(new TLAExprToGo(ptla, imports, data).toExpression());
		}
		this.imports.addImport("pgoutil");
		return new FunctionCall("pgoutil.NewSet", args);
	}

	protected Expression translate(PGoTLASetOp tla) throws PGoTransException {
		Expression leftRes = new TLAExprToGo(tla.getLeft(), imports, data).toExpression();
		Expression rightRes = new TLAExprToGo(tla.getRight(), imports, data).toExpression();

		Vector<Expression> lhs = new Vector<>();
		lhs.add(leftRes);

		Vector<Expression> exp = new Vector<>();
		String funcName = null;
		// Map the set operation to the pgoutil set function. \\notin does not
		// have a corresponding function and is handled separately.
		switch (tla.getToken()) {
		case "\\cup":
		case "\\union":
			funcName = "Union";
			break;
		case "\\cap":
		case "\\intersect":
			funcName = "Intersect";
			break;
		case "\\in":
			funcName = "Contains";
			break;
		case "\\notin":
			funcName = "NotIn";
			break;
		case "\\subseteq":
			funcName = "IsSubset";
			break;
		case "\\":
			funcName = "Difference";
			break;
		default:
			assert false;
		}

		if (funcName.equals("NotIn")) {
			exp.add(new Token("!"));
			funcName = "Contains";
		}
		// rightRes is the object because lhs can be an element (e.g. in
		// Contains)
		this.imports.addImport("pgoutil");
		exp.add(new FunctionCall(funcName, lhs, rightRes));
		return new SimpleExpression(exp);
	}

	protected Expression translate(PGoTLASimpleArithmetic tla) throws PGoTransException {
		Expression leftRes = new TLAExprToGo(tla.getLeft(), imports, data).toExpression();
		Expression rightRes = new TLAExprToGo(tla.getRight(), imports, data).toExpression();
		PGoType leftType = new TLAExprToType(tla.getLeft(), data).getType();
		PGoType rightType = new TLAExprToType(tla.getRight(), data).getType();

		if (tla.getToken().equals("^")) {
			this.imports.addImport("math");
			Vector<Expression> params = new Vector<>();
			// math.Pow takes float64s; convert if needed
			if (!(tla.getLeft() instanceof PGoTLANumber || leftType instanceof PGoDecimal)) {
				leftRes = new TypeConversion("float64", leftRes);
			}
			if (!(tla.getRight() instanceof PGoTLANumber || rightType instanceof PGoDecimal)) {
				rightRes = new TypeConversion("float64", rightRes);
			}
			params.add(leftRes);
			params.add(rightRes);
			return new FunctionCall("math.Pow", params);
		} else {
			PGoType convertedType = TLAExprToType.compatibleType(leftType, rightType);
			assert (convertedType != null);
			if (!(tla.getLeft() instanceof PGoTLANumber || leftType.equals(convertedType))) {
				leftRes = new TypeConversion(convertedType, leftRes);
			} else if (!(tla.getRight() instanceof PGoTLANumber || rightType.equals(convertedType))) {
				rightRes = new TypeConversion(convertedType, rightRes);
			}

			Vector<Expression> toks = new Vector<>();
			toks.add(leftRes);
			toks.add(new Token(" " + tla.getToken() + " "));
			toks.add(rightRes);
			return new SimpleExpression(toks);
		}
	}

	protected Expression translate(PGoTLAString tla) {
		return new Token("\"" + tla.getString() + "\"");
	}

	protected Expression translate(PGoTLAUnary tla) throws PGoTransException {
		Vector<Statement> ret = new Vector<>();

		switch (tla.getToken()) {
		case "~":
		case "\\lnot":
		case "\\neg":
			Expression expr = new TLAExprToGo(tla.getArg(), imports, data).toExpression();
			Vector<Expression> exp = new Vector<>();
			exp.add(new Token("!"));
			exp.add(expr);
			return new SimpleExpression(exp);
		case "UNION":
			expr = new TLAExprToGo(tla.getArg(), imports, data).toExpression();
			FunctionCall fc = new FunctionCall("EltUnion", new Vector<>(), expr);
			this.imports.addImport("pgoutil");
			return fc;
		case "SUBSET":
			expr = new TLAExprToGo(tla.getArg(), imports, data).toExpression();
			FunctionCall fc1 = new FunctionCall("PowerSet", new Vector<>(), expr);
			this.imports.addImport("pgoutil");
			return fc1;
		// these operations are of the form OP x \in S : P(x)
		case "CHOOSE":
			PGoTLAVariadic st = (PGoTLAVariadic) tla.getArg();
			assert (st.getArgs().size() == 1);
			// the set S
			Expression setExpr = new TLAExprToGo(((PGoTLASetOp) st.getArgs().get(0)).getRight(), imports, data)
					.toExpression();
			// the variable x
			Expression varExpr = new TLAExprToGo(((PGoTLASetOp) st.getArgs().get(0)).getLeft(), imports, data)
					.toExpression();
			// We need to add typing data to avoid TLAExprToType complaining
			// about untyped variables
			PGoTempData temp = new PGoTempData(data);
			for (PGoTLA arg : st.getArgs()) {
				PGoTLASetOp set = (PGoTLASetOp) arg;
				// TODO handle stuff like << x, y >> \in S \X T
				assert (set.getLeft() instanceof PGoTLAVariable);
				PGoTLAVariable var = (PGoTLAVariable) set.getLeft();
				PGoType containerType = new TLAExprToType(set.getRight(), data).getType();
				assert (containerType instanceof PGoSet);
				PGoType eltType = ((PGoSet) containerType).getElementType();
				temp.getLocals().put(var.getName(), PGoVariable.convert(var.getName(), eltType));
			}
			Expression pred = new TLAExprToGo(st.getExpr(), imports, temp).toExpression();
			// most expressions can't be used as the variable (only stuff like
			// tuples) so this should be one line
			assert (varExpr.toGo().size() == 1);

			// create the anonymous function for the predicate
			// go func: Choose(P interface{}, S pgoutil.Set) interface{}
			// (P is predicate)
			// P = func(varType) bool { return pred }
			AnonymousFunction P = new AnonymousFunction(PGoType.inferFromGoTypeName("bool"),
					// TODO (issue 28) deal with tuples as variable declaration
					new Vector<ParameterDeclaration>() {
						{
							add(new ParameterDeclaration(varExpr.toGo().get(0),
									new TLAExprToType(tla, data).getType()));
						}
					},
					new Vector<>(),
					new Vector<Statement>() {
						{
							add(new Return(pred));
						}
					});

			Vector<Expression> chooseFuncParams = new Vector<>();
			chooseFuncParams.add(P);
			chooseFuncParams.add(setExpr);

			this.imports.addImport("pgoutil");
			return new FunctionCall("pgoutil.Choose", chooseFuncParams);
		case "\\E":
		case "\\A":
			st = (PGoTLAVariadic) tla.getArg();

			temp = new PGoTempData(data);
			for (PGoTLA arg : st.getArgs()) {
				PGoTLASetOp set = (PGoTLASetOp) arg;
				// TODO handle stuff like << x, y >> \in S \X T
				assert (set.getLeft() instanceof PGoTLAVariable);
				PGoTLAVariable var = (PGoTLAVariable) set.getLeft();
				PGoType containerType = new TLAExprToType(set.getRight(), data).getType();
				assert (containerType instanceof PGoSet);
				PGoType eltType = ((PGoSet) containerType).getElementType();
				temp.getLocals().put(var.getName(), PGoVariable.convert(var.getName(), eltType));
			}
			pred = new TLAExprToGo(st.getExpr(), imports, temp).toExpression();

			Vector<Expression> setExprs = new Vector<>(), varExprs = new Vector<>();
			for (PGoTLA arg : st.getArgs()) {
				PGoTLASetOp setOp = (PGoTLASetOp) arg;
				varExprs.add(new TLAExprToGo(setOp.getLeft(), imports, data).toExpression());
				setExprs.add(new TLAExprToGo(setOp.getRight(), imports, data).toExpression());
			}
			// create the anonymous function for the predicate
			// go func: Exists|ForAll(P interface{}, S ...pgoutil.Set)
			// interface{}
			// (P is predicate)
			// P = func(varType, varType...) bool { return pred }
			Vector<ParameterDeclaration> params = new Vector<>();
			for (int i = 0; i < setExprs.size(); i++) {
				PGoTLA setExprTLA = ((PGoTLASetOp) st.getArgs().get(i)).getRight();
				PGoType setType = new TLAExprToType(setExprTLA, data).getType();
				PGoType varType = ((PGoCollectionType) setType).getElementType();
				params.add(new ParameterDeclaration(varExprs.get(i).toGo().get(0), varType));
			}
			P = new AnonymousFunction(PGoType.inferFromGoTypeName("bool"),
					// TODO (issue 28) deal with tuples as variable declaration
					params,
					new Vector<>(),
					new Vector<Statement>() {
						{
							add(new Return(pred));
						}
					});

			Vector<Expression> funcParams = new Vector<>();
			funcParams.add(P);
			for (Expression s : setExprs) {
				funcParams.add(s);
			}

			this.imports.addImport("pgoutil");
			return new FunctionCall((tla.getToken().equals("\\E") ? "pgoutil.Exists" : "pgoutil.ForAll"),
					funcParams);
		}
		assert false;
		return null;
	}

	protected Expression translate(PGoTLAVariable tla) {
		return new Token(String.valueOf(tla.getName()));
	}
}
