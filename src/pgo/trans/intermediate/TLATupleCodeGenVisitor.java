package pgo.trans.intermediate;

import java.util.List;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.golang.InterfaceType;
import pgo.model.golang.PtrType;
import pgo.model.golang.SliceLiteral;
import pgo.model.golang.SliceType;
import pgo.model.golang.StructType;
import pgo.model.golang.TypeName;
import pgo.model.golang.TypeVisitor;

public class TLATupleCodeGenVisitor extends TypeVisitor<Expression, RuntimeException> {

	private BlockBuilder builder;
	private List<Expression> elements;

	public TLATupleCodeGenVisitor(BlockBuilder builder, List<Expression> elements) {
		this.builder = builder;
		this.elements = elements;
	}

	@Override
	public Expression visit(TypeName typeName) throws RuntimeException {
		throw new RuntimeException("internal compiler error");
	}

	@Override
	public Expression visit(StructType structType) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PtrType ptrType) throws RuntimeException {
		throw new RuntimeException("internal compiler error");
	}

	@Override
	public Expression visit(SliceType sliceType) throws RuntimeException {
		return new SliceLiteral(sliceType.getElementType(), elements);
	}

	@Override
	public Expression visit(InterfaceType interfaceType) throws RuntimeException {
		throw new RuntimeException("internal compiler error");
	}

}
