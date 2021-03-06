package pgo.model.tla;

import pgo.util.SourceLocation;

public class PGoTLABool extends PGoTLAExpression {

	private boolean value;

	public PGoTLABool(SourceLocation location, boolean value) {
		super(location);
		this.value = value;
	}
	
	@Override
	public PGoTLABool copy() {
		return new PGoTLABool(getLocation(), value);
	}

	public boolean getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (value ? 1231 : 1237);
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PGoTLABool other = (PGoTLABool) obj;
		if (value != other.value)
			return false;
		return true;
	}
	
}
