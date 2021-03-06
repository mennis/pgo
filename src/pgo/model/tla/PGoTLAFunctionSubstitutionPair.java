package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PGoTLAFunctionSubstitutionPair extends PGoTLANode {

	private List<PGoTLASubstitutionKey> keys;
	private PGoTLAExpression value;

	public PGoTLAFunctionSubstitutionPair(SourceLocation location, List<PGoTLASubstitutionKey> keys, PGoTLAExpression value) {
		super(location);
		this.keys = keys;
		this.value = value;
	}
	
	@Override
	public PGoTLAFunctionSubstitutionPair copy() {
		return new PGoTLAFunctionSubstitutionPair(getLocation(), keys.stream().map(PGoTLASubstitutionKey::copy).collect(Collectors.toList()), value.copy());
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTLANodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public List<PGoTLASubstitutionKey> getKeys(){
		return keys;
	}
	
	public PGoTLAExpression getValue() {
		return value;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((keys == null) ? 0 : keys.hashCode());
		result = prime * result + ((value == null) ? 0 : value.hashCode());
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
		PGoTLAFunctionSubstitutionPair other = (PGoTLAFunctionSubstitutionPair) obj;
		if (keys == null) {
			if (other.keys != null)
				return false;
		} else if (!keys.equals(other.keys))
			return false;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		return true;
	}

}
