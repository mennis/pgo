package pgo.model.golang;

public class TypeName extends Type {
	
	private String name;
	private boolean builtin;
	
	public TypeName(String name) {
		this.name = name;
		this.builtin = false;
	}
	
	public TypeName(String name, boolean builtin) {
		this.name = name;
		this.builtin = builtin;
	}
	
	public String getName() {
		return name;
	}
	
	public boolean isBuiltin() {
		return builtin;
	}
	
	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
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
		TypeName other = (TypeName) obj;
		if (name == null) {
			return other.name == null;
		}
		return name.equals(other.name);
	}

}
