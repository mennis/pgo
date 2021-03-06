package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PcalProcess extends Node {
	private VariableDeclaration name;
	private Fairness fairness;
	private List<VariableDeclaration> variables;
	private List<LabeledStatements> labeledStatements;

	public PcalProcess(SourceLocation location, VariableDeclaration name, Fairness fairness, List<VariableDeclaration> variables, List<LabeledStatements> labeledStatements) {
		super(location);
		this.name = name;
		this.fairness = fairness;
		this.variables = variables;
		this.labeledStatements = labeledStatements;
	}

	@Override
	public PcalProcess copy() {
		return new PcalProcess(getLocation(), name.copy(), fairness,
				variables.stream().map(VariableDeclaration::copy).collect(Collectors.toList()),
				labeledStatements.stream().map(LabeledStatements::copy).collect(Collectors.toList()));
	}

	public VariableDeclaration getName() {
		return name;
	}

	public Fairness getFairness() {
		return fairness;
	}

	public List<VariableDeclaration> getVariables() {
		return variables;
	}

	public List<LabeledStatements> getLabeledStatements() {
		return labeledStatements;
	}

	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((fairness == null) ? 0 : fairness.hashCode());
		result = prime * result + ((labeledStatements == null) ? 0 : labeledStatements.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((variables == null) ? 0 : variables.hashCode());
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
		PcalProcess other = (PcalProcess) obj;
		if (fairness != other.fairness)
			return false;
		if (labeledStatements == null) {
			if (other.labeledStatements != null)
				return false;
		} else if (!labeledStatements.equals(other.labeledStatements))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (variables == null) {
			if (other.variables != null)
				return false;
		} else if (!variables.equals(other.variables))
			return false;
		return true;
	}
}
