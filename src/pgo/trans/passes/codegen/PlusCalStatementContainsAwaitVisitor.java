package pgo.trans.passes.codegen;

import pgo.Unreachable;
import pgo.model.pcal.*;

public class PlusCalStatementContainsAwaitVisitor extends StatementVisitor<Boolean, RuntimeException> {
	private boolean foundLabeledStatements;

	public PlusCalStatementContainsAwaitVisitor() {
		this(false);
	}

	public PlusCalStatementContainsAwaitVisitor(boolean foundLabeledStatements) {
		this.foundLabeledStatements = foundLabeledStatements;
	}

	@Override
	public Boolean visit(LabeledStatements labeledStatements) throws RuntimeException {
		if (foundLabeledStatements) {
			return false;
		}
		foundLabeledStatements = true;
		return labeledStatements.getStatements().stream().anyMatch(s -> s.accept(this));
	}

	@Override
	public Boolean visit(While while1) throws RuntimeException {
		return while1.getBody().stream().anyMatch(s -> s.accept(this));
	}

	@Override
	public Boolean visit(If if1) throws RuntimeException {
		return if1.getYes().stream().anyMatch(s -> s.accept(this)) ||
				if1.getNo().stream().anyMatch(s -> s.accept(this));
	}

	@Override
	public Boolean visit(Either either) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Assignment assignment) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Return return1) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Skip skip) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Call call) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(MacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Boolean visit(With with) throws RuntimeException {
		return with.getBody().stream().anyMatch(s -> s.accept(this));
	}

	@Override
	public Boolean visit(Print print) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Assert assert1) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(Await await) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(Goto goto1) throws RuntimeException {
		return false;
	}
}
