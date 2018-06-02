package pgo.trans.intermediate;

import java.util.*;

import pgo.errors.IssueContext;
import pgo.model.pcal.*;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAUnit;
import pgo.model.type.*;
import pgo.scope.UID;

public class TypeInferencePass {
	private TypeInferencePass() {}

	static void constrainVariableDeclaration(DefinitionRegistry registry, VariableDeclaration var, PGoTypeSolver solver, PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		PGoTypeVariable v;
		if (mapping.containsKey(var.getUID())) {
			v = mapping.get(var.getUID());
		} else {
			v = generator.get();
			mapping.put(var.getUID(), v);
		}

		PGoType valueType = new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping)
				.wrappedVisit(var.getValue());
		if (var.isSet()) {
			PGoTypeVariable member = generator.get();
			solver.addConstraint(new PGoTypeMonomorphicConstraint(var, new PGoTypeSet(member, Collections.singletonList(valueType)), valueType));
			solver.addConstraint(new PGoTypeMonomorphicConstraint(var, v, member));
		} else {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(var, v, valueType));
		}
	}

	public static Map<UID, PGoType> perform(IssueContext ctx, DefinitionRegistry registry, Algorithm pcal) {
		PGoTypeSolver solver = new PGoTypeSolver();
		PGoTypeGenerator generator = new PGoTypeGenerator("type");
		Map<UID, PGoTypeVariable> mapping = new HashMap<>();

		for (VariableDeclaration var : pcal.getVariables()) {
			constrainVariableDeclaration(registry, var, solver, generator, mapping);
		}

		// make sure the user-provided constant values typecheck
		for (UID id : registry.getConstants()) {
			PGoTypeVariable fresh = generator.get();
			mapping.put(id, fresh);
			PGoTLAExpression value = registry.getConstantValue(id);
			PGoType type = value.accept(new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping));
			solver.addConstraint(new PGoTypeMonomorphicConstraint(value, fresh, type));
		}

		for (PGoTLAUnit unit : pcal.getUnits()) {
			unit.accept(new TLAUnitTypeConstraintVisitor(registry, solver, generator, mapping));
		}

		for (Procedure p : pcal.getProcedures()) {
			List<PGoType> paramTypes = new ArrayList<>();
			for (VariableDeclaration var : p.getArguments()) {
				constrainVariableDeclaration(registry, var, solver, generator, mapping);
				paramTypes.add(mapping.get(var.getUID()));
			}
			PlusCalStatementTypeConstraintVisitor v =
					new PlusCalStatementTypeConstraintVisitor(ctx, registry, solver, generator, mapping);
			for (Statement stmt : p.getBody()) {
				stmt.accept(v);
			}
			PGoTypeVariable fresh = generator.get();
			solver.addConstraint(new PGoTypeMonomorphicConstraint(p, fresh, new PGoTypeProcedure(paramTypes, Collections.singletonList(p))));
			mapping.put(p.getUID(), fresh);
		}

		pcal.getProcesses().accept(new ProcessesVisitor<Void, RuntimeException>(){
			@Override
			public Void visit(SingleProcess singleProcess) throws RuntimeException {
				for (LabeledStatements stmts : singleProcess.getLabeledStatements()) {
					for (Statement stmt : stmts.getStatements()) {
						stmt.accept(new PlusCalStatementTypeConstraintVisitor(ctx, registry, solver, generator, mapping));
					}
				}
				return null;
			}

			@Override
			public Void visit(MultiProcess multiProcess) throws RuntimeException {
				for (PcalProcess proc : multiProcess.getProcesses()) {
					constrainVariableDeclaration(registry, proc.getName(), solver, generator, mapping);
					UID processVariableUID = proc.getName().getUID();
					PGoType processVariableType = mapping.get(processVariableUID);
					solver.addConstraint(new PGoTypePolymorphicConstraint(proc.getName().getUID(), Arrays.asList(
							new PGoTypeEqualityConstraint(
									processVariableType,
									new PGoTypeInt(Collections.singletonList(proc.getName()))),
							new PGoTypeEqualityConstraint(
									processVariableType,
									new PGoTypeString(Collections.singletonList(proc.getName()))))));
					for (VariableDeclaration var : proc.getVariables()) {
						constrainVariableDeclaration(registry, var, solver, generator, mapping);
					}
					for (LabeledStatements stmts : proc.getLabeledStatements()) {
						for (Statement stmt : stmts.getStatements()) {
							stmt.accept(new PlusCalStatementTypeConstraintVisitor(ctx, registry, solver, generator, mapping));
						}
					}
				}
				return null;
			}
		});

		solver.unify(ctx);
		if (ctx.hasErrors()) {
			return null;
		}
		Map<PGoTypeVariable, PGoType> typeMapping = solver.getMapping();

		Map<UID, PGoType> resultingTypeMapping = new HashMap<>();

		for (Map.Entry<UID, PGoTypeVariable> m : mapping.entrySet()) {
			resultingTypeMapping.put(m.getKey(), typeMapping.get(m.getValue()));
		}

		return resultingTypeMapping;
	}
}
