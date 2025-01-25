package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessUFManager
    extends AbstractUFManager<DummyFormula, DummyFunction, FormulaTypesForChecking, DummyEnv> {

  private final Map<String, DummyFunction> uninterpretedFunctions = new HashMap<>();

  protected SolverLessUFManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }
}
