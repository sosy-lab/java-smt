package org.sosy_lab.java_smt.solvers.SolverLess;

import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;


public class SolverLessUFManager
    extends AbstractUFManager<DummyFormula, DummyFunction, FormulaTypesForChecking, DummyEnv> {

  protected SolverLessUFManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }
}
