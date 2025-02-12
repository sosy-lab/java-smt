package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

public class SolverLessUFManager
    extends AbstractUFManager<DummyFormula, DummyFunction, DummyType, DummyEnv> {

  protected SolverLessUFManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }
}
