package org.sosy_lab.solver.api;

import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;

/**
 * Interface which operates over {@link IntegerFormula}s.
 *
 * <p>Integer formulas always take integral formulas as arguments.
 */
public interface IntegerFormulaManager
  extends NumeralFormulaManager<IntegerFormula, IntegerFormula> {
}
