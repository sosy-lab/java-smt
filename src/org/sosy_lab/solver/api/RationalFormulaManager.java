package org.sosy_lab.solver.api;

import org.sosy_lab.solver.api.NumeralFormula.RationalFormula;

/**
 * Interface for operating over {@link RationalFormula}.
 *
 * <p>Rational formulas may take both integral and rational formulas as arguments.
 */
public interface RationalFormulaManager
    extends NumeralFormulaManager<NumeralFormula, RationalFormula> {

  @Override
  default FormulaType<RationalFormula> getFormulaType() {
    return FormulaType.RationalType;
  }
}
