package org.sosy_lab.solver.visitors;

import com.google.common.base.Function;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.util.List;

/**
 * Abstract class for formula transformation.
 *
 * @see org.sosy_lab.solver.api.FormulaManager#transformRecursively
 */
public abstract class FormulaTransformationVisitor implements FormulaVisitor<Formula> {

  private final FormulaManager fmgr;

  protected FormulaTransformationVisitor(FormulaManager fmgr) {
    this.fmgr = fmgr;
  }

  @Override
  public Formula visitFreeVariable(Formula f, String name) {
    return f;
  }

  /**
   * Bound variables can not be changed.
   */
  @Override
  public final Formula visitBoundVariable(Formula f, int deBruijnIdx) {
    return f;
  }

  @Override
  public Formula visitConstant(Formula f, Object value) {
    return f;
  }

  /**
   * @param f Input function.
   * @param newArgs New arguments <b>after</b> the transformation
   * @param functionDeclaration Function declaration
   * @param newApplicationConstructor Construct a new function of the same type,
   *
   * @return Transformed function.
   */
  @Override
  public Formula visitFunction(
      Formula f,
      List<Formula> newArgs,
      FunctionDeclaration functionDeclaration,
      Function<List<Formula>, Formula> newApplicationConstructor) {
    return newApplicationConstructor.apply(newArgs);
  }

  @Override
  public Formula visitQuantifier(BooleanFormula f,
                                 Quantifier quantifier,
                                 List<Formula> boundVariables,
                                 BooleanFormula body) {
    return fmgr.getQuantifiedFormulaManager().mkQuantifier(
        quantifier,
        boundVariables,
        body
    );
  }
}
