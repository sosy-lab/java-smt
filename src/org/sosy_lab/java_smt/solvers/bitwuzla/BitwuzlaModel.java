package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.common.collect.ImmutableList;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaModel extends AbstractModel<Long, Long, Long> {
  protected BitwuzlaModel(
      AbstractProver<?> prover,
      FormulaCreator<Long, Long, Long, ?> creator) {
    super(prover, creator);
  }

  /**
   * Build a list of assignments that stays valid after closing the model.
   */
  @Override
  public ImmutableList<ValueAssignment> asList() {
    return null;
  }

  /**
   * Simplify the given formula and replace all symbols with their model values. If a symbol is not
   * set in the model and evaluation aborts, return <code>null</code>.
   *
   * @param formula
   */
  @Override
  protected @Nullable Long evalImpl(Long formula) {
    return null;
  }
}
