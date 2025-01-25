// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Joiner;
import java.util.Iterator;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractModel<TFormulaInfo, TType, TEnv>
    extends AbstractEvaluator<TFormulaInfo, TType, TEnv> implements Model {

  protected AbstractModel(
      AbstractProver<?> prover, FormulaCreator<TFormulaInfo, TType, TEnv, ?> creator) {
    super(prover, creator);
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    return getModelIterator();
  }

  /**
   * Returns an iterator for a solvers model. Only implement this method if you can guarantee a
   * truly iterative model evaluation with this iterator!
   *
   * @return a {@link ModelIterator} for a specific solver that is capable of iteratively evaluating
   *     the model of the solver.
   * @throws RuntimeException with wrapped {@link SolverException} or {@link InterruptedException},
   *     as the iterator does not allow exceptions.
   */
  protected ModelIterator getModelIterator() {
    throw new UnsupportedOperationException("Iterative model not supported for the chosen solver.");
  }

  @Override
  public String toString() {
    return Joiner.on('\n').join(iterator());
  }

  public interface ModelIterator extends Iterator<ValueAssignment> {

    @Override
    boolean hasNext();

    @Override
    ValueAssignment next();
  }
}
