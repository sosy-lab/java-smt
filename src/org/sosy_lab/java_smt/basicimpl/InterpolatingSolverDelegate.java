/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.java_smt.basicimpl.IndependentInterpolatingSolverDelegate.generateTermName;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/** Delegate that wraps non-interpolating provers, allowing them to return itp tracking points. */
public class InterpolatingSolverDelegate extends AbstractProver<String>
    implements InterpolatingProverEnvironment<String> {

  private final BasicProverEnvironment<?> delegate;

  protected InterpolatingSolverDelegate(
      BasicProverEnvironment<?> pDelegate, Set<ProverOptions> pOptions) {
    super(checkNotNull(pOptions));
    // TODO: is the delegate also saving all info of AbstractProver additionally, or does VOID
    //  prevent that?
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<String> formulasOfA)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Solver does not support native interpolation.");
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<String>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(
        "Tree interpolants are currently not supported using " + "independent interpolation");
  }

  @Override
  protected void popImpl() {
    delegate.pop();
  }

  @Override
  protected String addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    checkState(!closed);
    delegate.addConstraint(constraint);
    String termName = generateTermName();
    return termName;
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    delegate.push();
  }

  @Override
  protected boolean hasPersistentModel() {
    return false;
  }

  @Override
  public int size() {
    return delegate.size();
  }

  @Override
  public boolean isUnsatImpl() throws SolverException, InterruptedException {
    return delegate.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return delegate.isUnsatWithAssumptions(assumptions);
  }

  @Override
  public Model getModel() throws SolverException {
    return delegate.getModel();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return delegate.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    return delegate.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    return delegate.allSat(callback, important);
  }
}
