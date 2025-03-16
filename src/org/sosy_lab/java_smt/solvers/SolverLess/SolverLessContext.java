// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.Set;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.solvers.z3.Z3SolverContext;

public final class SolverLessContext extends AbstractSolverContext {

  Solvers usedSolverForSMTSolving;
  Z3SolverContext usedSolverForZ3Solving;

  private SolverLessContext(SolverLessFormulaManager pManager) {
    super(pManager);
  }

  public static SolverLessContext create(Solvers usedSolverForActualSMTSolving) {
    SolverLessFormulaCreator creator = new SolverLessFormulaCreator();
    SolverLessBooleanFormulaManager bmgr = new SolverLessBooleanFormulaManager(creator);
    SolverLessFormulaManager manager = new SolverLessFormulaManager(creator, bmgr);
    SolverLessContext result = new SolverLessContext(manager);
    result.setUsedSolverForSMTSolving(usedSolverForActualSMTSolving);
    return result;
  }

  @Override
  public String getVersion() {
    return "SolverLess 1.0. Please note that this Solver has no SMT-Solving capabilities. It is "
        + "only used for SMTLIB2 generating.";
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.SOLVERLESS;
  }

  public Solvers getUsedSolverForSMTSolving() {
    return usedSolverForSMTSolving;
  }

  public void setUsedSolverForSMTSolving(Solvers pUsedSolverForSMTSolving) {
    usedSolverForSMTSolving = pUsedSolverForSMTSolving;
  }

  @Override
  public ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new SolverlessProverEnvironment(this, pOptions);
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pOptions) {
    throw new UnsupportedOperationException("SolverLess does not support interpolation.");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pOptions) {
    throw new UnsupportedOperationException("SolverLess does not support optimization.");
  }

  @Override
  public void close() {}
}
