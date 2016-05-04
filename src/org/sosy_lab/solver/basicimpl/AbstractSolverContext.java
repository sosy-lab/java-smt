package org.sosy_lab.solver.basicimpl;

import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.InterpolatingProverEnvironmentWithAssumptions;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext;
import org.sosy_lab.solver.basicimpl.cache.CachingOptimizationProverEnvironment;
import org.sosy_lab.solver.basicimpl.cache.OptimizationQuery;
import org.sosy_lab.solver.basicimpl.cache.OptimizationResult;

import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public abstract class AbstractSolverContext implements SolverContext {

  private final FormulaManager fmgr;
  private final Map<OptimizationQuery, OptimizationResult> optimizationCache;
  private final SolverContextStatistics statistics;

  protected AbstractSolverContext(FormulaManager fmgr) {
    this.fmgr = fmgr;
    optimizationCache = new HashMap<>();
    statistics = new SolverContextStatistics();
  }

  @Override
  public final FormulaManager getFormulaManager() {
    return fmgr;
  }

  @Override
  public final ProverEnvironment newProverEnvironment(ProverOptions... options) {
    Set<ProverOptions> opts = EnumSet.noneOf(ProverOptions.class);
    Collections.addAll(opts, options);
    return newProverEnvironment0(opts);
  }

  protected abstract ProverEnvironment newProverEnvironment0(Set<ProverOptions> options);

  @SuppressWarnings("resource")
  @Override
  public final InterpolatingProverEnvironmentWithAssumptions<?>
      newProverEnvironmentWithInterpolation() {
    InterpolatingProverEnvironment<?> ipe = newProverEnvironmentWithInterpolation0();

    // In the case we do not already have a prover environment with assumptions
    // we add a wrapper to it
    InterpolatingProverEnvironmentWithAssumptions<?> out;
    if (!(ipe instanceof InterpolatingProverEnvironmentWithAssumptions)) {
      out = new InterpolatingProverWithAssumptionsWrapper<>(ipe, fmgr);
    } else {
      out = (InterpolatingProverEnvironmentWithAssumptions<?>) ipe;
    }
    return out;
  }

  protected abstract InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0();

  @Override
  public final OptimizationProverEnvironment newCachedOptimizationProverEnvironment() {
    return new CachingOptimizationProverEnvironment(
        newOptimizationProverEnvironment(),
        optimizationCache,
        statistics.getOptimizationCacheStatistics());
  }

  @Override
  public SolverContextStatistics getStatistics() {
    return statistics;
  }
}
