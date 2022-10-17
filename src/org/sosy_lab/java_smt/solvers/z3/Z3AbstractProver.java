// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.io.MoreFiles;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_lbool;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.ShutdownNotifier.ShutdownRequestListener;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.CachingModel;

abstract class Z3AbstractProver<T> extends AbstractProverWithAllSat<T> {

  protected final Z3FormulaCreator creator;
  protected final long z3context;
  private final Z3FormulaManager mgr;

  protected final long z3solver;

  private final UniqueIdGenerator trackId = new UniqueIdGenerator();
  private final @Nullable Map<String, BooleanFormula> storedConstraints;

  private final @Nullable PathCounterTemplate logfile;

  private final ShutdownRequestListener interruptListener;

  Z3AbstractProver(
      Z3FormulaCreator pCreator,
      Z3FormulaManager pMgr,
      Set<ProverOptions> pOptions,
      ImmutableMap<String, Object> pSolverOptions,
      @Nullable PathCounterTemplate pLogfile,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions, pMgr.getBooleanFormulaManager(), pShutdownNotifier);
    creator = pCreator;
    z3context = creator.getEnv();
    z3solver = Native.mkSolver(z3context);

    interruptListener = reason -> Native.solverInterrupt(z3context, z3solver);
    shutdownNotifier.register(interruptListener);
    storedConstraints =
        pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE) ? new HashMap<>() : null;

    logfile = pLogfile;
    mgr = pMgr;
    Native.solverIncRef(z3context, z3solver);

    long z3params = Native.mkParams(z3context);
    Native.paramsIncRef(z3context, z3params);
    for (Entry<String, Object> entry : pSolverOptions.entrySet()) {
      addParameter(z3params, entry.getKey(), entry.getValue());
    }
    Native.solverSetParams(z3context, z3solver, z3params);
    Native.paramsDecRef(z3context, z3params);
  }

  void addParameter(long z3params, String key, Object value) {
    long keySymbol = Native.mkStringSymbol(z3context, key);
    if (value instanceof Boolean) {
      Native.paramsSetBool(z3context, z3params, keySymbol, (Boolean) value);
    } else if (value instanceof Integer) {
      Native.paramsSetUint(z3context, z3params, keySymbol, (Integer) value);
    } else if (value instanceof Double) {
      Native.paramsSetDouble(z3context, z3params, keySymbol, (Double) value);
    } else if (value instanceof String) {
      long valueSymbol = Native.mkStringSymbol(z3context, (String) value);
      Native.paramsSetSymbol(z3context, z3params, keySymbol, valueSymbol);
    } else {
      throw new IllegalArgumentException(
          String.format(
              "unexpected type '%s' with value '%s' for parameter '%s'",
              value.getClass(), value, key));
    }
  }

  @Override
  public boolean isUnsat() throws Z3SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    logSolverStack();
    int result;
    try {
      result = Native.solverCheck(z3context, z3solver);
    } catch (Z3Exception e) {
      throw creator.handleZ3Exception(e);
    }
    undefinedStatusToException(result);
    return result == Z3_lbool.Z3_L_FALSE.toInt();
  }

  /** dump the current solver stack into a new SMTLIB file. */
  private void logSolverStack() throws Z3SolverException {
    if (logfile != null) { // if logging is not disabled
      try {
        // write stack content to logfile
        Path filename = logfile.getFreshPath();
        MoreFiles.createParentDirectories(filename);
        Files.writeString(filename, Native.solverToString(z3context, z3solver) + "(check-sat)\n");
      } catch (IOException e) {
        throw new Z3SolverException("Cannot write Z3 log file: " + e.getMessage());
      }
    }
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws Z3SolverException, InterruptedException {
    Preconditions.checkState(!closed);

    int result;
    try {
      result =
          Native.solverCheckAssumptions(
              z3context,
              z3solver,
              assumptions.size(),
              assumptions.stream().mapToLong(creator::extractInfo).toArray());
    } catch (Z3Exception e) {
      throw creator.handleZ3Exception(e);
    }
    undefinedStatusToException(result);
    return result == Z3_lbool.Z3_L_FALSE.toInt();
  }

  protected final void undefinedStatusToException(int solverStatus)
      throws Z3SolverException, InterruptedException {
    if (solverStatus == Z3_lbool.Z3_L_UNDEF.toInt()) {
      creator.shutdownNotifier.shutdownIfNecessary();
      throw new Z3SolverException(
          "Solver returned 'unknown' status, reason: "
              + Native.solverGetReasonUnknown(z3context, z3solver));
    }
  }

  @Override
  public Model getModel() {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return new CachingModel(new Z3Model(this, z3context, getZ3Model(), creator));
  }

  protected long getZ3Model() {
    return Native.solverGetModel(z3context, z3solver);
  }

  @CanIgnoreReturnValue
  protected long addConstraint0(BooleanFormula f) throws InterruptedException {
    Preconditions.checkState(!closed);
    long e = creator.extractInfo(f);
    Native.incRef(z3context, e);
    try {
      if (storedConstraints != null) { // Unsat core generation is on.
        String varName = String.format("Z3_UNSAT_CORE_%d", trackId.getFreshId());
        BooleanFormula t = mgr.getBooleanFormulaManager().makeVariable(varName);

        Native.solverAssertAndTrack(z3context, z3solver, e, creator.extractInfo(t));
        storedConstraints.put(varName, f);
        Native.decRef(z3context, e);
      } else {
        assertContraint(e);
      }
    } catch (Z3Exception exception) {
      throw creator.handleZ3Exception(exception);
    }
    Native.decRef(z3context, e);

    return e;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    Native.solverPush(z3context, z3solver);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(Native.solverGetNumScopes(z3context, z3solver) >= 1);
    Native.solverPop(z3context, z3solver, 1);
  }

  @Override
  public int size() {
    Preconditions.checkState(!closed);
    return Native.solverGetNumScopes(z3context, z3solver);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    if (storedConstraints == null) {
      throw new UnsupportedOperationException(
          "Option to generate the UNSAT core wasn't enabled when creating the prover environment.");
    }

    List<BooleanFormula> constraints = new ArrayList<>();
    long unsatCore = Native.solverGetUnsatCore(z3context, z3solver);
    Native.astVectorIncRef(z3context, unsatCore);
    for (int i = 0; i < Native.astVectorSize(z3context, unsatCore); i++) {
      long ast = Native.astVectorGet(z3context, unsatCore, i);
      Native.incRef(z3context, ast);
      String varName = Native.astToString(z3context, ast);
      Native.decRef(z3context, ast);
      constraints.add(storedConstraints.get(varName));
    }
    Native.astVectorDecRef(z3context, unsatCore);
    return constraints;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    checkGenerateUnsatCoresOverAssumptions();
    if (!isUnsatWithAssumptions(assumptions)) {
      return Optional.empty();
    }
    List<BooleanFormula> core = new ArrayList<>();
    long unsatCore = Native.solverGetUnsatCore(z3context, z3solver);
    Native.astVectorIncRef(z3context, unsatCore);
    for (int i = 0; i < Native.astVectorSize(z3context, unsatCore); i++) {
      long ast = Native.astVectorGet(z3context, unsatCore, i);
      core.add(creator.encapsulateBoolean(ast));
    }
    Native.astVectorDecRef(z3context, unsatCore);
    return Optional.of(core);
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    // Z3 sigsevs if you try to get statistics for closed environments
    Preconditions.checkState(!closed);

    ImmutableMap.Builder<String, String> builder = ImmutableMap.builder();
    Set<String> seenKeys = new HashSet<>();

    final long stats = Native.solverGetStatistics(z3context, z3solver);
    for (int i = 0; i < Native.statsSize(z3context, stats); i++) {
      String key = getUnusedKey(seenKeys, Native.statsGetKey(z3context, stats, i));
      if (Native.statsIsUint(z3context, stats, i)) {
        builder.put(key, Integer.toString(Native.statsGetUintValue(z3context, stats, i)));
      } else if (Native.statsIsDouble(z3context, stats, i)) {
        builder.put(key, Double.toString(Native.statsGetDoubleValue(z3context, stats, i)));
      } else {
        throw new IllegalStateException(
            String.format(
                "Unknown data entry value for key %s at position %d in statistics '%s'",
                key, i, Native.statsToString(z3context, stats)));
      }
    }

    return builder.buildOrThrow();
  }

  /**
   * In some cases, Z3 uses the same statistics key twice. In those cases, we append an index to the
   * second usage.
   */
  private String getUnusedKey(Set<String> seenKeys, final String originalKey) {
    if (seenKeys.add(originalKey)) {
      return originalKey;
    }
    String key;
    int index = 0;
    do {
      index++;
      key = originalKey + " (" + index + ")";
    } while (!seenKeys.add(key));
    return key;
  }

  @Override
  public void close() {
    if (!closed) {
      Preconditions.checkArgument(
          Native.solverGetNumScopes(z3context, z3solver) >= 0,
          "a negative number of scopes is not allowed");

      Native.solverReset(z3context, z3solver); // remove all assertions from the solver
      Native.solverDecRef(z3context, z3solver);

      shutdownNotifier.unregister(interruptListener);

      closed = true;
    }
  }

  @Override
  public String toString() {
    if (closed) {
      return "Closed Z3Solver";
    }
    return Native.solverToString(z3context, z3solver);
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    try {
      return super.allSat(callback, important);
    } catch (Z3Exception e) {
      throw creator.handleZ3Exception(e);
    }
  }

  protected void assertContraint(long negatedModel) {
    Native.solverAssert(z3context, z3solver, negatedModel);
  }
}
