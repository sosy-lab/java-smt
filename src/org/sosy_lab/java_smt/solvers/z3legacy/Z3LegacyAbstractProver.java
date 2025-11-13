/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3legacy;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.io.MoreFiles;
import com.microsoft.z3legacy.Native;
import com.microsoft.z3legacy.Z3Exception;
import com.microsoft.z3legacy.enumerations.Z3_lbool;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.ShutdownNotifier.ShutdownRequestListener;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.CachingModel;

abstract class Z3LegacyAbstractProver<T> extends AbstractProverWithAllSat<T> {

  protected final long z3solver;
  protected final Z3LegacyFormulaCreator creator;
  protected final long z3context;
  protected final Z3LegacyFormulaManager mgr;
  private final ShutdownRequestListener interruptListener;

  private final UniqueIdGenerator trackId = new UniqueIdGenerator();
  private final Optional<Deque<PersistentMap<String, BooleanFormula>>> storedConstraints;

  private final Optional<PathCounterTemplate> logfile;

  Z3LegacyAbstractProver(
      Z3LegacyFormulaCreator pCreator,
      Z3LegacyFormulaManager pMgr,
      Set<ProverOptions> pOptions,
      @Nullable PathCounterTemplate pLogfile,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions, pMgr.getBooleanFormulaManager(), pShutdownNotifier);
    creator = pCreator;
    z3context = creator.getEnv();
    z3solver = Native.mkSolver(z3context);

    Native.solverIncRef(z3context, z3solver);

    interruptListener = reason -> Native.interrupt(z3context);
    shutdownNotifier.register(interruptListener);

    if (pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE)) {
      storedConstraints = Optional.of(new ArrayDeque<>());
      storedConstraints.get().push(PathCopyingPersistentTreeMap.of());
    } else {
      storedConstraints = Optional.empty();
    }

    logfile = Optional.ofNullable(pLogfile);
    mgr = pMgr;
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

  /** dump the current solver stack into a new SMTLIB file. */
  protected void logSolverStack() throws SolverException {
    if (logfile.isPresent()) { // if logging is not disabled
      try {
        // write stack content to logfile
        Path filename = logfile.get().getFreshPath();
        MoreFiles.createParentDirectories(filename);
        Files.writeString(filename, this + "(check-sat)\n");
      } catch (IOException e) {
        throw new SolverException("Cannot write Z3 log file", e);
      }
    }
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return new CachingModel(getEvaluatorWithoutChecks());
  }

  @Override
  protected Z3LegacyModel getEvaluatorWithoutChecks() throws SolverException {
    return new Z3LegacyModel(this, z3context, getZ3Model(), creator);
  }

  protected long getZ3Model() {
    try {
      return Native.solverGetModel(z3context, z3solver);
    } catch (Z3Exception e) {
      throw creator.handleZ3ExceptionAsRuntimeException(e);
    }
  }

  @Override
  protected void pushImpl() {
    push0();
    try {
      Native.solverPush(z3context, z3solver);
    } catch (Z3Exception exception) {
      throw creator.handleZ3ExceptionAsRuntimeException(exception);
    }
  }

  @Override
  protected void popImpl() {
    Native.solverPop(z3context, z3solver, 1);
    pop0();
  }

  protected void assertContraint(long constraint) {
    Native.solverAssert(z3context, z3solver, constraint);
  }

  protected void assertContraintAndTrack(long constraint, long symbol) {
    Native.solverAssertAndTrack(z3context, z3solver, constraint, symbol);
  }

  @SuppressWarnings("unchecked")
  @Override
  protected T addConstraintImpl(BooleanFormula f) throws InterruptedException {
    Preconditions.checkState(!closed);
    long e = creator.extractInfo(f);
    try {
      if (storedConstraints.isPresent()) { // Unsat core generation is on.
        String varName = String.format("Z3_UNSAT_CORE_%d", trackId.getFreshId());
        BooleanFormula t = mgr.getBooleanFormulaManager().makeVariable(varName);
        assertContraintAndTrack(e, creator.extractInfo(t));
        storedConstraints.get().push(storedConstraints.get().pop().putAndCopy(varName, f));
      } else {
        assertContraint(e);
      }
    } catch (Z3Exception exception) {
      throw creator.handleZ3ExceptionAsRuntimeException(exception);
    }
    return (T) Long.valueOf(e);
  }

  protected void push0() {
    Preconditions.checkState(!closed);
    storedConstraints.ifPresent(pPersistentMaps -> pPersistentMaps.push(pPersistentMaps.peek()));
  }

  protected void pop0() {
    Preconditions.checkState(!closed);
    storedConstraints.ifPresent(Deque::pop);
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
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

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
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

  private void undefinedStatusToException(int solverStatus)
      throws SolverException, InterruptedException {
    if (solverStatus == Z3_lbool.Z3_L_UNDEF.toInt()) {
      creator.shutdownNotifier.shutdownIfNecessary();
      final String reason = Native.solverGetReasonUnknown(z3context, z3solver);
      switch (reason) {
        case "canceled": // see Z3: src/tactic/tactic.cpp
        case "interrupted": // see Z3: src/solver/check_sat_result.cpp
        case "interrupted from keyboard": // see Z3: src/solver/check_sat_result.cpp
          throw new InterruptedException(reason);
        default:
          throw new SolverException("Z3 returned 'unknown' status, reason: " + reason);
      }
    }
  }

  protected long getUnsatCore0() {
    return Native.solverGetUnsatCore(z3context, z3solver);
  }

  // This method is used to get the Z3 proof as a long for testing exclusively
  long getZ3Proof() {
    return Native.solverGetProof(z3context, z3solver);
  }

  // This method is used to get the Z3 solver object for testing exclusively
  long getZ3solver() {
    return z3solver;
  }

  @Override
  public int size() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(
        Native.solverGetNumScopes(z3context, z3solver) == super.size(),
        "prover-size %s does not match stack-size %s",
        Native.solverGetNumScopes(z3context, z3solver),
        super.size());
    return super.size();
  }

  protected long getStatistics0() {
    return Native.solverGetStatistics(z3context, z3solver);
  }

  @Override
  public String toString() {
    Preconditions.checkState(!closed);
    return Native.solverToString(z3context, z3solver);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    if (storedConstraints.isEmpty()) {
      throw new UnsupportedOperationException(
          "Option to generate the UNSAT core wasn't enabled when creating the prover environment.");
    }

    List<BooleanFormula> constraints = new ArrayList<>();
    long unsatCore = getUnsatCore0();
    Native.astVectorIncRef(z3context, unsatCore);
    for (int i = 0; i < Native.astVectorSize(z3context, unsatCore); i++) {
      long ast = Native.astVectorGet(z3context, unsatCore, i);
      Native.incRef(z3context, ast);
      String varName = Native.astToString(z3context, ast);
      Native.decRef(z3context, ast);
      constraints.add(storedConstraints.get().peek().get(varName));
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
    long unsatCore = getUnsatCore0();
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

    final long stats = getStatistics0();
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

  protected Deque<PersistentMap<String, BooleanFormula>> getStoredConstraints() {
    return storedConstraints.orElseThrow();
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
      storedConstraints.ifPresent(Collection::clear);
    }
    super.close();
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
}
