// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.io.MoreFiles;
import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;
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

abstract class Z3AbstractProver extends AbstractProverWithAllSat<Void> {

  protected final Z3FormulaCreator creator;
  protected final long z3context;
  protected final Z3FormulaManager mgr;

  private final UniqueIdGenerator trackId = new UniqueIdGenerator();
  @Nullable private final Deque<PersistentMap<String, BooleanFormula>> storedConstraints;

  private final @Nullable PathCounterTemplate logfile;

  Z3AbstractProver(
      Z3FormulaCreator pCreator,
      Z3FormulaManager pMgr,
      Set<ProverOptions> pOptions,
      @Nullable PathCounterTemplate pLogfile,
      ShutdownNotifier pContextShutdownNotifier,
      @Nullable ShutdownNotifier pProverShutdownNotifier) {
    super(
        pOptions,
        pMgr.getBooleanFormulaManager(),
        pContextShutdownNotifier,
        pProverShutdownNotifier);
    creator = pCreator;
    z3context = creator.getEnv();

    if (pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE)) {
      storedConstraints = new ArrayDeque<>();
      storedConstraints.push(PathCopyingPersistentTreeMap.of());
    } else {
      storedConstraints = null; // we use NULL as flag for "no unsat-core"
    }

    logfile = pLogfile;
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
    if (logfile != null) { // if logging is not disabled
      try {
        // write stack content to logfile
        Path filename = logfile.getFreshPath();
        MoreFiles.createParentDirectories(filename);
        Files.writeString(filename, this + "(check-sat)\n");
      } catch (IOException e) {
        throw new SolverException("Cannot write Z3 log file", e);
      }
    }
  }

  @SuppressWarnings("resource")
  @Override
  protected Model getModelImpl() throws SolverException {
    checkGenerateModels();
    return new CachingModel(getEvaluatorWithoutChecks());
  }

  @Override
  protected Z3Model getEvaluatorWithoutChecks() throws SolverException {
    return new Z3Model(this, z3context, getZ3Model(), creator);
  }

  protected abstract long getZ3Model() throws SolverException;

  protected abstract void assertContraint(long constraint);

  protected abstract void assertContraintAndTrack(long constraint, long symbol);

  @Override
  protected Void addConstraintImpl(BooleanFormula f) throws InterruptedException {
    Preconditions.checkState(!closed);
    long e = creator.extractInfo(f);
    try {
      if (storedConstraints != null) { // Unsat core generation is on.
        String varName = String.format("Z3_UNSAT_CORE_%d", trackId.getFreshId());
        BooleanFormula t = mgr.getBooleanFormulaManager().makeVariable(varName);
        assertContraintAndTrack(e, creator.extractInfo(t));
        storedConstraints.push(storedConstraints.pop().putAndCopy(varName, f));
      } else {
        assertContraint(e);
      }
    } catch (Z3Exception exception) {
      throw creator.handleZ3ExceptionAsRuntimeException(exception, proverShutdownNotifier);
    }
    return null;
  }

  protected void push0() {
    Preconditions.checkState(!closed);
    if (storedConstraints != null) {
      storedConstraints.push(storedConstraints.peek());
    }
  }

  protected void pop0() {
    Preconditions.checkState(!closed);
    if (storedConstraints != null) {
      storedConstraints.pop();
    }
  }

  protected abstract long getUnsatCore0();

  @Override
  protected List<BooleanFormula> getUnsatCoreImpl() {
    if (storedConstraints == null) {
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
      constraints.add(storedConstraints.peek().get(varName));
    }
    Native.astVectorDecRef(z3context, unsatCore);
    return constraints;
  }

  @Override
  protected Optional<List<BooleanFormula>> unsatCoreOverAssumptionsImpl(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
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

  protected abstract long getStatistics0();

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

  @Override
  public void close() {
    if (!closed) {
      if (storedConstraints != null) {
        storedConstraints.clear();
      }
    }
    super.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    try {
      return super.allSat(callback, important);
    } catch (Z3Exception e) {
      throw creator.handleZ3Exception(e, proverShutdownNotifier);
    }
  }
}
