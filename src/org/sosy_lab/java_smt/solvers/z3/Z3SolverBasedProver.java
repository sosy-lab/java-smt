/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.z3;

import static org.sosy_lab.java_smt.solvers.z3.Z3FormulaCreator.isOP;

import com.google.common.base.Preconditions;
import com.google.common.base.VerifyException;
import com.google.common.collect.ImmutableList;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_lbool;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import javax.annotation.Nullable;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.LongArrayBackedList;

abstract class Z3SolverBasedProver<T> implements BasicProverEnvironment<T> {

  protected final Z3FormulaCreator creator;
  protected final long z3context;
  private final FormulaManager mgr;

  protected boolean closed = false;

  protected final long z3solver;

  private int level = 0;

  private static final String UNSAT_CORE_TEMP_VARNAME = "Z3_UNSAT_CORE_%d";
  private final UniqueIdGenerator trackId = new UniqueIdGenerator();
  private final @Nullable Map<String, BooleanFormula> storedConstraints;

  Z3SolverBasedProver(
      Z3FormulaCreator pCreator, long z3params, FormulaManager pMgr, boolean enableUnsatCores) {
    creator = pCreator;
    z3context = creator.getEnv();
    z3solver = Native.mkSolver(z3context);
    mgr = pMgr;
    Native.solverIncRef(z3context, z3solver);
    Native.solverSetParams(z3context, z3solver, z3params);
    storedConstraints = enableUnsatCores ? new HashMap<>() : null;
  }

  @Override
  public boolean isUnsat() throws Z3SolverException, InterruptedException {
    Preconditions.checkState(!closed);
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
  public Z3Model getModel() {
    Preconditions.checkState(!closed);
    return Z3Model.create(z3context, getZ3Model(), creator);
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(!closed);
    try (Z3Model model = getModel()) {
      return model.modelToList();
    }
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
        String varName = String.format(UNSAT_CORE_TEMP_VARNAME, trackId.getFreshId());
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
    level++;
    Native.solverPush(z3context, z3solver);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(Native.solverGetNumScopes(z3context, z3solver) >= 1);
    level--;
    Native.solverPop(z3context, z3solver, 1);
  }

  protected int getLevel() {
    return level;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
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
  public void close() {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(
        Native.solverGetNumScopes(z3context, z3solver) >= 0,
        "a negative number of scopes is not allowed");

    while (level > 0) {
      pop();
    }
    Native.solverDecRef(z3context, z3solver);

    closed = true;
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
    Preconditions.checkState(!closed);

    // Unpack formulas to terms.
    long[] importantFormulas = new long[important.size()];
    int i = 0;
    for (BooleanFormula impF : important) {
      importantFormulas[i++] = Z3FormulaManager.getZ3Expr(impF);
    }

    try {
      push();
    } catch (Z3Exception e) {
      throw creator.handleZ3Exception(e);
    }

    while (!isUnsat()) {
      long[] valuesOfModel = new long[importantFormulas.length];
      long z3model = getZ3Model();

      for (int j = 0; j < importantFormulas.length; j++) {
        long funcDecl = Native.getAppDecl(z3context, importantFormulas[j]);
        long valueOfExpr = Native.modelGetConstInterp(z3context, z3model, funcDecl);
        if (valueOfExpr == 0) {
          // In theory, this is a legal return value for modelGetConstInterp and means
          // that the value doesn't matter.
          // However, we have never seen this value so far except in case of shutdowns.
          creator.shutdownNotifier.shutdownIfNecessary();
          // If it ever happens in a legitimate usecase, we need to remove the following
          // exception and handle it by passing a partial model to the callback.
          throw new VerifyException(
              "Z3 claims that the value of "
                  + Native.astToString(z3context, importantFormulas[j])
                  + " does not matter in allSat call.");
        }

        if (isOP(z3context, valueOfExpr, Z3_decl_kind.Z3_OP_FALSE.toInt())) {
          valuesOfModel[j] = Native.mkNot(z3context, importantFormulas[j]);
          Native.incRef(z3context, valuesOfModel[j]);
        } else {
          valuesOfModel[j] = importantFormulas[j];
        }
      }

      callback.apply(
          new LongArrayBackedList<BooleanFormula>(valuesOfModel) {
            @Override
            protected BooleanFormula convert(long pE) {
              return creator.encapsulateBoolean(pE);
            }
          });

      try {
        long negatedModel =
            Native.mkNot(z3context, Native.mkAnd(z3context, valuesOfModel.length, valuesOfModel));
        Native.incRef(z3context, negatedModel);
        assertContraint(negatedModel);
      } catch (Z3Exception e) {
        throw creator.handleZ3Exception(e);
      }
    }

    // we pushed some levels on assertionStack, remove them and delete solver
    pop();
    return callback.getResult();
  }

  protected void assertContraint(long negatedModel) {
    Native.solverAssert(z3context, z3solver, negatedModel);
  }
}
