/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.z3;

import static org.sosy_lab.solver.z3.Z3FormulaCreator.isOP;

import com.google.common.base.Optional;
import com.google.common.base.Preconditions;
import com.microsoft.z3.Native;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_lbool;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext.ProverOptions;
import org.sosy_lab.solver.basicimpl.LongArrayBackedList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.Nullable;

class Z3TheoremProver extends Z3AbstractProver<Void> implements ProverEnvironment {

  private final long z3solver;
  private int level = 0;
  private final UniqueIdGenerator trackId = new UniqueIdGenerator();
  private final FormulaManager mgr;

  private static final String UNSAT_CORE_TEMP_VARNAME = "Z3_UNSAT_CORE_%d";

  private final @Nullable Map<String, BooleanFormula> storedConstraints;

  Z3TheoremProver(
      Z3FormulaCreator creator,
      Z3FormulaManager pMgr,
      long z3params,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> opts) {
    super(creator, pShutdownNotifier);
    mgr = pMgr;
    z3solver = Native.mkSolver(z3context);
    Native.solverIncRef(z3context, z3solver);
    Native.solverSetParams(z3context, z3solver, z3params);
    if (opts.contains(ProverOptions.GENERATE_UNSAT_CORE)) {
      storedConstraints = new HashMap<>();
    } else {
      storedConstraints = null;
    }
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(Native.solverGetNumScopes(z3context, z3solver) >= 1);
    level--;
    Native.solverPop(z3context, z3solver, 1);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    long e = Z3FormulaManager.getZ3Expr(f);
    Native.incRef(z3context, e);

    if (storedConstraints != null) { // Unsat core generation is on.
      String varName = String.format(UNSAT_CORE_TEMP_VARNAME, trackId.getFreshId());
      BooleanFormula t = mgr.getBooleanFormulaManager().makeVariable(varName);

      Native.solverAssertAndTrack(z3context, z3solver, e, creator.extractInfo(t));
      storedConstraints.put(varName, f);
    } else {
      Native.solverAssert(z3context, z3solver, e);
    }
    Native.decRef(z3context, e);
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    level++;
    Native.solverPush(z3context, z3solver);
  }

  @Override
  public boolean isUnsat() throws Z3SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    int result = Native.solverCheck(z3context, z3solver);
    undefinedStatusToException(result);
    return result == Z3_lbool.Z3_L_FALSE.toInt();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws Z3SolverException, InterruptedException {
    Preconditions.checkState(!closed);

    int result =
        Native.solverCheckAssumptions(
            z3context,
            z3solver,
            assumptions.size(),
            assumptions.stream().mapToLong(creator::extractInfo).toArray());
    undefinedStatusToException(result);
    return result == Z3_lbool.Z3_L_FALSE.toInt();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    if (!isUnsatWithAssumptions(assumptions)) {
      return Optional.absent();
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
  protected long getZ3Model() {
    return Native.solverGetModel(z3context, z3solver);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    if (storedConstraints == null) {
      throw new UnsupportedOperationException(
          "Option to generate the UNSAT core wasn't enabled when creating"
              + " the prover environment.");
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
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    // Unpack formulas to terms.
    long[] importantFormulas = new long[important.size()];
    int i = 0;
    for (BooleanFormula impF : important) {
      importantFormulas[i++] = Z3FormulaManager.getZ3Expr(impF);
    }

    Native.solverPush(z3context, z3solver);

    while (Native.solverCheck(z3context, z3solver) == Z3_lbool.Z3_L_TRUE.toInt()) {
      long[] valuesOfModel = new long[importantFormulas.length];
      long z3model = Native.solverGetModel(z3context, z3solver);

      for (int j = 0; j < importantFormulas.length; j++) {
        long funcDecl = Native.getAppDecl(z3context, importantFormulas[j]);
        long valueOfExpr = Native.modelGetConstInterp(z3context, z3model, funcDecl);

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

      long negatedModel =
          Native.mkNot(z3context, Native.mkAnd(z3context, valuesOfModel.length, valuesOfModel));
      Native.incRef(z3context, negatedModel);
      Native.solverAssert(z3context, z3solver, negatedModel);
    }

    // we pushed some levels on assertionStack, remove them and delete solver
    Native.solverPop(z3context, z3solver, 1);
    return callback.getResult();
  }

  @Override
  public String toString() {
    Preconditions.checkState(!closed);
    return Native.solverToString(z3context, z3solver);
  }

  private void undefinedStatusToException(int solverStatus) throws Z3SolverException {
    if (solverStatus == Z3_lbool.Z3_L_UNDEF.toInt()) {
      throw new Z3SolverException(
          "Solver returned 'unknown' status, reason: "
              + Native.solverGetReasonUnknown(z3context, z3solver));
    }
  }
}
