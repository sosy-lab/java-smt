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
package org.sosy_lab.solver.z3java;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext.ProverOptions;
import org.sosy_lab.solver.basicimpl.Model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.Nullable;

class Z3TheoremProver extends Z3AbstractProver<Void> implements ProverEnvironment {

  private final ShutdownNotifier shutdownNotifier;
  private final Solver z3solver;
  private int level = 0;
  private final UniqueIdGenerator trackId = new UniqueIdGenerator();
  private final FormulaManager mgr;

  private static final String UNSAT_CORE_TEMP_VARNAME = "UNSAT_CORE_%d";

  private final @Nullable Map<String, BooleanFormula> storedConstraints;

  Z3TheoremProver(
      Z3FormulaCreator creator,
      Z3FormulaManager pMgr,
      Params z3params,
      ShutdownNotifier pShutdownNotifier,
      ProverOptions... options) {
    super(creator);
    mgr = pMgr;
    z3solver = z3context.mkSolver();
    z3solver.setParameters(z3params);
    Set<ProverOptions> opts = Sets.newHashSet(options);
    if (opts.contains(ProverOptions.GENERATE_UNSAT_CORE)) {
      storedConstraints = new HashMap<>();
    } else {
      storedConstraints = null;
    }
    shutdownNotifier = pShutdownNotifier;
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(z3solver.getNumScopes() >= 1);
    level--;
    z3solver.pop();
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    BoolExpr e = (BoolExpr)Z3FormulaManager.getZ3Expr(f);

    if (storedConstraints != null) { // Unsat core generation is on.
      String varName = String.format(UNSAT_CORE_TEMP_VARNAME, trackId.getFreshId());
      BooleanFormula t = mgr.getBooleanFormulaManager().makeVariable(varName);

      z3solver.assertAndTrack(e, (BoolExpr)creator.extractInfo(t));
      storedConstraints.put(varName, f);
    } else {
      z3solver.add(e);
    }
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    level++;
    z3solver.push();
  }

  @Override
  public boolean isUnsat() throws Z3SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    Status result = z3solver.check();
    shutdownNotifier.shutdownIfNecessary();
    Preconditions.checkArgument(result != Status.UNKNOWN);
    return result == Status.UNSATISFIABLE;
  }

  @Override
  protected com.microsoft.z3.Model getZ3Model() {
    return z3solver.getModel();
  }

  @Override
  public Model getModel() {
    Preconditions.checkState(!closed);
    return new Z3Model(z3context, getZ3Model(), creator);
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
    BoolExpr[] unsatCore = z3solver.getUnsatCore();
    for (BoolExpr ast : unsatCore) {
      String varName = ast.toString();
      constraints.add(storedConstraints.get(varName));
    }
    return constraints;
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(z3solver.getNumScopes() >= 0,
        "a negative number of scopes is not allowed");

    while (level > 0) {
      pop();
    }

    closed = true;
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    // Unpack formulas to terms.
    BoolExpr[] importantFormulas = new BoolExpr[important.size()];
    int i = 0;
    for (BooleanFormula impF : important) {
      importantFormulas[i++] = (BoolExpr)Z3FormulaManager.getZ3Expr(impF);
    }

    z3solver.push();

    while (z3solver.check() == Status.SATISFIABLE) {
      BoolExpr[] valuesOfModel = new BoolExpr[importantFormulas.length];
      com.microsoft.z3.Model z3model = z3solver.getModel();

      for (int j = 0; j < importantFormulas.length; j++) {
        BoolExpr valueOfExpr = (BoolExpr) z3model.getConstInterp(importantFormulas[j]);

        if (valueOfExpr.isFalse()) {
          valuesOfModel[j] = z3context.mkNot(importantFormulas[j]);
        } else {
          valuesOfModel[j] = importantFormulas[j];
        }
      }

      callback.apply(Lists.transform(Arrays.asList(valuesOfModel), creator.encapsulateBoolean));

      BoolExpr negatedModel = z3context.mkNot(z3context.mkAnd(valuesOfModel));
      z3solver.add(negatedModel);
    }

    // we pushed some levels on assertionStack, remove them and delete solver
    z3solver.pop();
    return callback.getResult();
  }
}
