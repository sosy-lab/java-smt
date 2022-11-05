// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.api.SimpleAPI;
import ap.parser.IExpression;
import ap.parser.IFormula;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class PrincessTheoremProver extends PrincessAbstractProver<Void, IExpression>
    implements ProverEnvironment {

  PrincessTheoremProver(
      PrincessFormulaManager pMgr,
      PrincessFormulaCreator creator,
      SimpleAPI pApi,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions) {
    super(pMgr, creator, pApi, pShutdownNotifier, pOptions);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    final IFormula t = (IFormula) mgr.extractInfo(constraint);
    final int formulaId = addAssertedFormula(t);
    if (generateUnsatCores) {
      api.setPartitionNumber(formulaId);
    }
    addConstraint0(t);
    return null;
  }

  @Override
  protected Iterable<IExpression> getAssertedFormulas() {
    return Iterables.concat(assertedFormulas);
  }
}
