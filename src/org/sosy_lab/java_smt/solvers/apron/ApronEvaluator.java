// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.apron;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractEvaluator;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;

public class ApronEvaluator extends AbstractEvaluator<ApronNode, ApronFormulaType, ApronModel> {

  private final ApronTheoremProver theoremProver;
  private ApronModel apronModel;

  protected ApronEvaluator(
      AbstractProver<?> pProver,
      FormulaCreator<ApronNode, ApronFormulaType, ApronModel, Long> creator)
      throws SolverException {
    super(pProver, creator);
    this.theoremProver = (ApronTheoremProver) pProver;
    this.apronModel = (ApronModel) theoremProver.getModel();
  }

  @Override
  protected @Nullable ApronNode evalImpl(ApronNode formula) {
    try {
      this.apronModel = (ApronModel) theoremProver.getModel();
      return apronModel.getValue(formula);
    } catch (SolverException e) {
      throw new RuntimeException(e);
    }
  }

  @Override
  public void close() {
    this.theoremProver.close();
    this.apronModel.close();
  }
}
