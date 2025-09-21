// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_model;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_eval;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

class Mathsat5Model extends AbstractModel<Long, Long, Long> {

  private final long model;

  /** for detecting closed environments, Exception is better than SegFault. */
  private final Mathsat5AbstractProver<?> prover;

  private final ImmutableList<ValueAssignment> assignments;

  Mathsat5Model(
      FormulaManager pFormulaManager,
      long pModel,
      Mathsat5FormulaCreator pCreator,
      Mathsat5AbstractProver<?> pProver) {
    super(pFormulaManager, pProver, pCreator);
    model = pModel;
    prover = pProver;

    assignments = super.asList();
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return assignments;
  }

  @Override
  public void close() {
    if (!isClosed()) {
      msat_destroy_model(model);
    }
    super.close();
  }

  @Override
  protected Long evalImpl(Long formula) {
    Preconditions.checkState(!isClosed());
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    return msat_model_eval(model, formula);
  }
}
