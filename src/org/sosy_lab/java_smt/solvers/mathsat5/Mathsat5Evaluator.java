// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_model_value;

import com.google.common.base.Preconditions;
import org.sosy_lab.java_smt.basicimpl.AbstractEvaluator;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;

/** This class requires an option for MathSAT: model_generation=true. TODO option does not work? */
class Mathsat5Evaluator extends AbstractEvaluator<Long, Long, Long> {

  private final long proverEnvironment;

  Mathsat5Evaluator(
      AbstractProver<?> prover, Mathsat5FormulaCreator creator, long pProverEnvironment) {
    super(prover, creator);
    proverEnvironment = pProverEnvironment;
  }

  @Override
  protected Long evalImpl(Long formula) {
    Preconditions.checkState(!isClosed());
    return msat_get_model_value(proverEnvironment, formula);
  }
}
