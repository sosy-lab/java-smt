/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.base.Preconditions.checkState;

import org.jspecify.annotations.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractEvaluator;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.TermManager;

class BitwuzlaEvaluator extends AbstractEvaluator<Term, Sort, TermManager> {
  private final BitwuzlaAbstractProver<?> prover;

  protected BitwuzlaEvaluator(
      BitwuzlaAbstractProver<?> pProver, FormulaCreator<Term, Sort, TermManager, ?> creator) {
    super(pProver, creator);
    prover = pProver;
  }

  @Override
  protected @Nullable Term evalImpl(Term formula) {
    checkState(!isClosed());
    checkState(!prover.isClosed(), "Cannot use model after prover is closed");
    return prover.env.get_value(formula);
  }
}
