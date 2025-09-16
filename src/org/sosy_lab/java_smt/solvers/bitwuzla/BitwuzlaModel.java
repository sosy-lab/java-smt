// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.common.base.Preconditions;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Bitwuzla;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;

class BitwuzlaModel extends AbstractModel<Term, Sort, Void> {

  // The prover env, not the creator env!
  private final Bitwuzla bitwuzlaEnv;

  private final BitwuzlaTheoremProver prover;

  protected BitwuzlaModel(
      Bitwuzla bitwuzlaEnv,
      BitwuzlaTheoremProver prover,
      BitwuzlaFormulaCreator bitwuzlaCreator,
      BitwuzlaFormulaManager bitwuzlaFormulaManager) {
    super(bitwuzlaFormulaManager, prover, bitwuzlaCreator);
    this.bitwuzlaEnv = bitwuzlaEnv;
    this.prover = prover;
  }

  @Override
  protected @Nullable Term evalImpl(Term formula) {
    Preconditions.checkState(!prover.isClosed(), "Cannot use model after prover is closed");
    return bitwuzlaEnv.get_value(formula);
  }
}
