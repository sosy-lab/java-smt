// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Long, Long, Long, BitwuzlaDeclaration> {

  protected BitwuzlaQuantifiedFormulaManager(
      FormulaCreator<Long, Long, Long, BitwuzlaDeclaration> pCreator) {
    super(pCreator);
  }

  @Override
  protected Long eliminateQuantifiers(Long pExtractInfo)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Bitwuzla does not support eliminating Quantifiers.");
  }

  @Override
  public Long mkQuantifier(Quantifier q, List<Long> vars, Long body) {
    // While substitution is possible, it changes existing formulas! We don't want this and ask
    // the devs for a new method that returns a new term with the substitution applied.
    throw new UnsupportedOperationException("Bitwuzla does not support Quantifiers in JavaSMT.");
    /*
    long[] argsAndBody =
        LongStream.concat(vars.stream().mapToLong(Long::longValue), LongStream.of(body)).toArray();
    if (q.equals(Quantifier.FORALL)) {
      return bitwuzlaJNI.bitwuzla_mk_term(
          BitwuzlaKind.BITWUZLA_KIND_FORALL.swigValue(), argsAndBody.length, argsAndBody);
    } else {
      return bitwuzlaJNI.bitwuzla_mk_term(
          BitwuzlaKind.BITWUZLA_KIND_EXISTS.swigValue(), argsAndBody.length, argsAndBody);
    }
    */
  }
}
