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
    long[] origVars = new long[vars.size()];
    long[] substVars = new long[vars.size()];
    long[] argsAndBody = new long[vars.size() + 1];
    for (int i = 0; i < vars.size(); i++) {
      long var = vars.get(i);
      origVars[i] = var;
      // Create/Use bound vars
      long boundCopy = ((BitwuzlaFormulaCreator) formulaCreator).makeBoundVariable(var);
      substVars[i] = boundCopy;
      argsAndBody[i + 1] = boundCopy;
    }
    long substBody = BitwuzlaJNI.bitwuzla_substitute_term(body, vars.size(), origVars, substVars);

    argsAndBody[0] = substBody;
    if (q.equals(Quantifier.FORALL)) {
      return BitwuzlaJNI.bitwuzla_mk_term(
          BitwuzlaKind.BITWUZLA_KIND_FORALL.swigValue(), argsAndBody.length, argsAndBody);
    } else {
      return BitwuzlaJNI.bitwuzla_mk_term(
          BitwuzlaKind.BITWUZLA_KIND_EXISTS.swigValue(), argsAndBody.length, argsAndBody);
    }
  }
}
