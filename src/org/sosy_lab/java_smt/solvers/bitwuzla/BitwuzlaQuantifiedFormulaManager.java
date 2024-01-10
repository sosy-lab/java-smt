// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.base.Preconditions.checkArgument;

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
    checkArgument(
        !vars.isEmpty(), "The list of bound variables for a quantifier may not be empty.");
    long[] origVars = new long[vars.size()];
    long[] substVars = new long[vars.size()];

    for (int i = 0; i < vars.size(); i++) {
      long var = vars.get(i);
      origVars[i] = var;
      // Create/Use bound vars
      long boundCopy = ((BitwuzlaFormulaCreator) formulaCreator).makeBoundVariable(var);
      substVars[i] = boundCopy;
    }
    long substBody = BitwuzlaJNI.bitwuzla_substitute_term(body, vars.size(), origVars, substVars);

    long[] argsAndBody = new long[2];
    argsAndBody[1] = substBody;
    long currentFormula = substBody;
    for (int i = 0; i < vars.size(); i++) {
      argsAndBody[0] = substVars[i];
      if (q.equals(Quantifier.FORALL)) {
        currentFormula =
            BitwuzlaJNI.bitwuzla_mk_term(
                BitwuzlaKind.BITWUZLA_KIND_FORALL.swigValue(), argsAndBody.length, argsAndBody);

      } else {
        currentFormula =
            BitwuzlaJNI.bitwuzla_mk_term(
                BitwuzlaKind.BITWUZLA_KIND_EXISTS.swigValue(), argsAndBody.length, argsAndBody);
      }
      argsAndBody[1] = currentFormula;
    }
    return currentFormula;
  }
}
