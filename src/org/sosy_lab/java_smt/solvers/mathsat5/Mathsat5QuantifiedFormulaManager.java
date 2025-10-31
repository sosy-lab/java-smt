/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.mathsat5;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_apply_substitution;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_exists;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_forall;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_variable;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_type;

import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class Mathsat5QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Long, Long, Long, Long> {

  protected Mathsat5QuantifiedFormulaManager(
      FormulaCreator<Long, Long, Long, Long> pFormulaCreator) {
    super(pFormulaCreator);
  }

  @Override
  protected Long eliminateQuantifiers(Long input) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  public Long mkQuantifier(Quantifier quantifier, List<Long> variables, Long body) {
    // Note: Mathsat supports this only for printing SMTLib2, not solving!
    checkArgument(!variables.isEmpty(), "List of bound variables can not be empty");

    Mathsat5FormulaCreator creator = (Mathsat5FormulaCreator) getFormulaCreator();
    long env = creator.getEnv();
    Long quantifiedFormula = null;

    long[] freeVariables = new long[variables.size()];
    long[] boundVariables = new long[variables.size()];
    for (int i = 0; i < variables.size(); i++) {
      long var = variables.get(i);
      freeVariables[i] = var;
      // We assume for now that the Mathsat cache automatically re-uses them
      boundVariables[i] = msat_make_variable(env, creator.getName(var), msat_term_get_type(var));
    }

    long substBody = msat_apply_substitution(env, body, 1, freeVariables, boundVariables);

    // TODO: in the past, dumping with the function for quantifiers with more than 1 variable
    //  caused problems. Re-check from time to time with function: msat_existentially_quantify()
    if (quantifier == Quantifier.EXISTS) {
      for (int i = 0; i < variables.size(); i++) {
        quantifiedFormula = msat_make_exists(env, boundVariables[i], substBody);
      }
    } else {
      for (int i = 0; i < variables.size(); i++) {
        quantifiedFormula = msat_make_forall(env, boundVariables[i], substBody);
      }
    }
    return checkNotNull(quantifiedFormula);
  }
}
