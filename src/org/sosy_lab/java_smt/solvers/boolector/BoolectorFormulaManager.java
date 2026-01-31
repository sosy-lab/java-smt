// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class BoolectorFormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

  BoolectorFormulaManager(
      BoolectorFormulaCreator pFormulaCreator,
      BoolectorUFManager pFunctionManager,
      BoolectorBooleanFormulaManager pBooleanManager,
      BoolectorBitvectorFormulaManager pBitvectorManager,
      BoolectorArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        null,
        null,
        pBitvectorManager,
        null,
        null,
        pArrayManager,
        null,
        null,
        null);
  }

  @Override
  protected Long equalImpl(Long pArg1, Long pArgs) {
    return BtorJNI.boolector_eq(getEnvironment(), pArg1, pArgs);
  }

  @Override
  public Long parseImpl(String pS) throws IllegalArgumentException {
    throw new UnsupportedOperationException("Boolector can not parse single formulas.");
  }

  @Override
  public String dumpFormulaImpl(Long pT) {
    // TODO

    // -- Possibility 1:
    // Boolector can dump valid SMTLIB2 for a complete solver stack,
    // thus we can create a new solver stack through cloning,
    // assert the current node, and dump it.
    // As the cloned stack also copies the existing stack from the original context,
    // this method only works for an empty solver stack.
    //
    // The following code does not work:
    // The cloned instance does only contain a TRUE assertion. ???
    //
    // long clone = BtorJNI.boolector_clone(getEnvironment());
    // long matchingNode = BtorJNI.boolector_match_node(clone, pT);
    // BtorJNI.boolector_assert(clone, matchingNode);
    // String dump = BtorJNI.boolector_help_dump_smt2(clone);
    // BtorJNI.boolector_delete(clone);
    //
    // // cleanup the string
    // String suffix = "\n(check-sat)\n(exit)\n";
    // Preconditions.checkState(dump.endsWith(suffix));
    // dump = dump.substring(0, dump.length() - suffix.length());
    // out.append(dump);
    // -- End Possibility 1

    // -- Possibility 2:
    // Dump a single node from Boolector via boolector_help_dump_node_smt2.
    // Therefore, we need to dump all used symbols and add SMTLIB2-related parts
    // like "assert" and "declare-fun" on our own.
    // This requires direct access to the children/sub-formulae of a formula,
    // which is not available in Boolector.
    // This is the same reason why visitor is not fully implemented.
    // -- End Possibility 2

    // -- Possibility 3: minimal working solution with invalid SMTLIB2.
    // This method only dumps the current node, i.e.,
    // in case of "symbol" we only get the declaration, in case of "formula with
    // operator" we get a nice String, but without any symbol declaration.
    // The name of a symbol might be prefixed with "BTOR_%d@".format(solver.level).
    // As Boolector supports only one stack at the moment,
    // the name of a symbol in the dump depends on the overall context.

    return BtorJNI.boolector_help_dump_node_smt2(getEnvironment(), pT);

    // -- End Possibility 3
  }

  static long getBtorTerm(Formula pT) {
    return ((BoolectorFormula) pT).getTerm();
  }
}
