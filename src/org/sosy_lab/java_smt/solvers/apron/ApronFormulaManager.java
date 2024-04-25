// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.apron;

import apron.Environment;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;

public class ApronFormulaManager
    extends AbstractFormulaManager<ApronNode, ApronFormulaType, Environment, Long> {

  protected ApronFormulaManager(
      ApronFormulaCreator pFormulaCreator,
      ApronUFManager functionManager,
      ApronBooleanFormulaManager booleanManager,
      ApronIntegerFormulaManager pIntegerFormulaManager,
      ApronRationalFormulaManager pRationalFormulaManager) {
    super(
        pFormulaCreator,
        functionManager,
        booleanManager,
        pIntegerFormulaManager,
        pRationalFormulaManager,
        null,
        null,
        null,
        null,
        null,
        null,
        null);
  }

  public static ApronNode getTerm(Formula pFormula) {
    return ((ApronNode) pFormula).getInstance();
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    throw new UnsupportedOperationException("Apron does not support parse().");
  }

  @Override
  public Appender dumpFormula(ApronNode t) {
    throw new UnsupportedOperationException("Apron does not support dumpFormula().");
  }

  @Override
  public <T extends Formula> T substitute(
      T f, Map<? extends Formula, ? extends Formula> fromToMapping) {
    throw new UnsupportedOperationException("Apron does not support substitute().");
  }
}
