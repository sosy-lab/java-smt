// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.trace;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Joiner;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;

public class TraceEnumerationFormulaManager implements EnumerationFormulaManager {

  private final EnumerationFormulaManager delegate;
  private final TraceLogger logger;

  TraceEnumerationFormulaManager(EnumerationFormulaManager pDelegate, TraceLogger pLogger) {
    delegate = checkNotNull(pDelegate);
    logger = checkNotNull(pLogger);
  }

  @Override
  public EnumerationFormulaType declareEnumeration(String name, Set<String> elementNames) {
    return logger.logDefKeep(
        "mgr.getEnumerationFormulaManager()",
        String.format(
            "declareEnumeration(\"%s\", Set.of(\"%s\"))",
            name, Joiner.on("\", \"").join(elementNames)),
        () -> delegate.declareEnumeration(name, elementNames));
  }

  @Override
  public EnumerationFormula makeConstant(String pName, EnumerationFormulaType pType) {
    return logger.logDef(
        "mgr.getEnumerationFormulaManager()",
        String.format("makeConstant(\"%s\", %s)", pName, logger.toVariable(pType)),
        () -> delegate.makeConstant(pName, pType));
  }

  @Override
  public EnumerationFormula makeVariable(String pVar, EnumerationFormulaType pType) {
    return logger.logDef(
        "mgr.getEnumerationFormulaManager()",
        String.format("makeVariable(\"%s\", %s)", pVar, logger.toVariable(pType)),
        () -> delegate.makeVariable(pVar, pType));
  }

  @Override
  public BooleanFormula equivalence(
      EnumerationFormula pEnumeration1, EnumerationFormula pEnumeration2) {
    return logger.logDef(
        "mgr.getEnumerationFormulaManager()",
        String.format(
            "equivalence(%s, %s)",
            logger.toVariable(pEnumeration1), logger.toVariable(pEnumeration2)),
        () -> delegate.equivalence(pEnumeration1, pEnumeration2));
  }
}
