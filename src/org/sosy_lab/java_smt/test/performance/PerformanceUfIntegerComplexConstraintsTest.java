// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test.performance;

import org.junit.Before;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class PerformanceUfIntegerComplexConstraintsTest extends AbstractPerformanceTest0 {

  @Before
  public final void checkRequirements() {
    requireIntegers();
  }

  @Override
  protected BooleanFormula createConstraint(int i) {
    FunctionDeclaration<BooleanFormula> foo =
        fmgr.declareUF(
            "foo", FormulaType.BooleanType, FormulaType.IntegerType, FormulaType.IntegerType);
    IntegerFormula var = imgr.makeVariable("i" + i);
    return fmgr.callUF(foo, var, var);
  }
}
