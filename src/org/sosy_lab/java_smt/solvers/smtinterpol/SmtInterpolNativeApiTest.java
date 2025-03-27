/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.truth.Truth.assertThat;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.log.LogManager;

public class SmtInterpolNativeApiTest {
  private Script script;

  private Sort booleanSort;
  private Sort integerSort;

  @Before
  public void setUp() {
    LogProxyForwarder smtInterpolLogProxy =
        new LogProxyForwarder(LogManager.createTestLogManager());
    script = new SMTInterpol(smtInterpolLogProxy, () -> false);
    script.setOption(":produce-proofs", "true");
    script.setLogic(Logics.AUFNIRA);

    booleanSort = script.getTheory().getBooleanSort();
    integerSort = script.getTheory().getNumericSort();
  }

  private Term makeVariable(String pName, Sort pSort) {
    script.declareFun(pName, new Sort[] {}, pSort);
    return script.term(pName);
  }

  @Test
  public void booleanTest() {
    // A and !A is unsatisfiable
    Term var = makeVariable("var", booleanSort);
    script.assertTerm(var);
    script.assertTerm(script.term("not", var));

    assertThat(script.checkSat()).isEqualTo(LBool.UNSAT);
  }

  @Test
  public void integerTest() {
    // a <= b and b <= c implies a <= c
    Term a = makeVariable("a", integerSort);
    Term b = makeVariable("b", integerSort);
    Term c = makeVariable("c", integerSort);

    script.assertTerm(
        script.term(
            "not",
            script.term(
                "=>",
                script.term("and", script.term("<=", a, b), script.term("<=", b, c)),
                script.term("<=", a, c))));

    assertThat(script.checkSat()).isEqualTo(LBool.UNSAT);
  }
}
