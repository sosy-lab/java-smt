/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

@RunWith(Parameterized.class)
@SuppressWarnings("resource")
public class SolverStackTest extends SolverBasedTest0 {

  @Parameters(name = "{0} (interpolation={1}}")
  public static List<Object[]> getAllCombinations() {
    List<Object[]> result = new ArrayList<>();
    for (Solvers solver : Solvers.values()) {
      result.add(new Object[] {solver, false});
      result.add(new Object[] {solver, true});
    }
    return result;
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Parameter(1)
  public boolean useInterpolatingEnvironment;

  /** Generate a prover environment depending on the parameter above. */
  private BasicProverEnvironment<?> newEnvironmentForTest(ProverOptions... options) {
    if (useInterpolatingEnvironment) {
      requireInterpolation();
      return context.newProverEnvironmentWithInterpolation();
    } else {
      return context.newProverEnvironment(options);
    }
  }

  @Rule public ExpectedException thrown = ExpectedException.none();

  private static final UniqueIdGenerator index = new UniqueIdGenerator(); // to get different names

  private void requireMultipleStackSupport() {
    assume()
        .withMessage("Solver does not support multiple stacks yet")
        .that(solver)
        .isNotEqualTo(Solvers.SMTINTERPOL);
  }

  protected final void requireUfValuesInModel() {
    assume()
        .withMessage(
            "Integration of solver does not support retrieving values for UFs from a model")
        .that(solver)
        .isNotEqualTo(Solvers.Z3);
  }

  @Test
  public void simpleStackTestBool() throws SolverException, InterruptedException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest();

    int i = index.getFreshId();
    BooleanFormula a = bmgr.makeVariable("bool_a" + i);
    BooleanFormula b = bmgr.makeVariable("bool_b" + i);
    BooleanFormula or = bmgr.or(a, b);

    stack.push(or); // L1
    assertThat(stack).isSatisfiable();
    BooleanFormula c = bmgr.makeVariable("bool_c" + i);
    BooleanFormula d = bmgr.makeVariable("bool_d" + i);
    BooleanFormula and = bmgr.and(c, d);

    stack.push(and); // L2
    assertThat(stack).isSatisfiable();

    BooleanFormula notOr = bmgr.not(or);

    stack.push(notOr); // L3
    assertThat(stack).isUnsatisfiable(); // "or" AND "not or" --> UNSAT

    stack.pop(); // L2
    assertThat(stack).isSatisfiable();

    stack.pop(); // L1
    assertThat(stack).isSatisfiable();

    // we are lower than before creating c and d.
    // however we assume that they are usable now (this violates SMTlib).
    stack.push(and); // L2
    assertThat(stack).isSatisfiable();

    stack.pop(); // L1
    assertThat(stack).isSatisfiable();

    stack.push(notOr); // L2
    assertThat(stack).isUnsatisfiable(); // "or" AND "not or" --> UNSAT

    stack.pop(); // L1
    assertThat(stack).isSatisfiable();

    stack.pop(); // L0 empty stack
  }

  @Test
  public void singleStackTestInteger() throws SolverException, InterruptedException {
    BasicProverEnvironment<?> env = newEnvironmentForTest();
    simpleStackTestNum(imgr, env);
  }

  @Test
  public void singleStackTestRational() throws SolverException, InterruptedException {
    requireRationals();
    assert rmgr != null;

    BasicProverEnvironment<?> env = newEnvironmentForTest();
    simpleStackTestNum(rmgr, env);
  }

  private <X extends NumeralFormula, Y extends X> void simpleStackTestNum(
      NumeralFormulaManager<X, Y> nmgr, BasicProverEnvironment<?> stack)
      throws SolverException, InterruptedException {
    int i = index.getFreshId();
    X a = nmgr.makeVariable("num_a" + i);
    X b = nmgr.makeVariable("num_b" + i);
    BooleanFormula leqAB = nmgr.lessOrEquals(a, b);

    stack.push(leqAB); // L1
    assertThat(stack).isSatisfiable();
    X c = nmgr.makeVariable("num_c" + i);
    X d = nmgr.makeVariable("num_d" + i);
    BooleanFormula eqCD = nmgr.lessOrEquals(c, d);

    stack.push(eqCD); // L2
    assertThat(stack).isSatisfiable();

    BooleanFormula gtAB = nmgr.greaterThan(a, b);

    stack.push(gtAB); // L3
    assertThat(stack).isUnsatisfiable(); // "<=" AND ">" --> UNSAT

    stack.pop(); // L2
    assertThat(stack).isSatisfiable();

    stack.pop(); // L1
    assertThat(stack).isSatisfiable();

    // we are lower than before creating c and d.
    // however we assume that they are usable now (this violates SMTlib).
    stack.push(eqCD); // L2
    assertThat(stack).isSatisfiable();

    stack.pop(); // L1
    assertThat(stack).isSatisfiable();

    stack.push(gtAB); // L2
    assertThat(stack).isUnsatisfiable(); // "or" AND "not or" --> UNSAT

    stack.pop(); // L1
    assertThat(stack).isSatisfiable();

    stack.pop(); // L0 empty stack
  }

  @Test
  public void stackTest() {
    BasicProverEnvironment<?> stack = newEnvironmentForTest();
    thrown.expect(RuntimeException.class);
    stack.pop();
  }

  @Test
  public void stackTest2() {
    BasicProverEnvironment<?> stack = newEnvironmentForTest();
    stack.push();
    stack.pop();
  }

  @Test
  public void stackTest3() {
    BasicProverEnvironment<?> stack = newEnvironmentForTest();
    stack.push();
    stack.pop();
    stack.push();
    stack.pop();
  }

  @Test
  public void stackTest4() {
    BasicProverEnvironment<?> stack = newEnvironmentForTest();
    stack.push();
    stack.push();
    stack.pop();
    stack.pop();
  }

  @Test
  public void stackTest5() {
    BasicProverEnvironment<?> stack = newEnvironmentForTest();
    stack.push();
    stack.pop();
    thrown.expect(RuntimeException.class);
    stack.pop();
  }

  @Test
  public void constraintTestBool1() throws SolverException, InterruptedException {
    BooleanFormula a = bmgr.makeVariable("bool_a");

    try (BasicProverEnvironment<?> stack = newEnvironmentForTest()) {
      stack.addConstraint(a);
      assertThat(stack).isSatisfiable();
    }

    try (BasicProverEnvironment<?> stack2 = newEnvironmentForTest()) {
      stack2.addConstraint(bmgr.not(a));
      assertThat(stack2).isSatisfiable();
    }
  }

  @Test
  public void constraintTestBool2() throws SolverException, InterruptedException {
    BooleanFormula a = bmgr.makeVariable("bool_a");

    try (BasicProverEnvironment<?> stack = newEnvironmentForTest()) {
      stack.push(a);
      assertThat(stack).isSatisfiable();
    }

    try (BasicProverEnvironment<?> stack2 = newEnvironmentForTest()) {
      stack2.addConstraint(bmgr.not(a));
      assertThat(stack2).isSatisfiable();
    }
  }

  @Test
  public void constraintTestBool3() throws SolverException, InterruptedException {
    BooleanFormula a = bmgr.makeVariable("bool_a");

    try (BasicProverEnvironment<?> stack = newEnvironmentForTest()) {
      stack.push(a);
      assertThat(stack).isSatisfiable();
    }

    try (BasicProverEnvironment<?> stack2 = newEnvironmentForTest()) {
      thrown.expect(RuntimeException.class);
      stack2.pop();
    }
  }

  @Test
  public void constraintTestBool4() throws SolverException, InterruptedException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest();
    stack.addConstraint(bmgr.makeVariable("bool_a"));
    assertThat(stack).isSatisfiable();
    thrown.expect(RuntimeException.class);
    stack.pop();
  }

  @Test
  public void satTestBool5() throws SolverException, InterruptedException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest();
    assertThat(stack).isSatisfiable();
  }

  @Test
  public void dualStackTest() throws SolverException, InterruptedException {
    requireMultipleStackSupport();

    BooleanFormula a = bmgr.makeVariable("bool_a");
    BooleanFormula not = bmgr.not(a);

    BasicProverEnvironment<?> stack1 = newEnvironmentForTest();
    stack1.push(a); // L1
    stack1.push(a); // L2
    BasicProverEnvironment<?> stack2 = newEnvironmentForTest();
    stack1.pop(); // L1
    stack1.pop(); // L0

    stack1.push(a); // L1
    assertThat(stack1).isSatisfiable();

    stack2.push(not); // L1
    assertThat(stack2).isSatisfiable();

    stack1.pop(); // L0
    stack2.pop(); // L0
  }

  @Test
  public void dualStackTest2() throws SolverException, InterruptedException {
    requireMultipleStackSupport();

    BooleanFormula a = bmgr.makeVariable("bool_a");
    BooleanFormula not = bmgr.not(a);

    BasicProverEnvironment<?> stack1 = newEnvironmentForTest();
    BasicProverEnvironment<?> stack2 = newEnvironmentForTest();
    stack1.push(a); // L1
    stack1.push(bmgr.makeBoolean(true)); // L2
    assertThat(stack1).isSatisfiable();
    stack2.push(not); // L1
    assertThat(stack2).isSatisfiable();
    stack1.pop(); // L1
    assertThat(stack1).isSatisfiable();
    stack1.pop(); // L1
    assertThat(stack1).isSatisfiable();
    stack2.pop(); // L1
    assertThat(stack2).isSatisfiable();
    assertThat(stack1).isSatisfiable();
  }

  /**
   * This test checks that a SMT solver uses "global declarations": regardless of the stack at
   * declaration time, declarations always live for the full life time of the solver (i.e., they do
   * not get deleted on pop()). This is contrary to the SMTLib standard, but required by us, e.g.
   * for BMC with induction (where we create new formulas while there is something on the stack).
   */
  @Test
  public void dualStackGlobalDeclarations() throws SolverException, InterruptedException {
    // Create non-empty stack
    BasicProverEnvironment<?> stack1 = newEnvironmentForTest();
    stack1.push(bmgr.makeVariable("bool_a"));

    // Declare b while non-empty stack exists
    final String varName = "bool_b";
    final BooleanFormula b = bmgr.makeVariable(varName);

    // Clear stack (without global declarations b gets deleted)
    stack1.push(b);
    assertThat(stack1).isSatisfiable();
    stack1.pop();
    stack1.pop();
    stack1.close();

    // Check that "b" (the reference to the old formula)
    // is equivalent to a new formula with the same variable
    assertThatFormula(b).isEquivalentTo(bmgr.makeVariable(varName));
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void modelForUnsatFormula() throws SolverException, InterruptedException {
    try (BasicProverEnvironment<?> stack = newEnvironmentForTest()) {
      stack.push(imgr.greaterThan(imgr.makeVariable("a"), imgr.makeNumber(0)));
      stack.push(imgr.lessThan(imgr.makeVariable("a"), imgr.makeNumber(0)));
      assertThat(stack).isUnsatisfiable();

      thrown.expect(Exception.class);
      stack.getModel();
    }
  }

  @Test
  public void modelForSatFormula() throws SolverException, InterruptedException {
    try (BasicProverEnvironment<?> stack = newEnvironmentForTest(ProverOptions.GENERATE_MODELS)) {
      IntegerFormula a = imgr.makeVariable("a");
      stack.push(imgr.greaterThan(a, imgr.makeNumber(0)));
      stack.push(imgr.lessThan(a, imgr.makeNumber(2)));
      assertThat(stack).isSatisfiable();

      Model model = stack.getModel();
      assertThat(model.evaluate(a)).isEqualTo(BigInteger.ONE);
    }
  }

  @Test
  public void modelForSatFormulaWithLargeValue() throws SolverException, InterruptedException {
    try (BasicProverEnvironment<?> stack = newEnvironmentForTest(ProverOptions.GENERATE_MODELS)) {
      BigInteger val = BigInteger.TEN.pow(1000);
      IntegerFormula a = imgr.makeVariable("a");
      stack.push(imgr.equal(a, imgr.makeNumber(val)));
      assertThat(stack).isSatisfiable();

      Model model = stack.getModel();
      assertThat(model.evaluate(a)).isEqualTo(val);
    }
  }

  @Test
  public void modelForSatFormulaWithUF() throws SolverException, InterruptedException {
    try (BasicProverEnvironment<?> stack = newEnvironmentForTest(ProverOptions.GENERATE_MODELS)) {
      IntegerFormula zero = imgr.makeNumber(0);
      IntegerFormula varA = imgr.makeVariable("a");
      IntegerFormula varB = imgr.makeVariable("b");
      stack.push(imgr.equal(varA, zero));
      stack.push(imgr.equal(varB, zero));
      FunctionDeclaration<IntegerFormula> uf =
          fmgr.declareUF("uf", FormulaType.IntegerType, FormulaType.IntegerType);
      stack.push(imgr.equal(fmgr.callUF(uf, varA), zero));
      stack.push(imgr.equal(fmgr.callUF(uf, varB), zero));
      assertThat(stack).isSatisfiable();

      Model model = stack.getModel();

      // actual type of object is not defined, thus do string matching:
      assertThat(model.evaluate(varA)).isEqualTo(BigInteger.ZERO);
      assertThat(model.evaluate(varB)).isEqualTo(BigInteger.ZERO);

      requireUfValuesInModel();

      assertThat(model.evaluate(fmgr.callUF(uf, imgr.makeNumber(BigDecimal.ZERO))))
          .isEqualTo(BigInteger.ZERO);
    }
  }
}
