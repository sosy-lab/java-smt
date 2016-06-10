/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.test;

import static com.google.common.collect.Iterables.getLast;
import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BasicProverEnvironment;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;

import java.util.Collections;
import java.util.List;
import java.util.Set;

/**
 * This class contains some simple Junit-tests to check the interpolation-API of our solvers.
 */
@RunWith(Parameterized.class)
@SuppressWarnings("resource")
public class SolverInterpolationTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Solvers[] getAllCombinations() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  /** Generate a prover environment depending on the parameter above. */
  @SuppressWarnings("unchecked")
  private <T> InterpolatingProverEnvironment<T> newEnvironmentForTest() {
    return (InterpolatingProverEnvironment<T>) context.newProverEnvironmentWithInterpolation();
  }

  private static final UniqueIdGenerator index = new UniqueIdGenerator(); // to get different names

  @Test
  @SuppressWarnings("CheckReturnValue")
  public <T> void simpleInterpolation() throws Exception {
    requireInterpolation();

    try (InterpolatingProverEnvironment<T> prover = newEnvironmentForTest()) {
      IntegerFormula x, y, z;
      x = imgr.makeVariable("x");
      y = imgr.makeVariable("y");
      z = imgr.makeVariable("z");
      BooleanFormula f1 = imgr.equal(y, imgr.multiply(imgr.makeNumber(2), x));
      BooleanFormula f2 =
          imgr.equal(y, imgr.add(imgr.makeNumber(1), imgr.multiply(z, imgr.makeNumber(2))));
      prover.push(f1);
      T id2 = prover.push(f2);
      boolean check = prover.isUnsat();
      assertThat(check).named("formulas must be contradicting").isTrue();
      prover.getInterpolant(Collections.singletonList(id2));
      // we actually only check for a successful execution here, the result is irrelevant.
    }
  }

  @Test
  @SuppressWarnings("unchecked")
  public <T> void emptyInterpolationGroup() throws SolverException, InterruptedException {
    requireInterpolation();
    try (InterpolatingProverEnvironment<T> prover = newEnvironmentForTest()) {
      IntegerFormula x, y, z;
      x = imgr.makeVariable("x");
      y = imgr.makeVariable("y");
      z = imgr.makeVariable("z");
      BooleanFormula f1 = imgr.equal(y, imgr.multiply(imgr.makeNumber(2), x));
      BooleanFormula f2 =
          imgr.equal(y, imgr.add(imgr.makeNumber(1), imgr.multiply(z, imgr.makeNumber(2))));
      T id1 = prover.push(f1);
      T id2 = prover.push(f2);
      assertThat(prover.isUnsat()).isTrue();

      BooleanFormula emptyB = prover.getInterpolant(Lists.newArrayList(id1, id2));
      assertThat(bmgr.isFalse(emptyB)).isTrue();
      BooleanFormula emptyA = prover.getInterpolant(Lists.newArrayList());
      assertThat(bmgr.isTrue(emptyA)).isTrue();
    }
  }

  @Test
  @SuppressWarnings({"unchecked", "varargs"})
  public <T> void binaryInterpolation() throws SolverException, InterruptedException {
    requireInterpolation();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);

    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);

    // build formula:  1 = A = B = C = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, b);
    BooleanFormula C = imgr.equal(b, c);
    BooleanFormula D = imgr.equal(c, zero);

    T TA = stack.push(A);
    T TB = stack.push(B);
    T TC = stack.push(C);
    T TD = stack.push(D);

    assertThatEnvironment(stack).isUnsatisfiable();

    BooleanFormula itp = stack.getInterpolant(Lists.newArrayList());
    BooleanFormula itpA = stack.getInterpolant(Lists.newArrayList(TA));
    BooleanFormula itpAB = stack.getInterpolant(Lists.newArrayList(TA, TB));
    BooleanFormula itpABC = stack.getInterpolant(Lists.newArrayList(TA, TB, TC));
    BooleanFormula itpD = stack.getInterpolant(Lists.newArrayList(TD));
    BooleanFormula itpDC = stack.getInterpolant(Lists.newArrayList(TD, TC));
    BooleanFormula itpDCB = stack.getInterpolant(Lists.newArrayList(TD, TC, TB));
    BooleanFormula itpABCD = stack.getInterpolant(Lists.newArrayList(TA, TB, TC, TD));

    stack.pop(); // clear stack, such that we can re-use the solver
    stack.pop();
    stack.pop();
    stack.pop();

    // special cases: start and end of sequence might need special handling in the solver
    assertThat(bmgr.makeBoolean(true)).isEqualTo(itp);
    assertThat(bmgr.makeBoolean(false)).isEqualTo(itpABCD);

    // we check here the stricter properties for sequential interpolants,
    // but this simple example should work for all solvers
    checkItpSequence(
        stack, Lists.newArrayList(A, B, C, D), Lists.newArrayList(itpA, itpAB, itpABC));
    checkItpSequence(
        stack, Lists.newArrayList(D, C, B, A), Lists.newArrayList(itpD, itpDC, itpDCB));
  }

  @Test
  @SuppressWarnings({"unchecked", "varargs"})
  public <T> void binaryInterpolation1() throws SolverException, InterruptedException {
    requireInterpolation();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    // build formula:  1 = A = B = C = 0
    BooleanFormula A = bmgr.makeBoolean(false);
    BooleanFormula B = bmgr.makeBoolean(false);

    T TA = stack.push(A);
    T TB = stack.push(B);

    assertThatEnvironment(stack).isUnsatisfiable();

    BooleanFormula itp0 = stack.getInterpolant(Lists.newArrayList());
    BooleanFormula itpA = stack.getInterpolant(Lists.newArrayList(TA));
    BooleanFormula itpB = stack.getInterpolant(Lists.newArrayList(TA));
    BooleanFormula itpAB = stack.getInterpolant(Lists.newArrayList(TA, TB));

    stack.pop(); // clear stack, such that we can re-use the solver
    stack.pop();

    // special cases: start and end of sequence might need special handling in the solver
    assertThat(bmgr.makeBoolean(true)).isEqualTo(itp0);
    assertThat(bmgr.makeBoolean(false)).isEqualTo(itpAB);

    // want to see non-determinism in all solvers? try this:
    // System.out.println(solver + ": " + itpA);

    // we check here the stricter properties for sequential interpolants,
    // but this simple example should work for all solvers
    checkItpSequence(stack, Lists.newArrayList(A, B), Lists.newArrayList(itpA));
    checkItpSequence(stack, Lists.newArrayList(B, A), Lists.newArrayList(itpB));
  }

  private void requireSequentialItp() {
    requireInterpolation();
    assume()
        .withFailureMessage("Solver does not support sequential interpolation.")
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);
  }

  private void requireTreeItp() {
    requireInterpolation();
    assume()
        .withFailureMessage("Solver does not support tree-interpolation.")
        .that(solver)
        .isAnyOf(Solvers.Z3, Solvers.SMTINTERPOL);
  }

  @Test
  @SuppressWarnings({"unchecked", "varargs"})
  public <T> void sequentialInterpolation() throws SolverException, InterruptedException {

    requireSequentialItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);

    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);

    // build formula:  1 = A = B = C = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, b);
    BooleanFormula C = imgr.equal(b, c);
    BooleanFormula D = imgr.equal(c, zero);

    Set<T> TA = Sets.newHashSet(stack.push(A));
    Set<T> TB = Sets.newHashSet(stack.push(B));
    Set<T> TC = Sets.newHashSet(stack.push(C));
    Set<T> TD = Sets.newHashSet(stack.push(D));

    assertThatEnvironment(stack).isUnsatisfiable();

    List<BooleanFormula> itps1 = stack.getSeqInterpolants(Lists.newArrayList(TA, TB, TC, TD));
    List<BooleanFormula> itps2 = stack.getSeqInterpolants(Lists.newArrayList(TD, TC, TB, TA));
    List<BooleanFormula> itps3 = stack.getSeqInterpolants(Lists.newArrayList(TA, TC, TB, TD));

    List<BooleanFormula> itps4 =
        stack.getSeqInterpolants(Lists.newArrayList(TA, TA, TA, TB, TC, TD, TD));
    List<BooleanFormula> itps5 =
        stack.getSeqInterpolants(Lists.newArrayList(TA, TA, TB, TC, TD, TA, TD));
    List<BooleanFormula> itps6 =
        stack.getSeqInterpolants(Lists.newArrayList(TB, TC, TD, TA, TA, TA, TD));

    stack.pop(); // clear stack, such that we can re-use the solver
    stack.pop();
    stack.pop();
    stack.pop();

    checkItpSequence(stack, Lists.newArrayList(A, B, C, D), itps1);
    checkItpSequence(stack, Lists.newArrayList(D, C, B, A), itps2);
    checkItpSequence(stack, Lists.newArrayList(A, C, B, D), itps3);
    checkItpSequence(stack, Lists.newArrayList(A, A, A, C, B, D, D), itps4);
    checkItpSequence(stack, Lists.newArrayList(A, A, B, C, D, A, D), itps5);
    checkItpSequence(stack, Lists.newArrayList(B, C, D, A, A, A, D), itps6);
  }

  @Test
  public <T> void treeInterpolation() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);

    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);
    IntegerFormula d = imgr.makeVariable("d" + i);

    // build formula:  1 = A = B = C = D = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, b);
    BooleanFormula C = imgr.equal(b, c);
    BooleanFormula D = imgr.equal(c, d);
    BooleanFormula E = imgr.equal(d, zero);

    testTreeInterpolants0(stack, A, B, C, D, E);
    testTreeInterpolants0(stack, A, B, C, E, D);
    testTreeInterpolants0(stack, A, B, D, C, E);
    testTreeInterpolants0(stack, A, B, D, E, C);
    testTreeInterpolants0(stack, A, B, E, C, D);
    testTreeInterpolants0(stack, A, B, E, D, C);

    testTreeInterpolants0(stack, bmgr.not(A), A, A, A, A);
    testTreeInterpolants0(stack, bmgr.not(A), A, A, A, B);
    testTreeInterpolants0(stack, bmgr.not(A), A, A, B, A);
    testTreeInterpolants0(stack, bmgr.not(A), A, B, A, A);
    testTreeInterpolants0(stack, bmgr.not(A), A, A, B, B);
    testTreeInterpolants0(stack, bmgr.not(A), A, B, B, B);

    testTreeInterpolants1(stack, A, B, C, D, E);
    testTreeInterpolants1(stack, A, B, C, E, D);
    testTreeInterpolants1(stack, A, B, D, C, E);
    testTreeInterpolants1(stack, A, B, D, E, C);
    testTreeInterpolants1(stack, A, B, E, C, D);
    testTreeInterpolants1(stack, A, B, E, D, C);

    testTreeInterpolants1(stack, bmgr.not(A), A, A, A, A);
    testTreeInterpolants1(stack, bmgr.not(A), A, A, A, B);
    testTreeInterpolants1(stack, bmgr.not(A), A, A, B, A);
    testTreeInterpolants1(stack, bmgr.not(A), A, B, A, A);
    testTreeInterpolants1(stack, bmgr.not(A), A, A, B, B);
    testTreeInterpolants1(stack, bmgr.not(A), A, B, B, B);

    testTreeInterpolants2(stack, A, B, C, D, E);
    testTreeInterpolants2(stack, A, B, C, E, D);
    testTreeInterpolants2(stack, A, B, D, C, E);
    testTreeInterpolants2(stack, A, B, D, E, C);
    testTreeInterpolants2(stack, A, B, E, C, D);
    testTreeInterpolants2(stack, A, B, E, D, C);

    testTreeInterpolants2(stack, bmgr.not(A), A, A, A, A);
    testTreeInterpolants2(stack, bmgr.not(A), A, A, A, B);
    testTreeInterpolants2(stack, bmgr.not(A), A, A, B, A);
    testTreeInterpolants2(stack, bmgr.not(A), A, B, A, A);
    testTreeInterpolants2(stack, bmgr.not(A), A, A, B, B);
    testTreeInterpolants2(stack, bmgr.not(A), A, B, B, B);
  }

  @SuppressWarnings({"unchecked", "varargs"})
  private <T> void testTreeInterpolants0(
      InterpolatingProverEnvironment<T> stack,
      BooleanFormula pA,
      BooleanFormula pB,
      BooleanFormula pC,
      BooleanFormula pD,
      BooleanFormula pE)
      throws SolverException, InterruptedException {
    Set<T> TA = Sets.newHashSet(stack.push(pA));
    Set<T> TB = Sets.newHashSet(stack.push(pB));
    Set<T> TC = Sets.newHashSet(stack.push(pC));
    Set<T> TD = Sets.newHashSet(stack.push(pD));
    Set<T> TE = Sets.newHashSet(stack.push(pE));

    assertThatEnvironment(stack).isUnsatisfiable();

    // we build a very simple tree:
    // A  D
    // |  |
    // B  E
    // | /
    // C
    List<BooleanFormula> itps =
        stack.getTreeInterpolants(
            Lists.newArrayList(TA, TB, TD, TE, TC), // post-order
            new int[] {0, 0, 2, 2, 0}); // left-most node in current subtree

    stack.pop(); // clear stack, such that we can re-use the solver
    stack.pop();
    stack.pop();
    stack.pop();
    stack.pop();

    checkImplies(stack, pA, itps.get(0));
    checkImplies(stack, bmgr.and(itps.get(0), pB), itps.get(1));
    checkImplies(stack, pD, itps.get(2));
    checkImplies(stack, bmgr.and(itps.get(2), pE), itps.get(3));
    checkImplies(stack, bmgr.and(itps.get(1), itps.get(3), pC), bmgr.makeBoolean(false));
  }

  @SuppressWarnings({"unchecked", "varargs"})
  private <T> void testTreeInterpolants1(
      InterpolatingProverEnvironment<T> stack,
      BooleanFormula pA,
      BooleanFormula pB,
      BooleanFormula pC,
      BooleanFormula pD,
      BooleanFormula pE)
      throws SolverException, InterruptedException {
    Set<T> TA = Sets.newHashSet(stack.push(pA));
    Set<T> TB = Sets.newHashSet(stack.push(pB));
    Set<T> TC = Sets.newHashSet(stack.push(pC));
    Set<T> TD = Sets.newHashSet(stack.push(pD));
    Set<T> TE = Sets.newHashSet(stack.push(pE));

    assertThatEnvironment(stack).isUnsatisfiable();

    // we build a simple tree:
    // ABCD
    // \|//
    //  E
    List<BooleanFormula> itps =
        stack.getTreeInterpolants(
            Lists.newArrayList(TA, TB, TC, TD, TE), // post-order
            new int[] {0, 1, 2, 3, 0}); // left-most node in current subtree

    stack.pop(); // clear stack, such that we can re-use the solver
    stack.pop();
    stack.pop();
    stack.pop();
    stack.pop();

    checkImplies(stack, pA, itps.get(0));
    checkImplies(stack, pB, itps.get(1));
    checkImplies(stack, pC, itps.get(2));
    checkImplies(stack, pD, itps.get(3));
    checkImplies(
        stack,
        bmgr.and(itps.get(0), itps.get(1), itps.get(2), itps.get(3), pE),
        bmgr.makeBoolean(false));
  }

  @SuppressWarnings({"unchecked", "varargs"})
  private <T> void testTreeInterpolants2(
      InterpolatingProverEnvironment<T> stack,
      BooleanFormula pA,
      BooleanFormula pB,
      BooleanFormula pC,
      BooleanFormula pD,
      BooleanFormula pE)
      throws SolverException, InterruptedException {
    Set<T> TA = Sets.newHashSet(stack.push(pA));
    Set<T> TB = Sets.newHashSet(stack.push(pB));
    Set<T> TC = Sets.newHashSet(stack.push(pC));
    Set<T> TD = Sets.newHashSet(stack.push(pD));
    Set<T> TE = Sets.newHashSet(stack.push(pE));

    assertThatEnvironment(stack).isUnsatisfiable();

    // we build a simple degenerated tree:
    // A
    // |
    // B
    // |
    // C
    // |
    // D
    // |
    // E
    List<BooleanFormula> itps =
        stack.getTreeInterpolants(
            Lists.newArrayList(TA, TB, TC, TD, TE), // post-order
            new int[] {0, 0, 0, 0, 0}); // left-most node in current subtree

    stack.pop(); // clear stack, such that we can re-use the solver
    stack.pop();
    stack.pop();
    stack.pop();
    stack.pop();

    checkImplies(stack, pA, itps.get(0));
    checkImplies(stack, bmgr.and(itps.get(0), pB), itps.get(1));
    checkImplies(stack, bmgr.and(itps.get(1), pC), itps.get(2));
    checkImplies(stack, bmgr.and(itps.get(2), pD), itps.get(3));
    checkImplies(stack, bmgr.and(itps.get(3), pE), bmgr.makeBoolean(false));
  }

  @Test
  @SuppressWarnings({"unchecked", "varargs"})
  public <T> void treeInterpolation2() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula five = imgr.makeNumber(5);

    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);
    IntegerFormula d = imgr.makeVariable("d" + i);
    IntegerFormula e = imgr.makeVariable("e" + i);

    // build formula:  1 = A = B = C = D+1 and D = E = 5
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, b);
    BooleanFormula R1 = imgr.equal(b, c);
    BooleanFormula C = imgr.equal(c, imgr.add(d, one));
    BooleanFormula R2 = imgr.equal(d, e);
    BooleanFormula D = imgr.equal(e, five);

    Set<T> TA = Sets.newHashSet(stack.push(A));
    Set<T> TB = Sets.newHashSet(stack.push(B));
    Set<T> TR1 = Sets.newHashSet(stack.push(R1));
    Set<T> TC = Sets.newHashSet(stack.push(C));
    Set<T> TR2 = Sets.newHashSet(stack.push(R2));
    Set<T> TD = Sets.newHashSet(stack.push(D));

    assertThatEnvironment(stack).isUnsatisfiable();

    // we build a simple tree:
    // A
    // |
    // B  C
    // | /
    // R1 D
    // | /
    // R2
    List<BooleanFormula> itps =
        stack.getTreeInterpolants(
            Lists.newArrayList(TA, TB, TC, TR1, TD, TR2), // post-order
            new int[] {0, 0, 2, 0, 4, 0}); // left-most node in current subtree

    stack.pop(); // clear stack, such that we can re-use the solver
    stack.pop();
    stack.pop();
    stack.pop();
    stack.pop();
    stack.pop();

    checkImplies(stack, A, itps.get(0));
    checkImplies(stack, bmgr.and(itps.get(0), B), itps.get(1));
    checkImplies(stack, C, itps.get(2));
    checkImplies(stack, bmgr.and(Lists.newArrayList(itps.get(1), itps.get(2), R1)), itps.get(3));
    checkImplies(stack, D, itps.get(4));
    checkImplies(
        stack, bmgr.and(Lists.newArrayList(itps.get(3), itps.get(4), R2)), bmgr.makeBoolean(false));
  }

  private void checkItpSequence(
      InterpolatingProverEnvironment<?> stack,
      List<BooleanFormula> formulas,
      List<BooleanFormula> itps)
      throws SolverException, InterruptedException {

    assert formulas.size() - 1 == itps.size() : "there should be N-1 interpolants for N formulas";

    checkImplies(stack, formulas.get(0), itps.get(0));
    for (int i = 1; i < formulas.size() - 1; i++) {
      checkImplies(stack, bmgr.and(itps.get(i - 1), formulas.get(i)), itps.get(i));
    }
    checkImplies(stack, bmgr.and(getLast(itps), getLast(formulas)), bmgr.makeBoolean(false));
  }

  private void checkImplies(BasicProverEnvironment<?> stack, BooleanFormula a, BooleanFormula b)
      throws SolverException, InterruptedException {
    // a=>b  <-->  !a||b
    stack.push(bmgr.or(bmgr.not(a), b));
    assertThatEnvironment(stack).isSatisfiable();
    stack.pop();
  }
}
