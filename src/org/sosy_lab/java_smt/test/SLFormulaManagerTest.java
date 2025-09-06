// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class SLFormulaManagerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  private BooleanFormula makeStarAll(List<BooleanFormula> formulas) {
    return formulas.stream().reduce(slmgr::makeStar).orElse(bmgr.makeTrue());
  }

  protected void requireSepNil() {
    assume()
        .withMessage("Java bindings for solver %s do not support SEP_NIL", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC4);
  }

  protected void requireMultipleHeapSorts() {
    assume()
        .withMessage(
            "Java bindings for solver %s do not support multiple heap sorts", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC4);
  }

  @Before
  public void setup() {
    requireSeparationLogic();
  }

  @Test
  public void testStackWithoutSL() throws InterruptedException, SolverException {
    BooleanFormula noSL = imgr.equal(imgr.makeNumber(1), imgr.makeVariable("x"));

    assertThatFormula(noSL).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testMakeEmp() throws InterruptedException, SolverException {
    BooleanFormula emptyHeapInt =
        slmgr.makeEmptyHeap(FormulaType.IntegerType, FormulaType.IntegerType);

    assertThatFormula(emptyHeapInt).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testMakeEmptoP2() throws InterruptedException, SolverException {
    requireMultipleHeapSorts();
    // Actually, no solver supports multiple heap sorts. However, our bindings for CVC5
    // apply non-incremental mode for SL and use distinct solver instances for distinct queries.

    BooleanFormula emptyHeapInt =
        slmgr.makeEmptyHeap(FormulaType.RationalType, FormulaType.BooleanType);
    BooleanFormula emptyHeapRat =
        slmgr.makeEmptyHeap(FormulaType.IntegerType, FormulaType.IntegerType);
    BooleanFormula query = bmgr.and(emptyHeapInt, emptyHeapRat);

    assertThatFormula(query).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testNotNilPtoNil() throws InterruptedException, SolverException {
    requireSepNil();

    IntegerFormula nil = slmgr.makeNilElement(FormulaType.IntegerType);
    BooleanFormula nilPtoNil = slmgr.makePointsTo(nil, nil);

    assertThatFormula(nilPtoNil).isUnsatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testNilPtoValue() throws InterruptedException, SolverException {
    requireSepNil();

    IntegerFormula nil = slmgr.makeNilElement(FormulaType.IntegerType);
    IntegerFormula value = imgr.makeNumber(42);
    BooleanFormula nilPtoValue = slmgr.makePointsTo(nil, value);

    assertThatFormula(nilPtoValue).isUnsatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testXPtoNil() throws InterruptedException, SolverException {
    requireSepNil();

    IntegerFormula ptr = imgr.makeVariable("p");
    IntegerFormula nil = slmgr.makeNilElement(FormulaType.IntegerType);
    BooleanFormula ptoNil = slmgr.makePointsTo(ptr, nil);

    assertThatFormula(ptoNil).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testXPtoValue() throws InterruptedException, SolverException {
    IntegerFormula ptr = imgr.makeVariable("p");
    IntegerFormula value = imgr.makeNumber(42);
    BooleanFormula ptoValue = slmgr.makePointsTo(ptr, value);

    assertThatFormula(ptoValue).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testPPtoNilThenPPtoNil() throws SolverException, InterruptedException {
    requireSepNil();

    IntegerFormula ptr = imgr.makeVariable("p");
    IntegerFormula nil = slmgr.makeNilElement(FormulaType.IntegerType);
    BooleanFormula ptoNil = slmgr.makePointsTo(ptr, nil);

    assertThatFormula(ptoNil).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);

    // test repeated non-incremental solving in CVC5
    try (ProverEnvironment prover =
        context.newProverEnvironment(ProverOptions.ENABLE_SEPARATION_LOGIC)) {
      prover.push(ptoNil);
      assertThatEnvironment(prover).isSatisfiable();
      assertThatEnvironment(prover).isSatisfiable();
      prover.pop();
    }
  }

  @Test
  public void testPtoNilThenPPto42() throws SolverException, InterruptedException {
    requireSepNil();

    IntegerFormula ptr = imgr.makeVariable("p");
    IntegerFormula nil = slmgr.makeNilElement(FormulaType.IntegerType);
    IntegerFormula value = imgr.makeNumber(42);
    BooleanFormula ptoNil = slmgr.makePointsTo(ptr, nil);
    BooleanFormula ptoValue = slmgr.makePointsTo(ptr, value);

    assertThatFormula(ptoNil).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
    assertThatFormula(ptoValue).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);

    // test repeated non-incremental solving in CVC5
    try (ProverEnvironment prover =
        context.newProverEnvironment(ProverOptions.ENABLE_SEPARATION_LOGIC)) {
      prover.push(ptoNil);
      assertThatEnvironment(prover).isSatisfiable();
      prover.pop();
      prover.push(ptoValue);
      assertThatEnvironment(prover).isSatisfiable();
      prover.pop();
    }
  }

  @Test
  public void testPtoAndEmp() throws InterruptedException, SolverException {
    IntegerFormula ptr = imgr.makeVariable("p");
    IntegerFormula value = imgr.makeNumber(42);
    BooleanFormula pto = slmgr.makePointsTo(ptr, value);
    BooleanFormula emp = slmgr.makeEmptyHeap(FormulaType.IntegerType, FormulaType.IntegerType);
    BooleanFormula combined = slmgr.makeStar(pto, emp);

    assertThatFormula(combined).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testStar() throws InterruptedException, SolverException {
    IntegerFormula ptr1 = imgr.makeVariable("ptoP1");
    IntegerFormula ptr2 = imgr.makeVariable("ptoP2");
    IntegerFormula value1 = imgr.makeNumber(42);
    IntegerFormula value2 = imgr.makeNumber(43);

    BooleanFormula ptoP1V1 = slmgr.makePointsTo(ptr1, value1);
    BooleanFormula ptoP1V2 = slmgr.makePointsTo(ptr1, value2);
    BooleanFormula ptoP2V1 = slmgr.makePointsTo(ptr2, value1);
    BooleanFormula ptoP2V2 = slmgr.makePointsTo(ptr2, value2);

    assertThatFormula(slmgr.makeStar(ptoP1V1, ptoP1V1))
        .isUnsatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
    assertThatFormula(slmgr.makeStar(ptoP1V1, ptoP1V2))
        .isUnsatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
    assertThatFormula(slmgr.makeStar(ptoP1V1, ptoP2V1))
        .isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
    assertThatFormula(slmgr.makeStar(ptoP1V1, ptoP2V2))
        .isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);

    assertThatFormula(
            bmgr.implication(
                slmgr.makeStar(ptoP1V1, ptoP2V2), imgr.distinct(ImmutableList.of(ptr1, ptr2))))
        .isTautological(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testSimpleTreeValid() throws InterruptedException, SolverException {
    requireSepNil();

    // lets build a tree:
    // - each node consists of two integers: left and right
    // - each node pointer points to the left integer, the right integer is at pointer+1
    IntegerFormula nil = slmgr.makeNilElement(FormulaType.IntegerType);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula root = imgr.makeVariable("root");
    IntegerFormula left = imgr.makeVariable("left");
    IntegerFormula right = imgr.makeVariable("right");
    BooleanFormula ptoRootLeft = slmgr.makePointsTo(root, left);
    BooleanFormula ptoRootRight = slmgr.makePointsTo(imgr.add(root, one), left);
    BooleanFormula ptoLeftNil = slmgr.makePointsTo(left, nil);
    BooleanFormula ptoRightNil = slmgr.makePointsTo(right, nil);

    // tree: (root -> left) * (root+1 -> right) * (left -> nil) * (right -> nil)
    BooleanFormula sepTree =
        makeStarAll(ImmutableList.of(ptoRootLeft, ptoRootRight, ptoLeftNil, ptoRightNil));

    assertThatFormula(sepTree).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
    try (ProverEnvironment prover =
        context.newProverEnvironment(
            ProverOptions.ENABLE_SEPARATION_LOGIC, ProverOptions.GENERATE_MODELS)) {
      prover.push(sepTree);
      assertThatEnvironment(prover).isSatisfiable();
      try (Model model = prover.getModel()) {
        // check that root, left and right are different
        BigInteger valRoot = model.evaluate(root);
        BigInteger valLeft = model.evaluate(left);
        BigInteger valRight = model.evaluate(right);
        BigInteger valNil = model.evaluate(nil);
        assertThat(ImmutableSet.of(valRoot, valLeft, valRight, valNil)).hasSize(4); // all different
        assertThat(valRoot.add(BigInteger.ONE)).isNoneOf(valLeft, valRight, valNil);
      }
      prover.pop();
    }
  }

  @Test
  public void testSimpleTreeInvalid() throws InterruptedException, SolverException {
    requireSepNil();

    IntegerFormula nil = slmgr.makeNilElement(FormulaType.IntegerType);
    IntegerFormula root = imgr.makeVariable("root");
    IntegerFormula left = imgr.makeVariable("left");
    IntegerFormula right = imgr.makeVariable("right");
    BooleanFormula ptoRootLeft = slmgr.makePointsTo(root, left);
    BooleanFormula ptoRootRight = slmgr.makePointsTo(imgr.add(root, imgr.makeNumber(1)), right);
    BooleanFormula ptoLeftNil = slmgr.makePointsTo(left, nil);
    BooleanFormula ptoLeftRight = slmgr.makePointsTo(left, right);

    // tree: (root -> left) * (root+1 -> right) * (left -> nil) * (left -> right)
    BooleanFormula sepTree =
        makeStarAll(ImmutableList.of(ptoRootLeft, ptoRootRight, ptoLeftNil, ptoLeftRight));

    // left has two different values -> invalid
    assertThatFormula(sepTree).isUnsatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testListValid() throws InterruptedException, SolverException {
    requireSepNil();

    IntegerFormula nil = slmgr.makeNilElement(FormulaType.IntegerType);
    List<IntegerFormula> nodes = new ArrayList<>();
    for (int i = 0; i <= 10; i++) {
      nodes.add(imgr.makeVariable("n" + i));
    }
    List<BooleanFormula> ptos = new ArrayList<>();
    for (int i = 0; i < nodes.size() - 1; i++) {
      ptos.add(slmgr.makePointsTo(nodes.get(i), nodes.get(i + 1)));
    }
    BooleanFormula ptoLastNil = slmgr.makePointsTo(Iterables.getLast(nodes), nil);

    // list: n1 -> n2 -> ... -> nil
    BooleanFormula sepTree = slmgr.makeStar(makeStarAll(ptos), ptoLastNil);
    assertThatFormula(sepTree).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Test
  public void testListValidCycle() throws InterruptedException, SolverException {
    List<IntegerFormula> nodes = new ArrayList<>();
    for (int i = 0; i <= 10; i++) {
      nodes.add(imgr.makeVariable("n" + i));
    }
    List<BooleanFormula> ptos = new ArrayList<>();
    for (int i = 0; i < nodes.size() - 1; i++) {
      ptos.add(slmgr.makePointsTo(nodes.get(i), nodes.get(i + 1)));
    }
    BooleanFormula ptoLastNil =
        slmgr.makePointsTo(Iterables.getLast(nodes), Iterables.getFirst(nodes, null));

    // list: (n1 -> n2 -> ... -> n10) * cycle: (n10 -> n1)
    BooleanFormula sepTree = slmgr.makeStar(makeStarAll(ptos), ptoLastNil);
    assertThatFormula(sepTree).isSatisfiable(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }
}
