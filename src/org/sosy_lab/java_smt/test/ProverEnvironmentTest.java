// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.CVC4;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.CVC5;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.MATHSAT5;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.OPENSMT;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.PRINCESS;
import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;
import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE;
import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import org.junit.Test;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

public class ProverEnvironmentTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void assumptionsTest() throws SolverException, InterruptedException {
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula c = bmgr.makeVariable("c");

    try (ProverEnvironment pe = context.newProverEnvironment()) {
      pe.push();
      pe.addConstraint(bmgr.or(b, bmgr.makeBoolean(false)));
      pe.addConstraint(c);
      assertThat(pe.isUnsat()).isFalse();
      assertThat(pe.isUnsatWithAssumptions(ImmutableList.of(bmgr.not(b)))).isTrue();
      assertThat(pe.isUnsatWithAssumptions(ImmutableList.of(b))).isFalse();
    }
  }

  @Test
  public void assumptionsWithModelTest() throws SolverException, InterruptedException {
    assume()
        .withMessage("MathSAT can't construct models for SAT check with assumptions")
        .that(solver)
        .isNotEqualTo(MATHSAT5);
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula c = bmgr.makeVariable("c");

    try (ProverEnvironment pe = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      pe.push();
      pe.addConstraint(bmgr.or(b, bmgr.makeBoolean(false)));
      pe.addConstraint(c);
      assertThat(pe.isUnsat()).isFalse();
      assertThat(pe.isUnsatWithAssumptions(ImmutableList.of(bmgr.not(b)))).isTrue();
      assertThat(pe.isUnsatWithAssumptions(ImmutableList.of(b))).isFalse();
      try (Model m = pe.getModel()) {
        assertThat(m.evaluate(c)).isTrue();
      }
    }
  }

  @Test
  public void unsatCoreTest() throws SolverException, InterruptedException {
    requireUnsatCore();
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment(GENERATE_UNSAT_CORE)) {
      unsatCoreTest0(pe);
    }
  }

  @Test
  public void unsatCoreTestForInterpolation() throws SolverException, InterruptedException {
    requireUnsatCore();
    requireInterpolation();
    try (BasicProverEnvironment<?> pe =
        context.newProverEnvironmentWithInterpolation(GENERATE_UNSAT_CORE)) {
      unsatCoreTest0(pe);
    }
  }

  @Test
  public void unsatCoreTestForOptimizationProver() throws SolverException, InterruptedException {
    requireUnsatCore();
    requireOptimization();
    try (BasicProverEnvironment<?> pe =
        context.newOptimizationProverEnvironment(GENERATE_UNSAT_CORE)) {
      unsatCoreTest0(pe);
    }
  }

  private void unsatCoreTest0(BasicProverEnvironment<?> pe)
      throws InterruptedException, SolverException {
    requireIntegers();
    pe.push();
    pe.addConstraint(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)));
    pe.addConstraint(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(2)));
    pe.addConstraint(imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(2)));
    assertThat(pe).isUnsatisfiable();
    List<BooleanFormula> unsatCore = pe.getUnsatCore();
    assertThat(unsatCore)
        .containsExactly(
            imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(2)),
            imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)));
  }

  @Test
  public void unsatCoreWithAssumptionsNullTest() throws InterruptedException, SolverException {
    requireUnsatCore();
    assume()
        .withMessage(
            "Solver %s does not support unsat core generation over assumptions", solverToUse())
        .that(solverToUse())
        .isNoneOf(PRINCESS, CVC4, CVC5, OPENSMT);

    try (ProverEnvironment pe =
        context.newProverEnvironment(GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      pe.push(bmgr.makeFalse());
      assertThat(pe).isUnsatisfiable();
      assertThrows(NullPointerException.class, () -> pe.unsatCoreOverAssumptions(null));
    }
  }

  @Test
  public void unsatCoreWithAssumptionsTest() throws SolverException, InterruptedException {
    requireIntegers();
    requireUnsatCore();
    assume()
        .withMessage(
            "Solver %s does not support unsat core generation over assumptions", solverToUse())
        .that(solverToUse())
        .isNoneOf(PRINCESS, CVC4, CVC5, OPENSMT);
    try (ProverEnvironment pe =
        context.newProverEnvironment(GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      pe.push();
      pe.addConstraint(imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(2)));
      BooleanFormula selector = bmgr.makeVariable("b");
      pe.addConstraint(bmgr.or(selector, imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(1))));
      Optional<List<BooleanFormula>> res =
          pe.unsatCoreOverAssumptions(ImmutableList.of(bmgr.not(selector)));
      assertThat(res).isPresent();
      List<BooleanFormula> unsatCore = res.orElseThrow();
      assertThat(unsatCore).containsExactly(bmgr.not(selector));
    }
  }

  @Test
  public void testSatWithUnsatUnsatCoreOptions() throws InterruptedException, SolverException {
    requireUnsatCore();
    try (ProverEnvironment prover = context.newProverEnvironment(GENERATE_UNSAT_CORE)) {
      checkSimpleQuery(prover);
    }

    requireUnsatCoreOverAssumptions();
    try (ProverEnvironment prover =
        context.newProverEnvironment(GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      checkSimpleQuery(prover);
    }

    try (ProverEnvironment prover =
        context.newProverEnvironment(GENERATE_UNSAT_CORE, GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      checkSimpleQuery(prover);
    }
  }

  private void checkSimpleQuery(ProverEnvironment pProver)
      throws InterruptedException, SolverException {
    BooleanFormula constraint = bmgr.implication(bmgr.makeVariable("a"), bmgr.makeVariable("b"));

    {
      pProver.push(constraint);
      assertThat(pProver.isUnsat()).isFalse();
      pProver.pop();
    }

    {
      pProver.push();
      pProver.addConstraint(constraint); // Z3 crashed here
      assertThat(pProver.isUnsat()).isFalse();
      pProver.pop();
    }
  }

  @Test
  public void testGetSimpleBooleanProof() throws InterruptedException, SolverException {
    assume().that(solverToUse()).isAnyOf(CVC5, MATHSAT5);
    requireProofGeneration(); // Ensures proofs are supported
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(bmgr.or(bmgr.not(q1), q2));
      prover.addConstraint(q1);
      prover.addConstraint(bmgr.not(q2));

      assertThat(prover.isUnsat()).isTrue();

      // Test getProof()
      Proof proof = prover.getProof();
      checkProof(proof);
    }
  }

  @Test
  public void testGetComplexRationalNumeralAndUFProof()
      throws InterruptedException, SolverException {
    assume().that(solverToUse()).isAnyOf(CVC5, MATHSAT5);
    requireProofGeneration(); // Ensures proofs are supported
    requireRationals();

    // "(declare-fun x1 () Real)" +
    // "(declare-fun x2 () Real)" +
    // "(declare-fun x3 () Real)" +
    // "(declare-fun y1 () Real)" +
    // "(declare-fun y2 () Real)" +
    //  "(declare-fun y3 () Real)" +
    //  "(declare-fun b () Real)" +
    //  "(declare-fun f (Real) Real)" +
    // "(declare-fun g (Real) Real)" +
    //  "(declare-fun a () Bool)" +
    //  "(declare-fun c () Bool)" +
    //  "(assert (and a (= (+ (f y1) y2) y3) (<= y1 x1)))" +
    // "(assert (and (= x2 (g b)) (= y2 (g b)) (<= x1 y1) (< x3 y3)))" +
    // "(assert (= a (= (+ (f x1) x2) x3)))" +
    //  "(assert (and (or a c) (not c)))";
    RationalFormula x1 = mgr.makeVariable(FormulaType.RationalType, "x1");
    RationalFormula x2 = mgr.makeVariable(FormulaType.RationalType, "x2");
    RationalFormula x3 = mgr.makeVariable(FormulaType.RationalType, "x3");
    RationalFormula y1 = mgr.makeVariable(FormulaType.RationalType, "y1");
    RationalFormula y2 = mgr.makeVariable(FormulaType.RationalType, "y2");
    RationalFormula y3 = mgr.makeVariable(FormulaType.RationalType, "y3");
    RationalFormula b = mgr.makeVariable(FormulaType.RationalType, "b");
    FunctionDeclaration<RationalFormula> f =
        mgr.getUFManager().declareUF("f", FormulaType.RationalType, FormulaType.RationalType);
    FunctionDeclaration<RationalFormula> g =
        mgr.getUFManager().declareUF("g", FormulaType.RationalType, FormulaType.RationalType);
    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula c = bmgr.makeVariable("c");

    RationalFormulaManager rfmgr = mgr.getRationalFormulaManager();

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      // "(assert (and a (= (+ (f y1) y2) y3) (<= y1 x1)))"
      prover.addConstraint(
          bmgr.and(
              a,
              rfmgr.equal(rfmgr.add(mgr.makeApplication(f, y1), y2), y3),
              rfmgr.lessOrEquals(y1, x1)));
      // "(assert (and (= x2 (g b)) (= y2 (g b)) (<= x1 y1) (< x3 y3)))"
      prover.addConstraint(
          bmgr.and(
              rfmgr.equal(x2, mgr.makeApplication(g, b)),
              rfmgr.equal(y2, mgr.makeApplication(g, b)),
              rfmgr.lessOrEquals(x1, y1),
              rfmgr.lessThan(x3, y3)));
      // "(assert (= a (= (+ (f x1) x2) x3)))"
      prover.addConstraint(
          bmgr.equivalence(a, rfmgr.equal(rfmgr.add(mgr.makeApplication(f, x1), x2), x3)));
      // "(assert (and (or a c) (not c)))"
      prover.addConstraint(bmgr.and(bmgr.or(a, c), bmgr.not(c)));
      assertThat(prover.isUnsat()).isTrue();

      // Retrieve and verify proof
      Proof proof = prover.getProof();
      checkProof(proof);
    }
  }

  @Test
  public void proofOfTrueTest() throws InterruptedException, SolverException {
    assume().that(solverToUse()).isAnyOf(CVC5, MATHSAT5);
    requireProofGeneration();

    BooleanFormula tru = bmgr.makeTrue();

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(tru);
      assertThat(prover.isUnsat()).isFalse();

      @SuppressWarnings("unused")
      Proof proof = prover.getProof();
      throw new AssertionError("Expected IllegalStateException was not thrown");

    } catch (IllegalStateException e) {
      // this should be thrown as getProof was called when last evaluation
      // was SAT
    }
  }

  @Test
  public void proofOfFalseTest() throws InterruptedException, SolverException {
    requireProofGeneration();
    assume().that(solverToUse()).isAnyOf(CVC5, MATHSAT5);

    BooleanFormula bottom = bmgr.makeFalse();

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(bottom);
      assertThat(prover.isUnsat()).isTrue();

      Proof proof = prover.getProof();
      if (solverToUse().equals(MATHSAT5))
        throw new AssertionError("Expected " + "UnsupportedOperationException was not thrown");
      assertThat(proof).isNotNull();
    } catch (UnsupportedOperationException e) {
      assertThat(solverToUse().equals(MATHSAT5));
    }
  }

  @Test
  public void testGetSimpleIntegerProof() throws InterruptedException, SolverException {
    assume().that(solverToUse()).isAnyOf(CVC5, MATHSAT5);
    requireProofGeneration(); // Ensures proofs are supported
    requireIntegers();

    IntegerFormula x1 = imgr.makeVariable("x1");
    IntegerFormula two = imgr.makeNumber("2");
    IntegerFormula cero = imgr.makeNumber("0");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(imgr.equal(x1, two));
      prover.addConstraint(imgr.lessThan(x1, cero));
      assertThat(prover.isUnsat()).isTrue();

      // Test getProof()
      Proof proof = prover.getProof();
      checkProof(proof);
    }
  }

  @Test
  public void getProofAfterGetProofAndAddingAssertionsTest()
      throws InterruptedException, SolverException {
    assume().that(solverToUse()).isAnyOf(CVC5, MATHSAT5);
    requireProofGeneration(); // Ensures proofs are supported
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");
    IntegerFormula x1 = imgr.makeVariable("x1");
    IntegerFormula two = imgr.makeNumber("2");
    IntegerFormula cero = imgr.makeNumber("0");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(bmgr.or(bmgr.not(q1), q2));
      prover.addConstraint(q1);
      prover.addConstraint(bmgr.not(q2));

      assertThat(prover.isUnsat()).isTrue();

      // Test getProof()
      Proof proof = prover.getProof();
      checkProof(proof);

      // assert integer formulas and test again
      prover.addConstraint(imgr.equal(x1, two));
      prover.addConstraint(imgr.lessThan(x1, cero));

      assertThat(prover.isUnsat()).isTrue();

      // Test getProof()
      Proof secondProof = prover.getProof();
      checkProof(secondProof);

      assertThat(proof).isNotEqualTo(secondProof);
    }
  }

  // For the second proof here, MathSAT5 produces a clause-hyp node that has no formula.
  // So the resolution chain is done with the following clauses {} {x1=2} choosing the pivot x1=2.
  // See this formatted native proof:
  // Formula: null
  // Rule: res-chain
  // No. Children: 3
  // Child 1:
  //  Formula: null
  //  Rule: clause-hyp
  //  No. Children: 0
  // Child 2:
  //  Formula: (`=_int` 'x1 2)
  //  Rule: null
  //  No. Children: 0
  // Child 3:
  //  Formula: null
  //  Rule: clause-hyp
  //  No. Children: 1
  //  Child 1:
  //    Formula: (`=_int` 'x1 2)
  //    Rule: null
  //    No. Children: 0
  // To solve this, the proof transformation assigns false, as the formula for clause-hyp nodes
  // that have no children.
  @Test
  public void getProofAfterGetProofClearingStackAndAddingDifferentAssertionsTest()
      throws InterruptedException, SolverException {
    assume().that(solverToUse()).isAnyOf(CVC5, MATHSAT5);
    requireProofGeneration(); // Ensures proofs are supported
    requireIntegers();

    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");
    IntegerFormula x1 = imgr.makeVariable("x1");
    IntegerFormula two = imgr.makeNumber("2");
    IntegerFormula cero = imgr.makeNumber("0");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {

      prover.push(bmgr.or(bmgr.not(q1), q2));
      prover.push(q1);
      prover.push(bmgr.not(q2));

      assertThat(prover.isUnsat()).isTrue();

      // Test getProof()
      Proof proof = prover.getProof();
      checkProof(proof);

      prover.pop();
      prover.pop();
      prover.pop();

      // assert integer formulas and test again
      prover.push(imgr.equal(x1, two));
      prover.push(imgr.lessThan(x1, cero));

      assertThat(prover.isUnsat()).isTrue();

      // Test getProof()
      Proof secondProof = prover.getProof();
      checkProof(secondProof);

      assertThat(proof).isNotEqualTo(secondProof);
    }
  }

  @Test
  public void getProofWithoutProofProductionEnabledTest()
      throws InterruptedException, SolverException {
    assume().that(solverToUse()).isAnyOf(CVC5, MATHSAT5);
    requireProofGeneration();

    BooleanFormula bottom = bmgr.makeFalse();

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.addConstraint(bottom);
      assertThat(prover.isUnsat()).isTrue();

      @SuppressWarnings("unused")
      Proof proof = prover.getProof();
      throw new AssertionError("Expected IllegalStateException was not thrown");

    } catch (IllegalStateException e) {
      assertThat(e.getMessage()).isEqualTo("Please set the prover option GENERATE_PROOFS.");
    }
  }

  // This test is based on the bvIsZeroAfterShiftLeft() test in BitvectorFormulaManagerTest
  @Test
  public void getBitVectorProofTest() throws InterruptedException, SolverException {
    assume().that(solverToUse()).isAnyOf(CVC5, MATHSAT5);
    requireProofGeneration();
    requireBitvectors();

    BitvectorFormula one = bvmgr.makeBitvector(32, 1);

    // unsigned char
    BitvectorFormula a = bvmgr.makeVariable(8, "char_a");
    BitvectorFormula b = bvmgr.makeVariable(8, "char_b");
    BitvectorFormula rightOp = bvmgr.makeBitvector(32, 7);

    // 'cast' a to unsigned int
    a = bvmgr.extend(a, 32 - 8, false);
    b = bvmgr.extend(b, 32 - 8, false);
    a = bvmgr.or(a, one);
    b = bvmgr.or(b, one);
    a = bvmgr.extract(a, 7, 0);
    b = bvmgr.extract(b, 7, 0);
    a = bvmgr.extend(a, 32 - 8, false);
    b = bvmgr.extend(b, 32 - 8, false);

    a = bvmgr.shiftLeft(a, rightOp);
    b = bvmgr.shiftLeft(b, rightOp);
    a = bvmgr.extract(a, 7, 0);
    b = bvmgr.extract(b, 7, 0);
    BooleanFormula f = bmgr.not(bvmgr.equal(a, b));

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(f);
      assertThat(prover.isUnsat()).isTrue();

      // Test getProof()
      Proof proof = prover.getProof();
      checkProof(proof);
    }
  }

  // This test is based on the testIntIndexIntValue() test in ArrayFormulaManagerTest
  @Test
  public void getArrayProofTest() throws InterruptedException, SolverException {
    assume().that(solverToUse()).isAnyOf(CVC5, MATHSAT5);
    requireProofGeneration();
    requireIntegers();
    requireArrays();

    // (arr2 = store(arr1, 4, 2)) & !(select(arr2, 4) = 2)
    ArrayFormulaType<IntegerFormula, IntegerFormula> type =
        FormulaType.getArrayType(IntegerType, IntegerType);
    IntegerFormula num2 = imgr.makeNumber(2);
    IntegerFormula num4 = imgr.makeNumber(4);
    ArrayFormula<IntegerFormula, IntegerFormula> arr1 = amgr.makeArray("arr1", type);
    ArrayFormula<IntegerFormula, IntegerFormula> arr2 = amgr.makeArray("arr2", type);
    BooleanFormula query =
        bmgr.and(
            amgr.equivalence(arr2, amgr.store(arr1, num4, num2)),
            bmgr.not(imgr.equal(num2, amgr.select(arr2, num4))));

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(query);
      assertThat(prover.isUnsat()).isTrue();

      // Test getProof()
      Proof proof = prover.getProof();
      checkProof(proof);
    }
  }

  // Traverses a proof and asserts that certain values are not null, instances, etc.
  private void checkProof(Proof pRoot) {
    assertThat(pRoot).isNotNull();

    Deque<Proof> stack = new ArrayDeque<>();
    stack.push(pRoot);

    while (!stack.isEmpty()) {
      Proof proof = stack.pop();
      Optional<ProofRule> rule = proof.getRule();
      Optional<Formula> formula = proof.getFormula();

      if (rule.isPresent()) assertThat(rule.get()).isInstanceOf(ProofRule.class);
      assertThat(proof.getChildren()).isNotNull();
      if (solverToUse().equals(CVC5)) assertThat(formula.isPresent()).isTrue();

      for (Proof child : proof.getChildren()) {
        assertThat(child).isNotNull();
        stack.push(child);
      }
    }
  }
}
