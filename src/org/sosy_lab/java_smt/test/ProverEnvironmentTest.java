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
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.CVC4;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.CVC5;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.MATHSAT5;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.OPENSMT;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.PRINCESS;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.SMTINTERPOL;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.Z3;
import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;
import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE;
import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.ASSUMED_FORMULAS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.AXIOM;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.CLOSING_CONSTRAINT;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.CONSTANTS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.CONSTANT_DIFF;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.CUT_FORMULA;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.DEFINING_EQUATION;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.DISCHARGED_ATOMS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.DIVISIBILITY;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.ELIM_CONSTANT;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.EQUATION;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.EQUATIONS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.EQ_CASES;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.EXPANDED_INFERENCES;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.FACTOR;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.INEQUALITY;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.INFERENCES;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.INSTANCE_FORMULA;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.INSTANCE_TERMS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.LEFT_ATOM;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.LEFT_COEFFICIENT;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.LEFT_FORMULA;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.LEFT_INEQUALITY;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.LEMMA_FORMULA;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.LOCAL_ASSUMED_FORMULAS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.LOCAL_BOUND_CONSTANTS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.LOCAL_PROVIDED_FORMULAS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.NEW_CONSTANTS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.NEW_SYMBOL;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.OLD_SYMBOL;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.OMEGA_BOUNDS_A;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.OMEGA_BOUNDS_B;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.OMEGA_STRENGTHEN_CASES;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.PROVIDED_FORMULAS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.QUANTIFIED_FORMULA;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.RESULT;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.RIGHT_ATOM;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.RIGHT_COEFFICIENT;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.RIGHT_FORMULA;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.RIGHT_INEQUALITY;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.SPLIT_FORMULA;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.SUBST;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.TARGET_LITERAL;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.THEORY;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.THEORY_AXIOMS;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.WEAK_INEQUALITY;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.Set;
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
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaSolverContext;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorSolverContext;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4SolverContext;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtSolverContext;
import org.sosy_lab.java_smt.solvers.princess.PrincessProofRule;
import org.sosy_lab.java_smt.solvers.yices2.Yices2SolverContext;

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
  public void unsatCoreWithAssumptionsNullTest() {
    requireUnsatCore();
    assume()
        .withMessage(
            "Solver %s does not support unsat core generation over assumptions", solverToUse())
        .that(solverToUse())
        .isNoneOf(PRINCESS, CVC4, CVC5, OPENSMT);

    try (ProverEnvironment pe =
        context.newProverEnvironment(GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
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

    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    }
  }

  @Test
  public void testGetComplexRationalNumeralAndUFProof()
      throws InterruptedException, SolverException {
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
      assertTrue(prover.isUnsat());

      // Retrieve and verify proof
      Proof proof = prover.getProof();
      checkProof(proof);

    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    }
  }

  @Test
  public void proofOfTrueTest() throws InterruptedException, SolverException {
    requireProofGeneration();

    BooleanFormula tru = bmgr.makeTrue();

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(tru);
      assertThat(prover.isUnsat()).isFalse();

      Proof proof = prover.getProof();
      assertThat(proof).isNotNull();

    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    } catch (IllegalStateException ie) {
      // this should be thrown as getProof was called when last evaluation was SAT
    }
  }

  // TODO: Mathsat5 does not produce a msat_manager. It adds null to the asserted formulas when
  //  adding the constraint for false.
  @Test
  public void proofOfFalseTest() throws InterruptedException, SolverException {
    requireProofGeneration();
    assume().that(solverToUse()).isNotEqualTo(MATHSAT5);

    BooleanFormula bottom = bmgr.makeFalse();

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(bottom);
      assertThat(prover.isUnsat()).isTrue();

      Proof proof = prover.getProof();
      assertThat(proof).isNotNull();

    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    } catch (IllegalStateException ie) {
      // this should be thrown as getProof was called when last evaluation was SAT
    }
  }

  @Test
  public void testGetSimpleIntegerProof() throws InterruptedException, SolverException {
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

    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    }
  }

  @Test
  public void getProofAfterGetProofAndAddingAssertionsTest()
      throws InterruptedException, SolverException {
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

      assertNotEquals(proof, secondProof);

    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    }
  }

  // TODO: MathSAT5 produces a proof with a CLAUSE_HYP rule without children, investigate why this
  // coudl be and how to process
  @Test
  public void getProofAfterGetProofClearingStackAndAddingDifferentAssertionsTest()
      throws InterruptedException, SolverException {
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

      assertNotEquals(proof, secondProof);

    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    }
  }

  @Test
  public void getProofWithoutProofProductionEnabledTest()
      throws InterruptedException, SolverException {
    requireProofGeneration();

    BooleanFormula bottom = bmgr.makeFalse();

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.addConstraint(bottom);
      assertThat(prover.isUnsat()).isTrue();

      Proof proof = prover.getProof();

      // Z3 always has proof generation on
      if (solverToUse().equals(Z3)) {
        assertThat(proof.getFormula()).isNotNull();
      }

    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
    } catch (IllegalStateException e) {
      assertThat(e).hasMessageThat().isEqualTo("Please set the prover option GENERATE_PROOFS.");
    }
  }

  // This test is based on the bvIsZeroAfterShiftLeft() test in BitvectorFormulaManagerTest
  @Test
  public void getBitVectorProofTest() throws InterruptedException, SolverException {
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

  private Proof findanyProofLeaf(Proof pn) {
    if (pn.isLeaf()) {
      return pn;
    }
    return findanyProofLeaf(pn.getChildren().stream().findFirst().get());
  }

  // Traverses a proof and asserts that certain values are not null, instances, etc.
  private void checkProof(Proof root) {
    assertThat(root).isNotNull();

    Deque<Proof> stack = new ArrayDeque<>();
    stack.push(root);

    while (!stack.isEmpty()) {
      Proof proof = stack.pop();
      ProofRule rule = proof.getRule();
      Optional<Formula> formula = proof.getFormula();

      assertThat(rule).isNotNull();
      assertThat(rule).isInstanceOf(ProofRule.class);
      assertThat(proof.getChildren()).isNotNull();
      if (solverToUse().equals(SMTINTERPOL)) {

      } else if (solverToUse().equals(PRINCESS)) {
        assertThat(formula.isEmpty()).isTrue();
      } else if (solverToUse().equals(MATHSAT5)) {
        // do nothing, optional proof may not provide a formula
      } else {
        assertThat(formula.isPresent()).isTrue();
      }

      if (solverToUse().equals(PRINCESS) && rule instanceof PrincessProofRule) {
        checkPrincessSpecificFields((PrincessProofRule) rule);
      }

      for (Proof child : proof.getChildren()) {
        assertThat(child).isNotNull();
        stack.push(child);
      }
    }
  }

  // Performs all necessary feature checks for Princess rules, validating type and existence of
  // fields retrieved via getSpecificFields.
  @SuppressWarnings("unchecked")
  private void checkPrincessSpecificFields(PrincessProofRule rule) {

    String ruleName = rule.getName();
    try {
      // Common fields
      if (ruleName.contains("CERTIFICATE")) {
        assertThat(rule.getSpecificField(CLOSING_CONSTRAINT)).isInstanceOf(Formula.class);
        assertThat(rule.getSpecificField(LOCAL_ASSUMED_FORMULAS)).isInstanceOf(Set.class);
        assertThat(rule.getSpecificField(ASSUMED_FORMULAS)).isInstanceOf(Set.class);
        assertThat(rule.getSpecificField(LOCAL_PROVIDED_FORMULAS)).isInstanceOf(List.class);
        assertThat(rule.getSpecificField(LOCAL_BOUND_CONSTANTS)).isInstanceOf(Set.class);
        assertThat(rule.getSpecificField(CONSTANTS)).isInstanceOf(Set.class);
        assertThat(rule.getSpecificField(THEORY_AXIOMS)).isInstanceOf(Set.class);

      } else if (ruleName.contains("INFERENCE")) {
        assertThat(rule.getSpecificField(ASSUMED_FORMULAS)).isInstanceOf(Set.class);
        assertThat(rule.getSpecificField(PROVIDED_FORMULAS)).isInstanceOf(Set.class);
        assertThat(rule.getSpecificField(LOCAL_BOUND_CONSTANTS)).isInstanceOf(Set.class);
        assertThat(rule.getSpecificField(CONSTANTS)).isInstanceOf(Set.class);
      }

      // Specific fields per rule type
      switch (ruleName) {
        case "BETA_CERTIFICATE":
          assertThat(rule.getSpecificField(LEFT_FORMULA)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RIGHT_FORMULA)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(LEMMA_FORMULA)).isNotNull();
          break;
        case "CUT_CERTIFICATE":
          assertThat(rule.getSpecificField(CUT_FORMULA)).isInstanceOf(Formula.class);
          break;
        case "OMEGA_CERTIFICATE":
          assertThat(rule.getSpecificField(ELIM_CONSTANT)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(OMEGA_BOUNDS_A)).isInstanceOf(List.class);
          assertThat(rule.getSpecificField(OMEGA_BOUNDS_B)).isInstanceOf(List.class);
          assertThat(rule.getSpecificField(OMEGA_STRENGTHEN_CASES)).isInstanceOf(List.class);
          break;
        case "SPLIT_EQ_CERTIFICATE":
          assertThat(rule.getSpecificField(LEFT_INEQUALITY)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RIGHT_INEQUALITY)).isInstanceOf(Formula.class);
          break;
        case "STRENGTHEN_CERTIFICATE":
          assertThat(rule.getSpecificField(WEAK_INEQUALITY)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(EQ_CASES)).isInstanceOf(BigInteger.class);
          break;
        case "BRANCH_INFERENCE_CERTIFICATE":
          List<ProofRule> inferences = rule.getSpecificField(INFERENCES);
          assertThat(inferences).isNotNull();
          assertThat(inferences).isNotEmpty();
          for (ProofRule inference : inferences) {
            assertThat(inference).isInstanceOf(PrincessProofRule.class);
            checkPrincessSpecificFields((PrincessProofRule) inference);
          }
          break;

        case "ALPHA_INFERENCE":
          assertThat(rule.getSpecificField(SPLIT_FORMULA)).isInstanceOf(Formula.class);
          break;
        case "ANTI_SYMMETRY_INFERENCE":
          assertThat(rule.getSpecificField(LEFT_INEQUALITY)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RIGHT_INEQUALITY)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
          break;
        case "COLUMN_REDUCE_INFERENCE":
          assertThat(rule.getSpecificField(OLD_SYMBOL)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(NEW_SYMBOL)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(DEFINING_EQUATION)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(SUBST)).isNotNull();
          break;
        case "COMBINE_EQUATIONS_INFERENCE":
          assertThat(rule.getSpecificField(EQUATIONS)).isInstanceOf(List.class);
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
          break;
        case "COMBINE_INEQUALITIES_INFERENCE":
          assertThat(rule.getSpecificField(LEFT_COEFFICIENT)).isInstanceOf(BigInteger.class);
          assertThat(rule.getSpecificField(LEFT_INEQUALITY)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RIGHT_COEFFICIENT)).isInstanceOf(BigInteger.class);
          assertThat(rule.getSpecificField(RIGHT_INEQUALITY)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
          break;
        case "DIRECT_STRENGTHEN_INFERENCE":
          assertThat(rule.getSpecificField(INEQUALITY)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(EQUATION)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
          break;
        case "DIV_RIGHT_INFERENCE":
          assertThat(rule.getSpecificField(DIVISIBILITY)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
          break;
        case "GROUND_INST_INFERENCE":
          assertThat(rule.getSpecificField(QUANTIFIED_FORMULA)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(INSTANCE_TERMS)).isInstanceOf(List.class);
          assertThat(rule.getSpecificField(INSTANCE_FORMULA)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(DISCHARGED_ATOMS)).isInstanceOf(List.class);
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
          break;
        case "MACRO_INFERENCE":
          List<PrincessProofRule> expandedInferences =
              (List<PrincessProofRule>) rule.getSpecificField(EXPANDED_INFERENCES);
          assertThat(expandedInferences).isInstanceOf(List.class);
          for (PrincessProofRule subInf : expandedInferences) {
            checkPrincessSpecificFields(subInf);
          }
          break;
        case "PRED_UNIFY_INFERENCE":
          assertThat(rule.getSpecificField(LEFT_ATOM)).isNotNull();
          assertThat(rule.getSpecificField(RIGHT_ATOM)).isNotNull();
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
          break;
        case "QUANTIFIER_INFERENCE":
          assertThat(rule.getSpecificField(QUANTIFIED_FORMULA)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(NEW_CONSTANTS)).isInstanceOf(List.class);
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
          break;
        case "REDUCE_INFERENCE":
          assertThat(rule.getSpecificField(EQUATIONS)).isInstanceOf(List.class);
          assertThat(rule.getSpecificField(TARGET_LITERAL)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
        case "REDUCE_PRED_INFERENCE":
          assertThat(rule.getSpecificField(EQUATIONS)).isInstanceOf(List.class);
          assertThat(rule.getSpecificField(TARGET_LITERAL)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
          break;
        case "SIMP_INFERENCE":
          assertThat(rule.getSpecificField(TARGET_LITERAL)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(RESULT)).isInstanceOf(Formula.class);
          assertThat(rule.getSpecificField(CONSTANT_DIFF)).isInstanceOf(BigInteger.class);
          assertThat(rule.getSpecificField(FACTOR)).isInstanceOf(BigInteger.class);
          break;
        case "THEORY_AXIOM_INFERENCE":
          assertThat(rule.getSpecificField(THEORY)).isNotNull();
          assertThat(rule.getSpecificField(AXIOM)).isInstanceOf(Formula.class);
          break;
        case "CLOSE_CERTIFICATE":
          // No specific fields to check here.
          break;
        default:
          // Either a rule without specific fields (like PARTIAL_CERTIFICATE_INFERENCE)
          // or a new/unhandled one.
          break;
      }
    } catch (IllegalArgumentException e) {
      // This is expected if a specific proof does not contain an optional field.
    }
  }
}
