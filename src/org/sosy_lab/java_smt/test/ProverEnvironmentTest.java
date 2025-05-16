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
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.SMTINTERPOL;
import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE;
import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.Optional;
import org.junit.Test;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.Proof.Subproof;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaSolverContext;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorSolverContext;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4SolverContext;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtSolverContext;
import org.sosy_lab.java_smt.solvers.princess.PrincessSolverContext;
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
  public void testSimpleProof() throws InterruptedException, SolverException {
    requireProofGeneration(); // Ensures proofs are supported
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(bmgr.or(bmgr.not(q1), q2));
      prover.addConstraint(q1);
      prover.addConstraint(bmgr.not(q2));

      assertThat(prover.isUnsat()).isTrue();

      // Test getProof()
      Subproof proof = prover.getProof();
      assertThat(proof).isNotNull();

      // Test getRule()
      assertThat(proof.getRule()).isNotNull();
      assertThat(proof.getRule()).isInstanceOf(ProofRule.class);

      // Test getFormula(), the root should always be false
      if (solverToUse().equals(SMTINTERPOL)) {
        assertThat(proof.getFormula()).isNull();
      } else {
        assertThat(proof.getFormula()).isEqualTo(bmgr.makeFalse());
      }

      // Test getArguments()
      assertThat(proof.getArguments()).isNotNull();
      assertThat(proof.getArguments()).isNotEmpty();

      // Test isLeaf()
      assertThat(proof.isLeaf()).isFalse();
      Subproof leaf = findanyProofLeaf(proof);
      assertThat(leaf).isNotNull();
      assertThat(leaf.isLeaf()).isTrue();

    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(PrincessSolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    }
  }

  @Test
  public void testComplexProof() throws InterruptedException, SolverException {
    requireProofGeneration(); // Ensures proofs are supported

    RationalFormula x1 = mgr.makeVariable(FormulaType.RationalType, "x1");
    NumeralFormula x2 = mgr.makeVariable(FormulaType.RationalType, "x2");
    RationalFormula x3 = mgr.makeVariable(FormulaType.RationalType, "x3");
    RationalFormula y1 = mgr.makeVariable(FormulaType.RationalType, "y1");
    NumeralFormula y2 = mgr.makeVariable(FormulaType.RationalType, "y2");
    RationalFormula y3 = mgr.makeVariable(FormulaType.RationalType, "y3");
    RationalFormula b = mgr.makeVariable(FormulaType.RationalType, "b");

    FunctionDeclaration<RationalFormula> f =
        mgr.getUFManager().declareUF("f", FormulaType.RationalType, FormulaType.RationalType);
    FunctionDeclaration<RationalFormula> g =
        mgr.getUFManager().declareUF("g", FormulaType.RationalType, FormulaType.RationalType);

    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula c = bmgr.makeVariable("c");

    rmgr = mgr.getRationalFormulaManager();

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      // Add constraints
      prover.addConstraint(
          bmgr.and(
              a,
              rmgr.equal(rmgr.add((NumeralFormula) mgr.makeApplication(f, y1), y2), y3),
              rmgr.lessOrEquals(y1, x1)));
      prover.addConstraint(
          bmgr.and(
              rmgr.equal(x2, (NumeralFormula) mgr.makeApplication(g, b)),
              rmgr.equal(y2, (NumeralFormula) mgr.makeApplication(g, b)),
              rmgr.lessOrEquals(x1, y1),
              rmgr.lessThan(x3, y3)));
      prover.addConstraint(
          bmgr.equivalence(
              a, rmgr.equal(rmgr.add((NumeralFormula) mgr.makeApplication(f, x1), x2), x3)));
      prover.addConstraint(bmgr.and(bmgr.or(a, c), bmgr.not(c)));

      // Check unsatisfiability
      assertThat(prover.isUnsat()).isTrue();

      // Retrieve and verify proof
      Subproof proof = prover.getProof();
      assertThat(proof).isNotNull();

      // Root formula check
      if (solverToUse().equals(SMTINTERPOL)) {
        assertThat(proof.getFormula()).isNull();
      } else {
        assertThat(proof.getFormula()).isEqualTo(bmgr.makeFalse());
      }

      // Rule check
      assertThat(proof.getRule()).isNotNull();
      assertThat(proof.getRule()).isInstanceOf(ProofRule.class);

      // Arguments check
      assertThat(proof.getArguments()).isNotNull();
      assertThat(proof.getArguments()).isNotEmpty();

      // Leaf check
      assertThat(proof.isLeaf()).isFalse();
      Subproof leaf = findanyProofLeaf(proof);
      assertThat(leaf).isNotNull();
      assertThat(leaf.isLeaf()).isTrue();

    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(PrincessSolverContext.class)
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

      Subproof proof = prover.getProof();


    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(PrincessSolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    } catch(IllegalStateException ie){
      //this should be thrown as getProof was called when last evaluation was SAT
    }
  }

  @Test
  public void proofOfFalseTest() throws InterruptedException, SolverException {
    requireProofGeneration();

    BooleanFormula bottom = bmgr.makeFalse();

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_PROOFS)) {
      prover.addConstraint(bottom);
      assertThat(prover.isUnsat()).isTrue();

      Subproof proof = prover.getProof();
      assertThat(proof).isNotNull();


    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(PrincessSolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    } catch(IllegalStateException ie){
      //this should be thrown as getProof was called when last evaluation was SAT
    }
  }

  @Test
  public void proofAfterProofTest() throws InterruptedException, SolverException {
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
      Subproof proof = prover.getProof();
      assertThat(proof).isNotNull();

      // Test getRule()
      assertThat(proof.getRule()).isNotNull();
      assertThat(proof.getRule()).isInstanceOf(ProofRule.class);

      // Test getFormula(), the root should always be false
      if (solverToUse().equals(SMTINTERPOL)) {
        assertThat(proof.getFormula()).isNull();
      } else {
        assertThat(proof.getFormula()).isEqualTo(bmgr.makeFalse());
      }

      // Test getArguments()
      assertThat(proof.getArguments()).isNotNull();
      assertThat(proof.getArguments()).isNotEmpty();

      // Test isLeaf()
      assertThat(proof.isLeaf()).isFalse();
      Subproof leaf = findanyProofLeaf(proof);
      assertThat(leaf).isNotNull();
      assertThat(leaf.isLeaf()).isTrue();

      //assert integer formulas and test again
      prover.addConstraint(imgr.equal(x1, two));
      prover.addConstraint(imgr.lessThan(x1, cero));

      assertThat(prover.isUnsat()).isTrue();

      // Test getProof()
      proof = prover.getProof();
      assertThat(proof).isNotNull();

      // Test getRule()
      assertThat(proof.getRule()).isNotNull();
      assertThat(proof.getRule()).isInstanceOf(ProofRule.class);

      // Test getFormula(), the root should always be false
      if (solverToUse().equals(SMTINTERPOL)) {
        assertThat(proof.getFormula()).isNull();
      } else {
        assertThat(proof.getFormula()).isEqualTo(bmgr.makeFalse());
      }

      // Test getArguments()
      assertThat(proof.getArguments()).isNotNull();
      assertThat(proof.getArguments()).isNotEmpty();

      // Test isLeaf()
      assertThat(proof.isLeaf()).isFalse();
      leaf = findanyProofLeaf(proof);
      assertThat(leaf).isNotNull();
      assertThat(leaf.isLeaf()).isTrue();



    } catch (UnsupportedOperationException e) {
      assertThat(e)
          .hasMessageThat()
          .isEqualTo("Proof generation is not available for the current solver.");
      Class<?> contextClass = context.getClass();
      boolean isExpected =
          contextClass.equals(CVC4SolverContext.class)
              || contextClass.equals(PrincessSolverContext.class)
              || contextClass.equals(OpenSmtSolverContext.class)
              || contextClass.equals(BoolectorSolverContext.class)
              || contextClass.equals(BitwuzlaSolverContext.class)
              || contextClass.equals(Yices2SolverContext.class);
      assertThat(isExpected).isTrue();
    }
  }


  private Subproof findanyProofLeaf(Subproof pn) {
    if (pn.isLeaf()) {
      return pn;
    }
    return findanyProofLeaf(pn.getArguments().stream().findFirst().get());
  }
}
