package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import com.microsoft.z3.*;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import java.lang.reflect.Constructor;
import java.util.HashMap;
import java.util.Set;
import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;

@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access"})
@Ignore("prevent this class being executed as testcase by ant")
public class Z3ProofsTest {

  private Z3SolverContext context;
  private Z3FormulaManager mgr;
  private Z3BooleanFormulaManager bmgr;
  private ProverEnvironment q1q2prover;

  @Before
  public void setUpSolverContext() throws Exception {
    //Z3 requires to enable proof generation in the configuration of the context
    Configuration config =
        Configuration.builder().setOption("solver.z3.requireProofs", "true").build();
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();

    // Create new context with SMTInterpol
    context =
        Z3SolverContext.create(
            logger,
            config,
            shutdown.getNotifier(),
            null, // no logfile
            42, // random seed value
            FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN,
            NonLinearArithmetic.USE,
            NativeLibraries::loadLibrary);
    mgr = (Z3FormulaManager) context.getFormulaManager();
    bmgr = (Z3BooleanFormulaManager) mgr.getBooleanFormulaManager();
  }

  @Before
  public void setUpQ1Q2Prover() throws InterruptedException {
    // example from the 2022 RESOLUTE paper
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");

    q1q2prover = context.newProverEnvironment0(Set.of());

    try {
      q1q2prover.addConstraint(bmgr.or(bmgr.not(q1), q2));
      q1q2prover.addConstraint(q1);
      q1q2prover.addConstraint(bmgr.not(q2));
      assertTrue(q1q2prover.isUnsat());

    } catch (SolverException pE) {
      throw new RuntimeException(pE);
    }
  }

  @After
  public void closeSolver() {
    if (context != null) {
      context.close();
    }
  }

  @Test
  public void getProofTest() throws InterruptedException {
    ProofNode proof = q1q2prover.getProof();
    assertThat(proof).isNotNull();
  }

  @Test
  public void getChildrenTest() {
    ProofNode proof = q1q2prover.getProof();
    assertThat(proof).isNotNull();
    assertThat(proof.getChildren()).isNotEmpty();
    assertThat(proof.getChildren().get(0)).isNotNull();
  }

  @Test
  public void getProofRuleTest() {
    ProofNode proof = q1q2prover.getProof();
    assertThat(proof).isNotNull();
    assertThat(proof.getRule()).isNotNull();
    assertThat(proof.getRule()).isEqualTo(Z3ProofRule.UNIT_RESOLUTION);
  }

  @Test
  public void getFormulaTest() {
    ProofNode proof = q1q2prover.getProof();
    assertThat(proof).isNotNull();
    assertThat(proof.getFormula()).isNotNull();
    assertThat(proof.getFormula()).isEqualTo(bmgr.makeFalse());
  }

  @Test
  public void Z3handleTransitivityTest() {
    BooleanFormula f1 = bmgr.makeVariable("f1");
    BooleanFormula f2 = bmgr.makeVariable("f2");
    BooleanFormula f3 = bmgr.makeVariable("f3");
    BooleanFormula equiv1 = bmgr.equivalence(f1, f2);
    BooleanFormula equiv2 = bmgr.equivalence(f2, f3);
    BooleanFormula equiv3 = bmgr.equivalence(f1, f3);

    Z3ProofNode pn = new Z3ProofNode(equiv3, Z3ProofRule.TRANSITIVITY);
    pn.addChild(new Z3ProofNode(equiv1, Z3ProofRule.ASSERTED));
    pn.addChild(new Z3ProofNode(equiv2, Z3ProofRule.ASSERTED));



    Z3ToResoluteProofConverter pc = new Z3ToResoluteProofConverter(mgr);

    ProofNode res = pc.handleTransitivity(pn);

   assertThat(res).isNotNull();
  }
}
