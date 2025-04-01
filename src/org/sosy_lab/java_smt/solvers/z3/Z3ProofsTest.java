package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertTrue;

import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.ProofNode;

@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access"})
@Ignore("prevent this class being executed as testcase by ant")
public class Z3ProofsTest {

  private SolverContext context;
  private Z3FormulaManager mgr;
  private Z3BooleanFormulaManager bmgr;
  private ProverEnvironment q1q2prover;

  @Before
  public void setUpSolverContext() throws Exception {
    // Z3 requires to enable proof generation in the configuration of the context
    Configuration config =
        Configuration.builder().setOption("solver.z3.requireProofs", "true").build();
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();

    context =
        SolverContextFactory.createSolverContext(
            config, logger, shutdown.getNotifier(), SolverContextFactory.Solvers.Z3);

    mgr = (Z3FormulaManager) context.getFormulaManager();
    bmgr = (Z3BooleanFormulaManager) mgr.getBooleanFormulaManager();
  }

  @Before
  public void setUpQ1Q2Prover() throws InterruptedException {
    // (declare-fun q1 () Bool)
    // (declare-fun q2 () Bool)
    // (assert (or (not q1) q2))
    // (assert q1)
    // (assert (not q2))
    // (check-sat)
    // (get-proof)
    // This problem is from the paper found in
    // https://ultimate.informatik.uni-freiburg.de/smtinterpol/proofs.html
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");

    q1q2prover = context.newProverEnvironment();

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
  public void getProofTest() throws InterruptedException, SolverException {
    ProofNode proof = q1q2prover.getProof();
    assertThat(proof).isNotNull();
  }

  @Test
  public void getChildrenTest() throws SolverException, InterruptedException {
    ProofNode proof = q1q2prover.getProof();
    assertThat(proof).isNotNull();
    assertThat(proof.getChildren()).isNotEmpty();
    assertThat(proof.getChildren().get(0)).isNotNull();
  }

  @Test
  public void getProofRuleTest() throws SolverException, InterruptedException {
    ProofNode proof = q1q2prover.getProof();
    assertThat(proof).isNotNull();
    assertThat(proof.getRule()).isNotNull();
    assertThat(proof.getRule()).isEqualTo(Z3ProofRule.UNIT_RESOLUTION);
  }

  @Test
  public void getFormulaTest() throws SolverException, InterruptedException {
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

    Z3ProofDag.Z3ProofNode pn = new Z3ProofDag.Z3ProofNode(equiv3, Z3ProofRule.TRANSITIVITY);
    pn.addChild(new Z3ProofDag.Z3ProofNode(equiv1, Z3ProofRule.ASSERTED));
    pn.addChild(new Z3ProofDag.Z3ProofNode(equiv2, Z3ProofRule.ASSERTED));

    Z3ToResoluteProofConverter pc = new Z3ToResoluteProofConverter(mgr);

    ProofNode res = pc.handleTransitivity(pn);

    assertThat(res).isNotNull();
  }
}
