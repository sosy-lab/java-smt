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

  @Before
  public void setUpSolver() throws Exception {
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

  @After
  public void closeSolver() {
    if (context != null) {
      context.close();
    }
  }

  @Test
  public void getProofTest() throws InterruptedException {
    // example from the 2022 RESOLUTE paper
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");

    ProverEnvironment prover = context.newProverEnvironment0(Set.of());
    // Z3TheoremProver prover =
    //    (Z3TheoremProver) context.newProverEnvironment0(Set.of(ProverOptions
    //    .GENERATE_UNSAT_CORE));
    try {
      System.out.println("proofs enabled: " + context.getGenerateProofs());
      prover.addConstraint(bmgr.or(bmgr.not(q1), q2));
      prover.addConstraint(q1);
      prover.addConstraint(bmgr.not(q2));
      assertTrue(prover.isUnsat());

      ProofNode proof = prover.getProof();
      assertThat(proof).isNotNull();
    } catch (SolverException pE) {
      throw new RuntimeException(pE);
    }
  }

  @Test
  public void printProofTest() throws InterruptedException {
    // example from the 2022 RESOLUTE paper
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");

    ProverEnvironment prover = context.newProverEnvironment0(Set.of());
    // Z3TheoremProver prover =
    //    (Z3TheoremProver) context.newProverEnvironment0(Set.of(ProverOptions
    //    .GENERATE_UNSAT_CORE));
    try {
      System.out.println("proofs enabled: " + context.getGenerateProofs());
      prover.addConstraint(bmgr.or(bmgr.not(q1), q2));
      prover.addConstraint(q1);
      prover.addConstraint(bmgr.not(q2));
      assertTrue(prover.isUnsat());

      ProofNode proof = prover.getProof();
      assertThat(proof).isNotNull();

      System.out.println(((Z3ProofNode) proof).asString());
    } catch (SolverException pE) {
      throw new RuntimeException(pE);
    }
  }

  @Test
  public void internalPrintProcessedProofTest() throws SolverException, InterruptedException {
    // example from the 2022 RESOLUTE paper
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");

    Z3TheoremProver prover = (Z3TheoremProver) context.newProverEnvironment0(Set.of());
    // Z3TheoremProver prover =
    //    (Z3TheoremProver) context.newProverEnvironment0(Set.of(ProverOptions
    //    .GENERATE_UNSAT_CORE));
    try {
      System.out.println("proofs enabled: " + context.getGenerateProofs());
      prover.addConstraint(bmgr.or(bmgr.not(q1), q2));
      prover.addConstraint(q1);
      prover.addConstraint(bmgr.not(q2));
      assertTrue(prover.isUnsat());

      long proof = prover.getZ3Proof();
      Z3ProofProcessor parser =
          new Z3ProofProcessor(
              mgr.getEnvironment(),
              prover.getZ3solver(),
              (Z3FormulaCreator) mgr.getFormulaCreator(),
              prover);
      Z3ProofNode root = parser.fromAST(proof);

      System.out.println(root.asString());

    } finally {
      prover.close();
    }
  }

  @Test
  public void nonRecursivePrintParsedProofTest() throws SolverException, InterruptedException {
    // example from the 2022 RESOLUTE paper
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");

    Z3TheoremProver prover = (Z3TheoremProver) context.newProverEnvironment0(Set.of());
    // Z3TheoremProver prover =
    //    (Z3TheoremProver) context.newProverEnvironment0(Set.of(ProverOptions
    //    .GENERATE_UNSAT_CORE));
    try {
      System.out.println("proofs enabled: " + context.getGenerateProofs());
      prover.addConstraint(bmgr.or(bmgr.not(q1), q2));
      prover.addConstraint(q1);
      prover.addConstraint(bmgr.not(q2));
      assertTrue(prover.isUnsat());

      long proof = prover.getZ3Proof();
      Z3NonRecursiveProofProcessor parser =
          new Z3NonRecursiveProofProcessor(
              mgr.getEnvironment(),
              prover.getZ3solver(),
              (Z3FormulaCreator) mgr.getFormulaCreator(),
              prover);
      Z3ProofNode root = parser.fromASTIterative(proof);

      System.out.println(root.asString());

    } finally {
      prover.close();
    }
  }

  @Test
  public void compareRecursiveAndNonRecursiveOutputsTest()
      throws SolverException, InterruptedException {
    // example from the 2022 RESOLUTE paper
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");

    Z3TheoremProver prover = (Z3TheoremProver) context.newProverEnvironment0(Set.of());
    // Z3TheoremProver prover =
    //    (Z3TheoremProver) context.newProverEnvironment0(Set.of(ProverOptions
    //    .GENERATE_UNSAT_CORE));
    try {
      System.out.println("proofs enabled: " + context.getGenerateProofs());
      prover.addConstraint(bmgr.or(bmgr.not(q1), q2));
      prover.addConstraint(q1);
      prover.addConstraint(bmgr.not(q2));
      assertTrue(prover.isUnsat());

      long proof = prover.getZ3Proof();

      Z3ProofProcessor parser =
          new Z3ProofProcessor(
              mgr.getEnvironment(),
              prover.getZ3solver(),
              (Z3FormulaCreator) mgr.getFormulaCreator(),
              prover);
      Z3ProofNode root = parser.fromAST(proof);

      Z3NonRecursiveProofProcessor nrParser =
          new Z3NonRecursiveProofProcessor(
              mgr.getEnvironment(),
              prover.getZ3solver(),
              (Z3FormulaCreator) mgr.getFormulaCreator(),
              prover);
      Z3ProofNode nRroot = nrParser.fromASTIterative(proof);

      assertEquals(root.asString(), nRroot.asString());

    } finally {
      prover.close();
    }
  }

  public static Context createContextWithRawPointer(long m_ctx) {
    try {
      Constructor<Context> constructor = Context.class.getDeclaredConstructor(long.class);
      constructor.setAccessible(true); // allow access even if non‑public
      return constructor.newInstance(m_ctx);
    } catch (Exception e) {
      throw new RuntimeException("Failed to create Context instance", e);
    }
  }

  @Test
  public void printZ3ProofAstTest() {
    HashMap<String, String> cfg = new HashMap<>();
    cfg.put("proof", "true");
    Context ctx = new Context(cfg);
    try {
      // Create boolean variables
      BoolExpr q1 = ctx.mkBoolConst("q1");
      BoolExpr q2 = ctx.mkBoolConst("q2");

      // Create solver
      Solver solver = ctx.mkSolver();

      // Assert (or (not q1) q2)
      solver.add(ctx.mkOr(ctx.mkNot(q1), q2));

      // Assert q1
      solver.add(q1);

      // Assert (not q2)
      solver.add(ctx.mkNot(q2));

      Status status = solver.check();

      System.out.println("Unsat: " + (status == Status.UNSATISFIABLE));

      Expr<?> proof = solver.getProof();
      System.out.println("proof: " + proof);
      System.out.println(Version.getFullVersion());
    } finally {
      ctx.close();
    }
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

    System.out.println(pn.asString());

    Z3ToResoluteProofConverter pc = new Z3ToResoluteProofConverter(mgr);

    ProofNode res = pc.handleTransitivity(pn);

    pc.printProof(res, 0);
  }
}
