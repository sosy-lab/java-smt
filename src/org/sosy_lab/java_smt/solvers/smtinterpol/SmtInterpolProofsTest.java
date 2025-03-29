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
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import com.google.common.collect.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import java.lang.reflect.Method;
import java.util.Set;
import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.ResolutionProofDag;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;

@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access"})
@Ignore("prevent this class being executed as testcase by ant")
public class SmtInterpolProofsTest {

  private SmtInterpolSolverContext context;
  private SmtInterpolFormulaManager mgr;
  private SmtInterpolBooleanFormulaManager bmgr;
  private SmtInterpolIntegerFormulaManager imgr;

  @Before
  public void setupSolver() throws InvalidConfigurationException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();

    // Create new context with SMTInterpol
    context =
        SmtInterpolSolverContext.create(
            config,
            logger,
            shutdown.getNotifier(),
            null, // no logfile
            42, // randomSeed
            NonLinearArithmetic.USE);

    // Get managers for creating formulas
    mgr = (SmtInterpolFormulaManager) context.getFormulaManager();
    bmgr = (SmtInterpolBooleanFormulaManager) mgr.getBooleanFormulaManager();
    imgr = (SmtInterpolIntegerFormulaManager) mgr.getIntegerFormulaManager();
  }

  @After
  public void closeSolver() {
    if (context != null) {
      context.close();
    }
  }

  @Test
  public void testGetProofTerm() throws SolverException, InterruptedException {
    // example from the 2022 paper
    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");
    BooleanFormula notQ1OrQ2 = bmgr.or(bmgr.not(q1), q2);
    BooleanFormula q1True = bmgr.equivalence(q1, bmgr.makeTrue());
    BooleanFormula q2False = bmgr.equivalence(q2, bmgr.makeFalse());

    SmtInterpolTheoremProver prover =
        (SmtInterpolTheoremProver)
            context.newProverEnvironment0(Set.of(ProverOptions.GENERATE_PROOFS));
    try {
      prover.addConstraint(notQ1OrQ2);
      prover.addConstraint(q1True);
      prover.addConstraint(q2False);
      assertThat(prover.isUnsat()).isTrue();

      Term proof = prover.smtInterpolGetProof();
      assertThat(proof).isNotNull();

      // String proofStr = proof.toString();
      // System.out.println(proofStr);
      System.out.println(proof);
    } finally {
      prover.close();
    }
  }

  @Test
  public void testGetProofClause() throws Exception {
    // example from the 2022 paper
    String constraint1 =
        "(set-logic QF_UF)\n"
            + "(declare-fun q1 () Bool)\n"
            + "(declare-fun q2 () Bool)\n"
            + "(assert (or (not q1) q2))";
    String constraint2 = "(assert q1)";
    String constraint3 = "(assert (not q2))";

    BooleanFormula formula1 = context.getFormulaManager().parse(constraint1);

    BooleanFormula formula2 = context.getFormulaManager().parse(constraint2);

    BooleanFormula formula3 = context.getFormulaManager().parse(constraint3);

    SmtInterpolTheoremProver prover =
        (SmtInterpolTheoremProver)
            context.newProverEnvironment0(
                Set.of(ProverOptions.GENERATE_PROOFS, ProverOptions.GENERATE_MODELS));

    SMTInterpol smtinterpol = (SMTInterpol) prover.env;
    try {
      prover.addConstraint(formula1);
      prover.addConstraint(formula2);
      prover.addConstraint(formula3);
      assertThat(prover.isUnsat()).isTrue();

      Clause proof = smtinterpol.retrieveProof();
      ProofNode proofNode = proof.getProof();
      Term term = smtinterpol.getProof();

      assertThat(proof).isNotNull();

      // String proofStr = proof.toString();
      System.out.println(invokeGetProofMode(smtinterpol).toString());
      System.out.println(proof.toTerm(smtinterpol.getTheory()));
      System.out.println(proof);
      System.out.println(proofNode);
      System.out.println(term);
    } finally {
      prover.close();
    }
  }


  @Test
  public void testSmtInterpolProof() throws Exception {
    // Arrange: parse constraints as in the SmtInterpolProofsTest.
    String constraint1 =
        "(set-logic QF_UF)\n"
            + "(declare-fun q1 () Bool)\n"
            + "(declare-fun q2 () Bool)\n"
            + "(assert (or (not q1) q2))";
    String constraint2 = "(assert q1)";
    String constraint3 = "(assert (not q2))";

    BooleanFormula q1 = bmgr.makeVariable("q1");
    BooleanFormula q2 = bmgr.makeVariable("q2");

    // Create a prover with proof and model generation enabled.
    SmtInterpolTheoremProver prover =
        (SmtInterpolTheoremProver)
            context.newProverEnvironment0(
                ImmutableSet.of(ProverOptions.GENERATE_PROOFS, ProverOptions.GENERATE_MODELS));
    SMTInterpol smtInterpol = (SMTInterpol) prover.env;
    try {
      // Act: add constraints and check unsat.
      prover.addConstraint(bmgr.or(bmgr.not(q1), q2));
      prover.addConstraint(q1);
      prover.addConstraint(bmgr.not(q2));
      assertTrue(prover.isUnsat());

      // Retrieve the proof term from SMTInterpol.
      Term proofTerm = smtInterpol.getProof();
      assertNotNull(proofTerm);

      Term proof = prover.smtInterpolGetProof();
      assertThat(proof).isNotNull();

      // String proofStr = proof.toString();
      // System.out.println(proofStr);
      System.out.println(proof);

      // Optionally, additional assertions on the dag structure can be added here.
    } finally {
      prover.close();
    }
  }

  public static Object invokeGetProofMode(SMTInterpol instance) throws Exception {
    Method getProofModeMethod = SMTInterpol.class.getDeclaredMethod("getProofMode");
    getProofModeMethod.setAccessible(true);
    return getProofModeMethod.invoke(instance);
  }
}
