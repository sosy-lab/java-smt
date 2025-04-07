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

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
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

      processTerm(proof);
    } finally {
      prover.close();
    }
  }

  private int indentLevel = 0;

  private void printIndented(String message) {
    System.out.println(" ".repeat(indentLevel * 2) + message);
  }

  void processTerm(Term term) {
    printIndented("Processing term: " + term.getClass().getSimpleName());
    if (term instanceof ApplicationTerm) {
      processAppTerm((ApplicationTerm) term);
    } else if (term instanceof AnnotatedTerm) {
      processAnnotatedTerm((AnnotatedTerm) term);
    } else if (term instanceof LetTerm) {
      processLetTerm((LetTerm) term);
    } else if (term instanceof ConstantTerm) {
      processConstTerm((ConstantTerm) term);
    } else if (term instanceof LambdaTerm) {
      processLambdaTerm((LambdaTerm) term);
    } else if (term instanceof MatchTerm) {
      processMatchTerm((MatchTerm) term);
    } else if (term instanceof QuantifiedFormula) {
      processQuantifiedFormula((QuantifiedFormula) term);
    } else if (term instanceof TermVariable) {
      processTermVariable((TermVariable) term);
    } else {
      printIndented("Unknown term type: " + term.getClass());
    }
  }

  private void processTermVariable(TermVariable term) {
    printIndented("TermVariable: " + term.toString());
    indentLevel++;
    printIndented("Sort: " + term.getSort().toString());
    printIndented("Declared Sort: " + term.getDeclaredSort().toString());
    printIndented("Name: " + term.getName());
    indentLevel--;
  }

  private void processQuantifiedFormula(QuantifiedFormula term) {
    printIndented("QuantifiedFormula: " + term.toString());
    indentLevel++;
    printIndented("Sort: " + term.getSort().toString());
    printIndented("Quantifier: " + term.getQuantifier());
    printIndented("Subformula: " + term.getSubformula().toString());
    for (int i = 0; i < term.getVariables().length; i++) {
      printIndented("Variable " + i + ": " + term.getVariables()[i]);
      processTerm(term.getVariables()[i]);
    }
    indentLevel--;
  }

  private void processMatchTerm(MatchTerm term) {
    printIndented("MatchTerm: " + term.toString());
    indentLevel++;
    printIndented("Sort: " + term.getSort().toString());
    printIndented("DataTerm: " + term.getDataTerm().toString());
    for (int i = 0; i < term.getVariables().length; i++) {
      for (int j = 0; j < term.getVariables()[i].length; j++) {
        printIndented("Variable " + i + " " + j + ": " + term.getVariables()[i][j]);
        processTerm(term.getVariables()[i][j]);
      }
    }
    for (int i = 0; i < term.getCases().length; i++) {
      printIndented("Case " + i + ": " + term.getCases()[i]);
      processTerm(term.getCases()[i]);
    }
    for (int i = 0; i < term.getConstructors().length; i++) {
      printIndented("Constructor " + i + ": " + term.getConstructors()[i].toString());
    }
    indentLevel--;
  }

  private void processLambdaTerm(LambdaTerm term) {
    printIndented("LambdaTerm: " + term.toString());
    indentLevel++;
    printIndented("Sort: " + term.getSort().toString());
    printIndented("Subterm: " + term.getSubterm().toString());
    for (int i = 0; i < term.getVariables().length; i++) {
      printIndented("Variable " + i + ": " + term.getVariables()[i]);
      processTerm(term.getVariables()[i]);
    }
    printIndented("Subterm will be processed");
    processTerm(term.getSubterm());
    indentLevel--;
  }

  private void processConstTerm(ConstantTerm term) {
    printIndented("ConstantTerm: " + term.toString());
    indentLevel++;
    printIndented("Sort: " + term.getSort().toString());
    printIndented("Value: " + term.getValue());
    if (term.getValue() instanceof Term) {
      printIndented("Value is a term");
      processTerm((Term) term.getValue());
    }
    indentLevel--;
  }

  private void processLetTerm(LetTerm term) {
    printIndented("LetTerm: " + term.toString());
    indentLevel++;
    printIndented("Sort: " + term.getSort().toString());
    printIndented("Subterm: " + term.getSubTerm().toString());
    for (int i = 0; i < term.getValues().length; i++) {
      printIndented("value " + i + ": " + term.getValues()[i]);
      processTerm(term.getValues()[i]);
    }
    for (int i = 0; i < term.getVariables().length; i++) {
      printIndented("variable " + i + ": " + term.getVariables()[i]);
      processTerm(term.getVariables()[i]);
    }
    printIndented("Subterm will be processed");
    processTerm(term.getSubTerm());
    indentLevel--;
  }

  private void processAnnotatedTerm(AnnotatedTerm term) {
    printIndented("AnnotatedTerm: " + term.toString());
    indentLevel++;
    printIndented("Sort: " + term.getSort().toString());
    printIndented("Subterm: " + term.getSubterm().toString());
    for (int i = 0; i < term.getFreeVars().length; i++) {
      printIndented("Free Variable " + i + ": " + term.getFreeVars()[i]);
      processTerm(term.getFreeVars()[i]);
    }
    for (int i = 0; i < term.getAnnotations().length; i++) {
      printIndented("Annotation " + i + ": " + term.getAnnotations()[i]);
      printIndented("Key: " + term.getAnnotations()[i].getKey());
      Object value = term.getAnnotations()[i].getValue();
      if (value != null) {
        printIndented("Value: " + value);
        printIndented("value class: " + value.getClass());
        if (value instanceof Object[]) {
          Object[] valueArray = (Object[]) value;
          for (Object element : valueArray) {
            // Process each element in the array
            printIndented("Array element: " + element);
            printIndented("element class: " + element.getClass());
          }
        }
      }
    }
    printIndented("Subterm will be processed");
    processTerm(term.getSubterm());
    indentLevel--;
  }

  private void processAppTerm(ApplicationTerm term) {
    printIndented("ApplicationTerm: " + term.toString());
    indentLevel++;
    printIndented("Function Symbol: " + term.getFunction().toString());
    Term[] parameters = term.getParameters();
    printIndented("Sort: " + term.getSort().toString());
    printIndented("Parameters: " + parameters.length);
    for (int i = 0; i < parameters.length; i++) {
      printIndented("Parameter " + i + ": " + parameters[i]);
      processTerm(parameters[i]);
    }
    indentLevel--;
  }

  @Test
  public void testPPN() {
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

      SmtInterpolProofNodeCreator pc =
          new SmtInterpolProofNodeCreator(
              (SmtInterpolFormulaCreator) prover.mgr.getFormulaCreator(), prover);

      assertThat(pc.createPPNDag(proof)).isNotNull();

      System.out.println(pc.createPPNDag(proof).asString());

    } catch (InterruptedException pE) {
      throw new RuntimeException(pE);
    } finally {
      prover.close();
    }
  }
}
