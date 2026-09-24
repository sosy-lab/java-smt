// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.api.FormulaType.BooleanType;

import com.google.common.collect.Iterables;
import java.math.BigInteger;
import java.util.List;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager.SolverResponse;
import org.sosy_lab.java_smt.api.FormulaManager.SolverResponse.CheckSatResponse.Status;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;

public class ParserTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Before
  public void setUp() {
    requireParser();
  }

  @Test
  public void parseAllSimpleBooleanTest() {
    String smt = "(assert true)";
    assertThat(mgr.parseAll(smt)).containsExactly(bmgr.makeTrue());
  }

  @Test
  public void parseAllSimpleIntegerTest() {
    requireIntegers();
    String smt = "(declare-fun x () Int)(assert (= x 1))";
    assertThat(mgr.parseAll(smt))
        .containsExactly(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)));
  }

  @Test
  public void parseAllDefineFunTest() throws SolverException, InterruptedException {
    requireIntegers();
    assume()
        .withMessage("Solver %s does not support parsing function definitions", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.SMTINTERPOL);

    String smt =
        "(define-fun f ((x Int)) Int (+ x 1))"
            + "(assert true)"
            + "(declare-fun y1 () Int)"
            + "(declare-fun y2 () Int)"
            + "(assert (= (f y1) 2))"
            + "(define-fun g ((x Int)) Int (+ x 3))"
            + "(assert (= (g y2) 2))"
            + "(declare-fun y3 () Int)"
            + "(declare-fun y4 () Int)"
            + "(assert (= (g y3) 2))"
            + "(define-fun h ((x Int)) Int (+ x 5))"
            + "(assert (= (h y4) 2))";
    List<BooleanFormula> parsed = mgr.parseAll(smt);
    assertThat(parsed).hasSize(5);
    assertThatFormula(parsed.get(0)).isEquivalentTo(bmgr.makeTrue());
    assertThatFormula(parsed.get(1))
        .isEquisatisfiableTo(imgr.equal(imgr.makeVariable("y1"), imgr.makeNumber(1)));
    assertThatFormula(parsed.get(2))
        .isEquisatisfiableTo(imgr.equal(imgr.makeVariable("y2"), imgr.makeNumber(-1)));
    assertThatFormula(parsed.get(3))
        .isEquisatisfiableTo(imgr.equal(imgr.makeVariable("y3"), imgr.makeNumber(-1)));
    assertThatFormula(parsed.get(4))
        .isEquisatisfiableTo(imgr.equal(imgr.makeVariable("y4"), imgr.makeNumber(-3)));
  }

  @Test
  public void parseAllMultipleAssertionsTest() {
    requireIntegers();
    String smt = "(declare-fun x () Int)(assert (> x 0))(assert (< x 10))";
    BooleanFormula gt = imgr.greaterThan(imgr.makeVariable("x"), imgr.makeNumber(0));
    BooleanFormula lt = imgr.lessThan(imgr.makeVariable("x"), imgr.makeNumber(10));
    assertThat(mgr.parseAll(smt)).containsExactly(gt, lt).inOrder();
  }

  @Test
  public void parseAllDifferentTypesTest() {
    requireIntegers();
    String smt = "(declare-fun x () Int)(declare-fun y () Bool)(assert (= x 1))(assert y)";
    BooleanFormula intEq = imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1));
    BooleanFormula boolY = bmgr.makeVariable("y");
    assertThat(mgr.parseAll(smt)).containsExactly(intEq, boolY).inOrder();
  }

  @Test
  public void parseAllFunctionApplicationTest() {
    requireIntegers();
    String smt = "(declare-fun f (Int) Int)(declare-fun x () Int)(assert (= (f x) 1))";
    IntegerFormula x = imgr.makeVariable("x");
    assertThat(mgr.parseAll(smt))
        .containsExactly(
            imgr.equal(fmgr.declareAndCallUF("f", FormulaType.IntegerType, x), imgr.makeNumber(1)));
  }

  @Test
  public void parseAllBitvectorTest() throws SolverException, InterruptedException {
    requireBitvectors();
    String smt = "(declare-fun x () (_ BitVec 8))(assert (= x #x01))";
    List<BooleanFormula> parsed = mgr.parseAll(smt);
    assertThat(parsed).hasSize(1);
    assertThatFormula(Iterables.getOnlyElement(parsed))
        .isEquisatisfiableTo(bvmgr.equal(bvmgr.makeVariable(8, "x"), bvmgr.makeBitvector(8, 1)));
  }

  @Test
  public void parseAllQuantifierTest() {
    requireQuantifiers();
    requireIntegers();
    assume().that(solver).isNotEqualTo(Solvers.YICES2);
    String smt = "(declare-fun p (Int) Bool)(assert (forall ((x Int)) (p x)))";
    // NOTE: This test might be tricky as forall parsing can be complex.
    // For now, we will just assert that it doesn't throw an exception and returns a formula.
    // A more robust check would involve comparing the structure of the formula.
    assertThat(mgr.parseAll(smt)).hasSize(1);
    assertThat(mgr.parseAll(smt).get(0)).isInstanceOf(BooleanFormula.class);
  }

  @Test
  public void parseAllStringTest() throws SolverException, InterruptedException {
    requireStrings();
    assume()
        .withMessage("Solver %s does not support parsing strings", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    String smt = "(declare-fun s () String)(assert (= s \"hello\"))";
    List<BooleanFormula> parsed = mgr.parseAll(smt);
    assertThat(parsed).hasSize(1);
    assertThatFormula(Iterables.getOnlyElement(parsed))
        .isEquisatisfiableTo(smgr.equal(smgr.makeVariable("s"), smgr.makeString("hello")));
  }

  @Test
  public void parseAllFloatingPointFromIntTest() {
    requireFloats();
    requireIntegers();
    String smt = "(declare-fun x () Int)(assert (= x 1.0))";
    assertThat(mgr.parseAll(smt)).hasSize(1);
    assertThat(mgr.parseAll(smt).get(0)).isInstanceOf(BooleanFormula.class);
  }

  @Test
  public void parseAllFloatingPointFromRealTest() {
    requireFloats();
    requireRationals();
    String smt = "(declare-fun x () Real)(assert (= x 1.0))";
    assertThat(mgr.parseAll(smt)).hasSize(1);
    assertThat(mgr.parseAll(smt).get(0)).isInstanceOf(BooleanFormula.class);
  }

  @Test
  public void parseAllComplexNestedTest() {
    requireIntegers();
    String smt =
        "(declare-fun x () Int)(declare-fun y () Int)(assert (or (= x 1) (and (> y 0) (< y 10))))";
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    BooleanFormula eqX = imgr.equal(x, imgr.makeNumber(1));
    BooleanFormula gtY = imgr.greaterThan(y, imgr.makeNumber(0));
    BooleanFormula ltY = imgr.lessThan(y, imgr.makeNumber(10));
    BooleanFormula and = bmgr.and(gtY, ltY);
    BooleanFormula or = bmgr.or(eqX, and);
    assertThat(mgr.parseAll(smt)).containsExactly(or);
  }

  @Test
  public void parseAllLetBindingTest() {
    requireIntegers();
    String smt = "(declare-fun x () Int)(assert (let ((a x)) (= a 1)))";
    // For now, just check if it parses without error and returns a formula.
    // Detailed check of let-binding expansion might be solver-dependent.
    assertThat(mgr.parseAll(smt)).hasSize(1);
    assertThat(mgr.parseAll(smt).get(0)).isInstanceOf(BooleanFormula.class);
  }

  @Test
  public void parseAllSyntaxErrorTest() {
    String smt = "(assert (= x 1)"; // Missing closing parenthesis
    assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
  }

  @Test
  public void parseAllUndeclaredVariableTest() {
    String smt = "(assert (= x 1))"; // 'x' not declared
    assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
  }

  @Test
  public void parseAllTypeMismatchTest() throws SolverException, InterruptedException {
    requireIntegers();
    String smt = "(declare-fun x () Int)(assert (= x true))"; // Int vs Bool
    assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
  }

  @Test
  public void parseAllUnknownCommandTest() {
    String smt = "(unknown-command)";
    assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
  }

  @Test
  public void parseAllEmptyStringTest() {
    String smt = "";
    assertThat(mgr.parseAll(smt)).isEmpty();
  }

  @Test
  public void parseAllEmptyString2Test() {
    String smt = "   ";
    assertThat(mgr.parseAll(smt)).isEmpty();
  }

  @Test
  public void parseAllEmptyString3Test() {
    String smt = "\n\t  \n";
    assertThat(mgr.parseAll(smt)).isEmpty();
  }

  @Test
  public void parseAllIncorrectFunctionArityTest() {
    requireIntegers();
    String smt = "(declare-fun f (Int) Int)(assert (f))"; // f expects 1 arg, got 0
    assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
  }

  @Test
  public void parseAllReservedKeywordTest() throws SolverException, InterruptedException {
    requireIntegers();
    // 'assert' is a reserved keyword, cannot be used as a function name in most solvers
    String smt = "(declare-fun assert () Int)(assert (= assert 1))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
  }

  @Test
  public void parseAllQuotedSymbolTest() {
    // Capture a variable from the context
    var f = mgr.makeVariable(BooleanType, "my variable");
    var g = mgr.parse("(assert |my variable|)");

    assertThat(g).isEqualTo(f);
  }

  @Test
  public void parseAllQuotedSymbolRedefinitionTest() {
    // Parse a variable that was already defined in the context
    var f = mgr.makeVariable(BooleanType, "my variable");
    var str = "(declare-fun |my variable| () Bool) (assert |my variable|)";
    var g = mgr.parse(str);

    assertThat(g).isEqualTo(f);
  }

  @Test
  public void parseAllEpsilonTermTest() throws SolverException, InterruptedException {
    // Princess rewrites the assertion as an epsilon term, which caused issues while parsing as it
    // introduces a new variable
    requireRationals();
    BooleanFormula f = mgr.parse("(assert (> (/ 1.0 2.0) 0.0))");

    assertThatFormula(f).isTautological();
  }

  @Test
  public void parseScriptStackTest() throws SolverException, InterruptedException {
    requireIntegers();

    String push =
        """
        (declare-const v Int)
        (get-assertions)
        (assert (= v 0))
        (push 1)
        (declare-const w Int)
        (assert (= w v))
        (get-assertions)
        (pop 1)
        (get-assertions)
        (exit)
        """;
    var pushResponse = mgr.parseScript(push);

    assertThat(((SolverResponse.AssertedResponse) pushResponse.get(0)).asserted()).hasSize(0);
    assertThat(((SolverResponse.AssertedResponse) pushResponse.get(1)).asserted()).hasSize(2);
    assertThat(((SolverResponse.AssertedResponse) pushResponse.get(2)).asserted()).hasSize(1);

    String reset =
        """
        (declare-const v Int)
        (assert (= v 0))
        (get-assertions)
        (reset)
        (get-assertions)
        (exit)
        """;
    var resetResponse = mgr.parseScript(reset);

    assertThat(((SolverResponse.AssertedResponse) resetResponse.get(0)).asserted()).hasSize(1);
    assertThat(((SolverResponse.AssertedResponse) resetResponse.get(1)).asserted()).hasSize(0);
  }

  @Test
  public void parseScriptCheckSatTest() throws SolverException, InterruptedException {
    requireIntegers();

    String check =
        """
        (declare-const v Int)
        (assert (= v 0))
        (check-sat)
        (exit)
        """;
    var checkResponse = mgr.parseScript(check);

    assertThat(((SolverResponse.CheckSatResponse) checkResponse.get(0)).status())
        .isEqualTo(Status.SAT);

    String checkAssuming =
        """
        (declare-const v Int)
        (assert (= v 0))
        (check-sat-assuming ((= v 1)))
        (exit)
        """;
    var assumingResponse = mgr.parseScript(checkAssuming);

    assertThat(((SolverResponse.CheckSatResponse) assumingResponse.get(0)).status())
        .isEqualTo(Status.UNSAT);
  }

  @Test
  public void parseScriptModelTest() throws SolverException, InterruptedException {
    requireIntegers();

    String modelSmtlib =
        """
        (declare-const v Int)
        (assert (= v 0))
        (check-sat)
        (get-model)
        (exit)
        """;
    var modelResponse = mgr.parseScript(modelSmtlib);
    var model = ((SolverResponse.ModelResponse) modelResponse.get(1)).model();

    assertThat(model).hasSize(1);
    assertThat(model.get(0).getName()).isEqualTo("v");
    assertThat(model.get(0).getValue()).isEqualTo(new BigInteger("0"));

    String evalSmtlib =
        """
        (declare-const v Int)
        (assert (= v 0))
        (check-sat)
        (get-value (v))
        (exit)
        """;
    var evalResponse = mgr.parseScript(evalSmtlib);

    assertThat(((SolverResponse.EvaluationResponse) evalResponse.get(1)).value().get(0))
        .isEqualTo(imgr.makeNumber(0));
  }

  @Test
  public void parseScriptUnsatCoreTest() throws SolverException, InterruptedException {
    requireIntegers();
    requireUnsatCore();

    String unsatCoreSmtlib =
        """
        (declare-const v Int)
        (declare-const w Int)
        (assert (and (= v 0) (> v 0)))
        (assert (= w 0))
        (check-sat)
        (get-unsat-core)
        (exit)
        """;
    var unsatCoreResponse = mgr.parseScript(unsatCoreSmtlib);
    var unsatCore = ((SolverResponse.UnsatCoreResponse) unsatCoreResponse.get(1)).core();

    assertThat(unsatCore).hasSize(1);
    assertThat(mgr.extractVariables(unsatCore.get(0)).keySet()).containsExactly("v");
  }

  @Test
  public void parseScriptUnsatAssumptionsTest() throws SolverException, InterruptedException {
    requireIntegers();
    requireUnsatCoreOverAssumptions();

    String unsatAssumptionsSmtlib =
        """
        (declare-const A Bool)
        (declare-const B Bool)
        (assert (xor A B))
        (assert A)
        (check-sat-assuming (A B))
        (get-unsat-assumptions)
        (exit)
        """;
    var unsatAssumptionsResponse = mgr.parseScript(unsatAssumptionsSmtlib);
    var unsatAssumptionsCore =
        ((SolverResponse.UnsatCoreResponse) unsatAssumptionsResponse.get(1)).core();

    assertThat(unsatAssumptionsCore).hasSize(1);
    assertThat(mgr.extractVariables(unsatAssumptionsCore.get(0)).keySet()).containsExactly("B");
  }

  @SuppressWarnings("unused")
  @Test
  public void parseScriptResetTest() throws SolverException, InterruptedException {
    requireIntegers();

    String resetSmtlib =
        """
        (declare-const v Int)
        (reset)
        (assert (= v 0))
        (check-sat)
        (exit)
        """;
    assertThrows(IllegalArgumentException.class, () -> mgr.parseScript(resetSmtlib));

    String redeclareSmtlib =
        """
        (declare-const v Int)
        (reset)
        (declare-const v Int)
        (assert (= v 0))
        (check-sat)
        (exit)
        """;
    var redeclareResponse = mgr.parseScript(redeclareSmtlib);

    String redefineSmtlib =
        """
        (declare-const v Int)
        (reset)
        (declare-const v Bool)
        (assert v)
        (check-sat)
        (exit)
        """;
    var redefineResponse = mgr.parseScript(redefineSmtlib);
  }

  @SuppressWarnings("unused")
  @Test
  public void parseScriptExitTest() throws SolverException, InterruptedException {
    requireIntegers();

    String noExitSmtlib =
        """
        (declare-const v Int)
        (assert (= v 0))
        (check-sat)
        """;
    var noExit = mgr.parseScript(noExitSmtlib);

    String earlyExitSmtlib =
        """
        (declare-const v Int)
        (assert (= v 0))
        (exit)
        (check-sat)
        """;
    assertThrows(IllegalArgumentException.class, () -> mgr.parseScript(earlyExitSmtlib));
  }

  private Thread cancelIn(int delay) {
    return new Thread(
        () -> {
          try {
            Thread.sleep(delay);
            shutdownManager.requestShutdown("Shutdown Request");
          } catch (InterruptedException exception) {
            throw new UnsupportedOperationException("Unexpected interrupt", exception);
          }
        });
  }

  @SuppressWarnings("resource")
  @Test
  public void parseScriptTimeoutTest() {
    assume().that(solver).isNoneOf(Solvers.PRINCESS, Solvers.CVC5);
    requireIntegers();

    var hardProblem = new HardIntegerFormulaGenerator(imgr, bmgr).generate(50);
    var hardSmtlib = String.format("%s (check-sat)", mgr.dumpFormula(hardProblem));

    cancelIn(500).start();
    assertThrows(InterruptedException.class, () -> mgr.parseScript(hardSmtlib));
  }
}
