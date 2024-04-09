// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.collect.Iterables.filter;
import static com.google.common.collect.Iterables.getLast;
import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.base.Splitter;
import com.google.common.collect.HashMultiset;
import com.google.common.collect.Iterables;
import com.google.common.collect.Multiset;
import com.google.common.truth.TruthJUnit;
import java.util.List;
import java.util.function.Supplier;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;

@SuppressWarnings("checkstyle:linelength")
public class SolverFormulaIOTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  private static final String MATHSAT_DUMP1 =
      "(set-info :source |printed by MathSAT|)\n"
          + "(declare-fun a () Bool)\n"
          + "(declare-fun b () Bool)\n"
          + "(declare-fun d () Bool)\n"
          + "(declare-fun e () Bool)\n"
          + "(define-fun .def_9 () Bool (= a b))\n"
          + "(define-fun .def_10 () Bool (not .def_9))\n"
          + "(define-fun .def_13 () Bool (and .def_10 d))\n"
          + "(define-fun .def_14 () Bool (or e .def_13))\n"
          + "(assert .def_14)";
  private static final String MATHSAT_DUMP2 =
      "(set-info :source |printed by MathSAT|)\n"
          + "(declare-fun a () Int)\n"
          + "(declare-fun b () Int)\n"
          + "(declare-fun c () Int)\n"
          + "(declare-fun q () Bool)\n"
          + "(declare-fun u () Bool)\n"
          + "(define-fun .def_15 () Int (* (- 1) c))\n"
          + "(define-fun .def_16 () Int (+ b .def_15))\n"
          + "(define-fun .def_17 () Int (+ a .def_16))\n"
          + "(define-fun .def_19 () Bool (= .def_17 0))\n"
          + "(define-fun .def_27 () Bool (= .def_19 q))\n"
          + "(define-fun .def_28 () Bool (not .def_27))\n"
          + "(define-fun .def_23 () Bool (<= b a))\n"
          + "(define-fun .def_29 () Bool (and .def_23 .def_28))\n"
          + "(define-fun .def_11 () Bool (= a b))\n"
          + "(define-fun .def_34 () Bool (and .def_11 .def_29))\n"
          + "(define-fun .def_30 () Bool (or u .def_29))\n"
          + "(define-fun .def_31 () Bool (and q .def_30))\n"
          + "(define-fun .def_35 () Bool (and .def_31 .def_34))\n"
          + "(assert .def_35)";
  private static final String MATHSAT_DUMP3 =
      "(set-info :source |printed by MathSAT|)\n"
          + "(declare-fun fun_b (Int) Bool)\n"
          + "(define-fun .def_11 () Bool (fun_b 1))\n"
          + "(assert .def_11)";
  private static final String SMTINTERPOL_DUMP1 =
      "(declare-fun d () Bool)\n"
          + "(declare-fun b () Bool)\n"
          + "(declare-fun a () Bool)\n"
          + "(declare-fun e () Bool)\n"
          + "(assert (or e (and (xor a b) d)))";
  private static final String SMTINTERPOL_DUMP2 =
      "(declare-fun b () Int)(declare-fun a () Int)\n"
          + "(declare-fun c () Int)\n"
          + "(declare-fun q () Bool)\n"
          + "(declare-fun u () Bool)\n"
          + "(assert (let ((.cse0 (xor q (= (+ a b) c))) (.cse1 (>= a b))) (and (or (and .cse0"
          + " .cse1) u) q (= a b) .cse0 .cse1)))";
  private static final String Z3_DUMP1 =
      "(declare-fun d () Bool)\n"
          + "(declare-fun b () Bool)\n"
          + "(declare-fun a () Bool)\n"
          + "(declare-fun e () Bool)\n"
          + "(assert  (or e (and (xor a b) d)))";
  private static final String Z3_DUMP2 =
      "(declare-fun b () Int)\n"
          + "(declare-fun a () Int)\n"
          + "(declare-fun c () Int)\n"
          + "(declare-fun q () Bool)\n"
          + "(declare-fun u () Bool)\n"
          + "(assert  (let (($x35 (and (xor q (= (+ a b) c)) (>= a b)))) (let (($x9 (= a b))) (and"
          + " (and (or $x35 u) q) (and $x9 $x35)))))";

  @Test
  public void varDumpTest() {
    // Boolector will fail this anyway since bools are bitvecs for btor
    TruthJUnit.assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);
    BooleanFormula a = bmgr.makeVariable("main::a");
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula c1 = bmgr.xor(a, b);
    BooleanFormula c2 = bmgr.xor(a, b);
    BooleanFormula d = bmgr.and(c1, c2);

    String formDump = mgr.dumpFormula(d).toString();
    assertThat(formDump).contains("(declare-fun |main::a| () Bool)");
    assertThat(formDump).contains("(declare-fun b () Bool)");
    checkThatAssertIsInLastLine(formDump);
    checkThatDumpIsParseable(formDump);
  }

  @Test
  public void varDumpTest2() {
    // Boolector will fail this anyway since bools are bitvecs for btor
    TruthJUnit.assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);

    // always true

    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula c1 = bmgr.xor(a, b);
    BooleanFormula c2 = bmgr.and(a, b);
    BooleanFormula d = bmgr.or(c1, c2);
    BooleanFormula e = bmgr.and(a, d);

    BooleanFormula x1 = bmgr.xor(a, b);
    BooleanFormula x2 = bmgr.and(a, b);
    BooleanFormula w = bmgr.or(x1, x2);
    BooleanFormula v = bmgr.or(x1, b);

    BooleanFormula branch1 = bmgr.and(d, e);
    BooleanFormula branch2 = bmgr.and(w, v);
    BooleanFormula branchComp = bmgr.or(branch1, branch2);

    String formDump = mgr.dumpFormula(branchComp).toString();
    assertThat(formDump).contains("(declare-fun a () Bool)");
    assertThat(formDump).contains("(declare-fun b () Bool)");

    // The serialization has to be parse-able.
    checkThatDumpIsParseable(formDump);
  }

  @Test
  public void valDumpTest() {
    // Boolector will fail this anyway since bools are bitvecs for btor
    TruthJUnit.assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);
    BooleanFormula tr1 = bmgr.makeBoolean(true);
    BooleanFormula tr2 = bmgr.makeBoolean(true);
    BooleanFormula fl1 = bmgr.makeBoolean(false);
    BooleanFormula fl2 = bmgr.makeBoolean(false);
    BooleanFormula valComp = bmgr.and(fl1, tr1);
    BooleanFormula valComp2 = bmgr.and(fl1, tr1);
    BooleanFormula valComp3 = bmgr.and(tr2, valComp);
    BooleanFormula valComp4 = bmgr.and(fl2, valComp2);
    BooleanFormula valComp5 = bmgr.or(valComp3, valComp4);

    String formDump = mgr.dumpFormula(valComp5).toString();
    checkThatAssertIsInLastLine(formDump);
    checkThatDumpIsParseable(formDump);
  }

  @Test
  public void intsDumpTest() {
    requireIntegers();
    IntegerFormula f1 = imgr.makeVariable("a");
    IntegerFormula val = imgr.makeNumber(1);
    BooleanFormula formula = imgr.equal(f1, val);

    String formDump = mgr.dumpFormula(formula).toString();

    // check that int variable is declared correctly + necessary assert that has to be there
    assertThat(formDump).contains("(declare-fun a () Int)");
    checkThatAssertIsInLastLine(formDump);
    checkThatDumpIsParseable(formDump);
  }

  @Test
  public void bvDumpTest() {
    requireBitvectors();
    TruthJUnit.assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);
    BitvectorFormula f1 = bvmgr.makeVariable(8, "a");
    BitvectorFormula val = bvmgr.makeBitvector(8, 1);
    BooleanFormula formula = bvmgr.equal(f1, val);

    String formDump = mgr.dumpFormula(formula).toString();

    // check that int variable is declared correctly + necessary assert that has to be there
    assertThat(formDump).contains("(declare-fun a () (_ BitVec 8))");
    checkThatAssertIsInLastLine(formDump);
    checkThatDumpIsParseable(formDump);
  }

  @Test
  public void funcsDumpTest() {
    requireIntegers();
    IntegerFormula int1 = imgr.makeNumber(1);
    IntegerFormula var = imgr.makeVariable("var_a");
    FunctionDeclaration<IntegerFormula> funA =
        fmgr.declareUF(
            "fun_a", FormulaType.IntegerType, FormulaType.IntegerType, FormulaType.IntegerType);
    IntegerFormula res1 = fmgr.callUF(funA, int1, var);
    BooleanFormula formula = imgr.equal(res1, var);

    String formDump = mgr.dumpFormula(formula).toString();

    // check that function is dumped correctly + necessary assert that has to be there
    assertThat(formDump).contains("(declare-fun fun_a (Int Int) Int)");
    checkThatAssertIsInLastLine(formDump);
    checkThatDumpIsParseable(formDump);
  }

  @Test
  public void parseMathSatTestParseFirst1() throws SolverException, InterruptedException {
    requireParser();
    compareParseWithOrgParseFirst(MATHSAT_DUMP1, this::genBoolExpr);
  }

  @Test
  public void parseMathSatTestExprFirst1() throws SolverException, InterruptedException {
    requireParser();
    compareParseWithOrgExprFirst(MATHSAT_DUMP1, this::genBoolExpr);
  }

  @Test
  public void parseSmtinterpolTestParseFirst1() throws SolverException, InterruptedException {
    requireParser();
    compareParseWithOrgParseFirst(SMTINTERPOL_DUMP1, this::genBoolExpr);
  }

  @Test
  public void parseSmtinterpolTestExprFirst1() throws SolverException, InterruptedException {
    requireParser();
    compareParseWithOrgExprFirst(SMTINTERPOL_DUMP1, this::genBoolExpr);
  }

  @Test
  public void parseZ3TestParseFirst1() throws SolverException, InterruptedException {
    requireParser();
    compareParseWithOrgParseFirst(Z3_DUMP1, this::genBoolExpr);
  }

  @Test
  public void parseZ3TestExprFirst1() throws SolverException, InterruptedException {
    requireParser();
    compareParseWithOrgExprFirst(Z3_DUMP1, this::genBoolExpr);
  }

  @Test
  public void parseMathSatTestParseFirst2() throws SolverException, InterruptedException {
    requireParser();
    compareParseWithOrgParseFirst(MATHSAT_DUMP2, this::redundancyExprGen);
  }

  @Test
  public void parseMathSatTestExprFirst2() throws SolverException, InterruptedException {
    requireParser();
    compareParseWithOrgExprFirst(MATHSAT_DUMP2, this::redundancyExprGen);
  }

  @Test
  public void parseSmtinterpolSatTestParseFirst2() throws SolverException, InterruptedException {
    requireParser();
    requireIntegers();
    compareParseWithOrgParseFirst(SMTINTERPOL_DUMP2, this::redundancyExprGen);
  }

  @Test
  public void parseSmtinterpolSatTestExprFirst2() throws SolverException, InterruptedException {
    requireParser();
    compareParseWithOrgExprFirst(SMTINTERPOL_DUMP2, this::redundancyExprGen);
  }

  @Test
  public void parseZ3SatTestParseFirst2() throws SolverException, InterruptedException {
    requireParser();
    requireIntegers();
    compareParseWithOrgParseFirst(Z3_DUMP2, this::redundancyExprGen);
  }

  @Test
  public void parseZ3SatTestExprFirst2() throws SolverException, InterruptedException {
    requireParser();
    compareParseWithOrgExprFirst(Z3_DUMP2, this::redundancyExprGen);
  }

  @Test
  public void parseMathSatTestExprFirst3() throws SolverException, InterruptedException {
    requireParser();
    requireIntegers();
    compareParseWithOrgExprFirst(MATHSAT_DUMP3, this::functionExprGen);
  }

  @Test
  public void redundancyTest() {
    assume()
        .withMessage(
            "Solver %s does not remove redundant sub formulae from formula dump.", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.YICES2, Solvers.CVC5);

    assume()
        .withMessage(
            "Solver %s will fail this anyway since it bools are handled as bitvectors of length"
                + " one.",
            solverToUse())
        .that(solver)
        .isNotEqualTo(Solvers.BOOLECTOR);

    String formDump = mgr.dumpFormula(redundancyExprGen()).toString();
    int count = Iterables.size(Splitter.on(">=").split(formDump)) - 1;
    int count2 = Iterables.size(Splitter.on("<=").split(formDump)) - 1;
    // Please avoid exponential overhead when printing a formula.
    assertWithMessage(formDump + " does not contain <= or >= only once.")
        .that(count == 1 || count2 == 1)
        .isTrue();
  }

  @Test
  public void funDeclareTest() {
    requireIntegers();
    IntegerFormula int1 = imgr.makeNumber(1);
    IntegerFormula int2 = imgr.makeNumber(2);

    FunctionDeclaration<IntegerFormula> funA =
        fmgr.declareUF("fun_a", FormulaType.IntegerType, FormulaType.IntegerType);
    FunctionDeclaration<IntegerFormula> funB =
        fmgr.declareUF("fun_b", FormulaType.IntegerType, FormulaType.IntegerType);
    IntegerFormula res1 = fmgr.callUF(funA, int1);
    IntegerFormula res2 = fmgr.callUF(funB, int2);

    IntegerFormula calc = imgr.add(res1, res2);
    String formDump = mgr.dumpFormula(imgr.equal(calc, int1)).toString();

    // check if dumped formula fits our specification
    checkThatFunOnlyDeclaredOnce(formDump);
    checkThatAssertIsInLastLine(formDump);
    checkThatDumpIsParseable(formDump);
  }

  @Test
  public void funDeclareTest2() {
    requireIntegers();
    IntegerFormula int1 = imgr.makeNumber(1);
    IntegerFormula int2 = imgr.makeNumber(2);

    FunctionDeclaration<IntegerFormula> funA =
        fmgr.declareUF("fun_a", FormulaType.IntegerType, FormulaType.IntegerType);
    IntegerFormula res1 = fmgr.callUF(funA, int1);
    IntegerFormula res2 = fmgr.callUF(funA, int2);

    IntegerFormula calc = imgr.add(res1, res2);
    String formDump = mgr.dumpFormula(imgr.equal(calc, int1)).toString();

    // check if dumped formula fits our specification
    checkThatFunOnlyDeclaredOnce(formDump);
    checkThatAssertIsInLastLine(formDump);
    checkThatDumpIsParseable(formDump);
  }

  private void compareParseWithOrgExprFirst(String textToParse, Supplier<BooleanFormula> fun)
      throws SolverException, InterruptedException {
    // Boolector will fail this anyway since bools are bitvecs for btor
    TruthJUnit.assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);
    // check if input is correct
    checkThatFunOnlyDeclaredOnce(textToParse);
    checkThatAssertIsInLastLine(textToParse);

    // actual test
    BooleanFormula expr = fun.get();
    BooleanFormula parsedForm = mgr.parse(textToParse);
    assertThatFormula(parsedForm).isEquivalentTo(expr);
  }

  private void compareParseWithOrgParseFirst(String textToParse, Supplier<BooleanFormula> fun)
      throws SolverException, InterruptedException {
    // Boolector will fail this anyway since bools are bitvecs for btor
    TruthJUnit.assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);
    // check if input is correct
    checkThatFunOnlyDeclaredOnce(textToParse);
    checkThatAssertIsInLastLine(textToParse);

    // actual test
    BooleanFormula parsedForm = mgr.parse(textToParse);
    BooleanFormula expr = fun.get();
    assertThatFormula(parsedForm).isEquivalentTo(expr);
  }

  private void checkThatFunOnlyDeclaredOnce(String formDump) {
    // Boolector will fail this anyway since bools are bitvecs for btor
    TruthJUnit.assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);
    Multiset<String> funDeclares = HashMultiset.create();

    for (String line : Splitter.on('\n').split(formDump)) {
      if (line.startsWith("(declare-fun ")) {
        funDeclares.add(line.replaceAll("\\s+", ""));
      }
    }

    // remove non-duplicates
    funDeclares.entrySet().removeIf(pStringEntry -> pStringEntry.getCount() <= 1);
    assertWithMessage("duplicate function declarations").that(funDeclares).isEmpty();
  }

  private void checkThatAssertIsInLastLine(String dump) {
    // Boolector will fail this anyway since bools are bitvecs for btor
    TruthJUnit.assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);

    List<String> lines = Splitter.on('\n').splitToList(dump.trim());
    String lineUnderTest = getLast(lines);

    if (solver == Solvers.OPENSMT) {
      // OpenSMT prints assertions over several lines, so lets find the last SMT-LIB command by
      // heuristic: the last line starting with a plain bracket.
      lineUnderTest = getLast(filter(lines, line -> line.startsWith("(")));
    }

    assertWithMessage("last line(s) of <\n" + dump + ">")
        .that(lineUnderTest)
        .startsWith("(assert ");
    assertWithMessage("last line(s) of <\n" + dump + ">").that(getLast(lines)).endsWith(")");
  }

  @SuppressWarnings("CheckReturnValue")
  private void checkThatDumpIsParseable(String dump) {
    requireParser();
    mgr.parse(dump);
  }

  private BooleanFormula genBoolExpr() {
    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula c = bmgr.xor(a, b);
    BooleanFormula d = bmgr.makeVariable("d");
    BooleanFormula e = bmgr.makeVariable("e");
    BooleanFormula f = bmgr.and(c, d);
    return bmgr.or(e, f);
  }

  private BooleanFormula redundancyExprGen() {
    IntegerFormula i1 = imgr.makeVariable("a");
    IntegerFormula i2 = imgr.makeVariable("b");
    IntegerFormula erg = imgr.makeVariable("c");
    BooleanFormula b1 = bmgr.makeVariable("q");
    BooleanFormula b2 = bmgr.makeVariable("u");

    // 1st execution
    BooleanFormula f1 = imgr.equal(imgr.add(i1, i2), erg);
    BooleanFormula comp1 = imgr.greaterOrEquals(i1, i2);
    BooleanFormula x1 = bmgr.xor(b1, f1);
    BooleanFormula comb1 = bmgr.and(x1, comp1);

    // rest
    BooleanFormula r1a = bmgr.or(comb1, b2);
    BooleanFormula r1b = bmgr.and(r1a, b1);

    // rest
    BooleanFormula r2a = imgr.equal(i1, i2);
    BooleanFormula r2b = bmgr.and(r2a, comb1);

    return bmgr.and(r1b, r2b);
  }

  private BooleanFormula functionExprGen() {
    IntegerFormula arg = imgr.makeNumber(1);
    FunctionDeclaration<BooleanFormula> funA =
        fmgr.declareUF("fun_b", FormulaType.BooleanType, FormulaType.IntegerType);
    BooleanFormula res1 = fmgr.callUF(funA, arg);
    return bmgr.and(res1, bmgr.makeBoolean(true));
  }
}
