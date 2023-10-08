// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import static com.google.common.truth.Truth.assertThat;

import java.util.Arrays;
import java.util.List;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.solvers.opensmt.api.ArithLogic;
import org.sosy_lab.java_smt.solvers.opensmt.api.InterpolationContext;
import org.sosy_lab.java_smt.solvers.opensmt.api.ItpAlgorithm;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.LogicFactory;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic_t;
import org.sosy_lab.java_smt.solvers.opensmt.api.MainSolver;
import org.sosy_lab.java_smt.solvers.opensmt.api.Model;
import org.sosy_lab.java_smt.solvers.opensmt.api.OpenSmt;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SMTConfig;
import org.sosy_lab.java_smt.solvers.opensmt.api.SMTOption;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SymRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.TemplateFunction;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorInt;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorPTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorSRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.opensmt_logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.sstat;

public class OpenSmtNativeAPITest {
  static {
    NativeLibraries.loadLibrary("opensmt");
    NativeLibraries.loadLibrary("opensmtjava");
  }

  /** Return free variables. */
  private VectorPTRef variables(Logic logic, PTRef term) {
    if (logic.isVar(term)) {
      VectorPTRef vars = new VectorPTRef();
      vars.add(term);
      return vars;
    } else {
      VectorPTRef vars = new VectorPTRef();
      for (PTRef sub : logic.getPterm(term).getArgs()) {
        VectorPTRef res = variables(logic, sub);
        vars.addAll(res);
      }
      return vars;
    }
  }

  /** Verify that we have a valid interpolant. See VerificationUtils.h in OpenSmt for details. */
  private boolean verifyInterpolant(Logic logic, PTRef partA, PTRef partB, PTRef interpol) {
    SMTConfig config = new SMTConfig();
    MainSolver solver = new MainSolver(logic, config, "opensmt-verifier");

    // Check A ⊨ I
    solver.push(logic.mkNot(logic.mkImpl(partA, interpol)));
    if (!solver.check().equals(sstat.False())) {
      return false;
    }
    solver.pop();

    // Check I ⊨ ¬B
    solver.push(logic.mkNot(logic.mkImpl(interpol, logic.mkNot(partB))));
    if (!solver.check().equals(sstat.False())) {
      return false;
    }
    solver.pop();

    VectorPTRef varsPartA = variables(logic, partA);
    VectorPTRef varsPartB = variables(logic, partB);
    VectorPTRef varsInterpol = variables(logic, interpol);

    // Check symb(I) ⊆ symb(A) ∩ symb(B)
    return varsPartA.containsAll(varsInterpol) && varsPartB.containsAll(varsInterpol);
  }

  @Test
  public void testSolverFactory() {
    Logic logic = LogicFactory.getInstance(Logic_t.QF_UF);

    // a = b
    PTRef varA = logic.mkBoolVar("a");
    PTRef varB = logic.mkBoolVar("b");
    PTRef f = logic.mkEq(varA, varB);

    SMTConfig config = new SMTConfig();
    MainSolver mainSolver = new MainSolver(logic, config, "JavaSmt");
    mainSolver.push(f);

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.True());

    Model model = mainSolver.getModel();

    PTRef valA = model.evaluate(varA);
    PTRef valB = model.evaluate(varB);

    assertThat(valA).isEqualTo(valB);
  }

  @Test
  public void testBooleanLogic() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_bool, "opensmt-test", false);
    Logic logic = osmt.getLogic();

    // a ∧ ¬a
    PTRef varA = logic.mkBoolVar("a");
    PTRef notA = logic.mkNot(varA);
    PTRef f = logic.mkAnd(varA, notA);

    MainSolver mainSolver = osmt.getMainSolver();
    mainSolver.push(f);

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.False());
  }

  @Test
  public void testUninterpretedFunctionLogic() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_uf, "opensmt-test", false);
    Logic logic = osmt.getLogic();

    // Declare sort U
    SRef mySort = logic.declareUninterpretedSort("U");

    // Declare variable a, b
    PTRef varA = logic.mkVar(mySort, "a");
    PTRef varB = logic.mkVar(mySort, "b");

    // Term a=b
    PTRef f0 = logic.mkEq(varA, varB);

    // Declare function f(x)
    VectorSRef sigF = new VectorSRef();
    sigF.add(mySort);
    SymRef funF = logic.declareFun("f", mySort, sigF);

    // Instantiate f for a
    VectorPTRef argFa = new VectorPTRef();
    argFa.add(varA);
    PTRef appFa = logic.mkUninterpFun(funF, argFa);

    // Instantiate f for b
    VectorPTRef argFb = new VectorPTRef();
    argFb.add(varB);
    PTRef appFb = logic.mkUninterpFun(funF, argFb);

    // Term f(a)≠f(b)
    VectorPTRef dist = new VectorPTRef();
    dist.add(appFa);
    dist.add(appFb);
    PTRef f1 = logic.mkDistinct(dist);

    MainSolver mainSolver = osmt.getMainSolver();
    mainSolver.push(f0);
    mainSolver.push(f1);

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.False());
  }

  @Test
  public void testUninterpretedFunctionInterpol() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_uf, "opensmt-test", true);
    Logic logic = osmt.getLogic();

    // Declare sort U
    SRef mysort = logic.declareUninterpretedSort("U");

    // Declare variable a, b, c
    PTRef varA = logic.mkVar(mysort, "a");
    PTRef varB = logic.mkVar(mysort, "b");
    PTRef varC = logic.mkVar(mysort, "c");

    // Term a=b ∧ b=c
    PTRef f0 = logic.mkAnd(logic.mkEq(varA, varB), logic.mkEq(varB, varC));

    // Term a≠c
    VectorPTRef dist = new VectorPTRef();
    dist.add(varA);
    dist.add(varC);
    PTRef f1 = logic.mkDistinct(dist);

    MainSolver mainSolver = osmt.getMainSolver();
    mainSolver.push(f0);
    mainSolver.push(f1);

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.False());

    InterpolationContext context = mainSolver.getInterpolationContext();
    VectorInt mask = new VectorInt();
    mask.add(0);

    // Verify interpolant
    PTRef interpol = context.getSingleInterpolant(mask);
    assertThat(verifyInterpolant(logic, f0, f1, interpol)).isTrue();
  }

  @Test
  public void testLinearIntegerLogic() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_lia, "opensmt-test", false);
    ArithLogic logic = osmt.getLIALogic();

    // Declare variables
    PTRef varA = logic.mkIntVar("a");
    PTRef varC = logic.mkIntVar("c");

    // Create integer constants
    PTRef const0 = logic.mkIntConst("0");
    PTRef const3 = logic.mkIntConst("3");

    // Terms a+3 < c, c ≥ 0
    PTRef f0 = logic.mkLt(logic.mkPlus(varA, const3), varC);
    PTRef f1 = logic.mkGeq(varC, const0);

    MainSolver mainSolver = osmt.getMainSolver();
    mainSolver.push(f0);
    mainSolver.push(f1);

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.True());
  }

  @Test
  public void testLinearIntegerInterpol() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_lia, "opensmt-test", true);
    ArithLogic logic = osmt.getLIALogic();

    // Declare variables
    PTRef varA = logic.mkIntVar("a");
    PTRef varB = logic.mkIntVar("b");
    PTRef varC = logic.mkIntVar("c");

    // Term a>b ∧ b>c
    PTRef f0 = logic.mkAnd(logic.mkGt(varA, varB), logic.mkGt(varB, varC));

    // Term c>a
    PTRef f1 = logic.mkGt(varC, varA);

    MainSolver solver = osmt.getMainSolver();
    solver.push(f0);
    solver.push(f1);

    sstat r = solver.check();
    assertThat(r).isEqualTo(sstat.False());

    InterpolationContext context = solver.getInterpolationContext();
    VectorInt mask = new VectorInt();
    mask.add(0);

    // Verify interpolant
    PTRef interpol = context.getSingleInterpolant(mask);
    assertThat(verifyInterpolant(logic, f0, f1, interpol)).isTrue();

    // Switch interpolation algorithm
    SMTConfig config = osmt.getConfig();
    config.setLRAInterpolationAlgorithm(ItpAlgorithm.getLraDecomposingWeak());

    // Verify second interpolant
    PTRef interpolDweak = context.getSingleInterpolant(mask);
    assertThat(verifyInterpolant(logic, f0, f1, interpolDweak)).isTrue();
  }

  @Test
  public void testIntegerArray() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_alia, "opensmt-test", false);
    ArithLogic logic = osmt.getLIALogic();

    // Declare an integer array variable
    SRef sortIntArray = logic.getArraySort(logic.getSort_int(), logic.getSort_int());
    PTRef varA = logic.mkVar(sortIntArray, "a");

    // Declare variables for the indices i,j and the element e
    PTRef varI = logic.mkIntVar("i");
    PTRef varJ = logic.mkIntVar("j");
    PTRef varE = logic.mkIntVar("e");

    // Term e = select(store(a,i,e),i)
    PTRef eq0 = logic.mkEq(varE, logic.mkSelect(logic.mkStore(varA, varI, varE), varI));

    // Term a = store(a,i,select(a,i))
    PTRef eq1 = logic.mkEq(varA, logic.mkStore(varA, varI, logic.mkSelect(varA, varI)));

    // Term i≠j ⇒ select(store(a,i,e),j) = select(a,j)
    PTRef eq2 =
        logic.mkImpl(
            logic.mkDistinct(varI, varJ),
            logic.mkEq(
                logic.mkSelect(logic.mkStore(varA, varI, varE), varJ), logic.mkSelect(varA, varJ)));

    VectorPTRef neg =
        new VectorPTRef(new PTRef[] {logic.mkNot(eq0), logic.mkNot(eq1), logic.mkNot(eq2)});
    PTRef f = logic.mkOr(neg);

    // Prove that the equations hold for all models
    MainSolver solver = osmt.getMainSolver();
    solver.push(f);

    sstat r = solver.check();
    assertThat(r).isEqualTo(sstat.False());
  }

  @Test
  public void testFormulaIntrospection() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_lia, "opensmt-test", false);
    ArithLogic logic = osmt.getLIALogic();

    // Declare variables
    PTRef varA = logic.mkIntVar("a");
    PTRef varB = logic.mkIntVar("b");
    PTRef varC = logic.mkIntVar("c");

    // Term a+b < -c
    PTRef f = logic.mkLt(logic.mkPlus(varA, varB), logic.mkNeg(varC));

    // Check that there are 3 variables in the term
    VectorPTRef vars = variables(logic, f);
    assertThat(vars.size() == 3).isTrue();
  }

  @Test
  public void testFunctionTemplates() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_lia, "opensmt-test", false);
    ArithLogic logic = osmt.getLIALogic();

    // Define function negate(a) = -1*a

    // FIXME: This will fail the test. Are formal arguments not scoped? See Interpret.cc, line 750
    // PTRef negate_a = logic.mkIntVar("a");

    PTRef negateA = logic.mkIntVar("negate_a");
    PTRef negateBody = logic.mkTimes(logic.getTerm_IntMinusOne(), negateA);

    VectorPTRef negateArgs = new VectorPTRef();
    negateArgs.add(negateA);
    TemplateFunction negateF =
        new TemplateFunction("negate", negateArgs, logic.getSort_int(), negateBody);

    // Declare variable a
    PTRef varA = logic.mkIntVar("a");

    // Instantiate negate for a
    VectorPTRef arg0 = new VectorPTRef();
    arg0.add(varA);
    PTRef app0 = logic.instantiateFunctionTemplate(negateF, arg0);

    // Instantiate negate for negate(a)
    VectorPTRef arg1 = new VectorPTRef();
    arg1.add(app0);
    PTRef app1 = logic.instantiateFunctionTemplate(negateF, arg1);

    // Term negate(negate(a)) ≠ a
    PTRef f = logic.mkNot(logic.mkEq(app1, varA));

    MainSolver solver = osmt.getMainSolver();
    solver.push(f);

    sstat r = solver.check();
    assertThat(r).isEqualTo(sstat.False());
  }

  @Test
  public void testAbort() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_lia, "opensmt-test", false);
    ArithLogic logic = osmt.getLIALogic();

    // Declare variables
    PTRef varA = logic.mkIntVar("a");
    PTRef varC = logic.mkIntVar("c");

    // Create integer constants
    PTRef const0 = logic.mkIntConst("0");
    PTRef const3 = logic.mkIntConst("3");

    // Terms a+3 < c, c ≥ 0
    PTRef f0 = logic.mkLt(logic.mkPlus(varA, const3), varC);
    PTRef f1 = logic.mkGeq(varC, const0);

    MainSolver mainSolver = osmt.getMainSolver();
    mainSolver.push(f0);
    mainSolver.push(f1);

    mainSolver.stop();

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.Undef());
  }

  /* INFO:
   * This testcase was taken from VariableNames test and shows that OpenSMT does
   * not handle \u0000 in variable names correctly.
   */
  @Test
  public void testNulString() {
    Logic logic = LogicFactory.getLogicAll();

    // Any String containing \u0000 should work here
    PTRef nil = logic.mkBoolVar("\u0000");

    // This test fails intermittently, so i needs to be chosen large enough
    for (int i = 0; i < 1000; i++) {
      String pp = logic.pp(nil);
      assertThat(pp)
          .isEqualTo(
              "\u0000"); // The String returned in the failed case is just \u0000 - without the `|`
      // characters

      /* Note:
       * I patched OpenSMT to fix the issue and logic.pp(nil) should now always
       * return "\u0000"
       *
       * OpenSMT internally uses a function that converts the letters of the
       * variable name to their ASCII code and then looks up that code in a
       * table to see if any of them are reserved. In that case the entire
       * variable name needs to be escaped and is put in '|' quotes. Due to a
       * bug this function only works for regular ASCII characters with a value
       * less than 128. However in our case the unicode character \u0000 gets
       * represented as the two byte sequence C0 80 as Java uses modifie utf8
       * for Strings. With this encoding \u0000 can occur in a C String as its
       * not confused with the terminating null. However due to the bug the
       * escape sequence is converted to a signed value and since the character
       * code is greater than 127 that value is negative. The negative index
       * then is looked up in the table and will generally hit a non-zero value
       * in memory - which is then interpreted as 'true' and quotes are added.
       * However occasionally the value happens to be zero and that's why the
       * test failed intermittently.
       *
       * With the patch the conversion is now handled correctly, and there's no
       * need to quote the escape sequence for \u0000.
       */
    }
  }

  @Test
  public void testExample() {
    ArithLogic logic = LogicFactory.getLIAInstance();

    PTRef varA = logic.mkIntVar("a");
    PTRef varB = logic.mkIntVar("b");
    PTRef varC = logic.mkIntVar("c");

    PTRef formulaA = logic.mkAnd(logic.mkLt(varA, varB), logic.mkLt(varC, varA));
    PTRef formulaB = logic.mkLt(varB, varC);

    SMTConfig config = new SMTConfig();
    config.setOption(":produce-interpolants", new SMTOption(1));

    MainSolver mainSolver = new MainSolver(logic, config, "JavaSmt");
    mainSolver.push(formulaA);
    mainSolver.push(formulaB);

    sstat check1 = mainSolver.check();
    System.out.println(check1);

    InterpolationContext context = mainSolver.getInterpolationContext();
    VectorInt mask = new VectorInt(List.of(0));
    PTRef interpol = context.getSingleInterpolant(mask);
    System.out.println(logic.pp(interpol));

    mainSolver.pop();

    sstat check2 = mainSolver.check();
    System.out.println(check2);

    Model model = mainSolver.getModel();
    for (PTRef var : Arrays.asList(varA, varB, varC)) {
      PTRef val = model.evaluate(var);
      System.out.println(logic.pp(val));
    }
  }
}
