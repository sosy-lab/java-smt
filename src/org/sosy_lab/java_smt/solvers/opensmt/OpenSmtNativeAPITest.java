// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import static com.google.common.truth.Truth.assertThat;

import opensmt.ArithLogic;
import opensmt.InterpolationContext;
import opensmt.ItpAlgorithm;
import opensmt.Logic;
import opensmt.LogicFactory;
import opensmt.Logic_t;
import opensmt.MainSolver;
import opensmt.Model;
import opensmt.OpenSmt;
import opensmt.PTRef;
import opensmt.SMTConfig;
import opensmt.SRef;
import opensmt.SymRef;
import opensmt.TemplateFunction;
import opensmt.VectorInt;
import opensmt.VectorPTRef;
import opensmt.VectorSRef;
import opensmt.opensmt_logic;
import opensmt.sstat;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

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
    if (!solver.check().isFalse()) {
      return false;
    }
    solver.pop();

    // Check I ⊨ ¬B
    solver.push(logic.mkNot(logic.mkImpl(interpol, logic.mkNot(partB))));
    if (!solver.check().isFalse()) {
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
    assertThat(r.isTrue()).isTrue();

    Model model = mainSolver.getModel();

    PTRef valA = model.evaluate(varA);
    PTRef valB = model.evaluate(varB);

    assertThat(valA.equals(valB)).isTrue();
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
    assertThat(r.isFalse()).isTrue();
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
    assertThat(r.isFalse()).isTrue();
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
    assertThat(r.isFalse()).isTrue();

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
    assertThat(r.isTrue()).isTrue();
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
    assertThat(r.isFalse()).isTrue();

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
    assertThat(r.isFalse()).isTrue();
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
    assertThat(r.isFalse()).isTrue();
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
    assertThat(r.isUndef()).isTrue();
  }

  /* FIXME: Hangs if interpolation is enabled. Translated from InterpolatingProverTest
  @Test
  public void testSimpleInterpolation() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_lia, "opensmt-test", true);
    ArithLogic logic = osmt.getLIALogic();

    PTRef x = logic.mkIntVar("x");
    PTRef y = logic.mkIntVar("y");
    PTRef z = logic.mkIntVar("z");

    PTRef f1 = logic.mkEq(y, logic.mkTimes(logic.mkIntConst("2"), x));
    PTRef f2 = logic.mkEq(y, logic.mkPlus(logic.mkIntConst("1"), logic.mkTimes(z, logic.mkIntConst("2"))));

    MainSolver mainSolver = osmt.getMainSolver();
    mainSolver.push(f1);
    mainSolver.push(f2);

    sstat r = mainSolver.check();
    assertThat(r.isFalse()).isTrue();
  }
  */
}
