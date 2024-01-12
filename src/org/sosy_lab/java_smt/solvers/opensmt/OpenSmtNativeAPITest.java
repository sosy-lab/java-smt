// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import static com.google.common.truth.Truth.assertThat;

import org.junit.AssumptionViolatedException;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.solvers.opensmt.api.ArithLogic;
import org.sosy_lab.java_smt.solvers.opensmt.api.InterpolationContext;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.LogicFactory;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic_t;
import org.sosy_lab.java_smt.solvers.opensmt.api.MainSolver;
import org.sosy_lab.java_smt.solvers.opensmt.api.Model;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SMTConfig;
import org.sosy_lab.java_smt.solvers.opensmt.api.SMTOption;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SymRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.TemplateFunction;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorInt;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorPTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorSRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.sstat;

public class OpenSmtNativeAPITest {

  @BeforeClass
  public static void load() {
    try {
      NativeLibraries.loadLibrary("opensmt");
      NativeLibraries.loadLibrary("opensmtjava");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("OpenSMT is not available", e);
    }
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
    solver.push();
    solver.insertFormula(logic.mkNot(logic.mkImpl(partA, interpol)));
    if (!solver.check().equals(sstat.False())) {
      return false;
    }
    solver.pop();

    // Check I ⊨ ¬B
    solver.push();
    solver.insertFormula(logic.mkNot(logic.mkImpl(interpol, logic.mkNot(partB))));
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
    MainSolver mainSolver = new MainSolver(logic, config, "opensmt-test");

    mainSolver.push();
    mainSolver.insertFormula(f);

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.True());

    Model model = mainSolver.getModel();

    PTRef valA = model.evaluate(varA);
    PTRef valB = model.evaluate(varB);

    assertThat(valA).isEqualTo(valB);
  }

  @Test
  public void testBooleanLogic() {
    Logic logic = LogicFactory.getInstance(Logic_t.QF_BOOL);

    // a ∧ ¬a
    PTRef varA = logic.mkBoolVar("a");
    PTRef notA = logic.mkNot(varA);
    PTRef f = logic.mkAnd(varA, notA);

    SMTConfig config = new SMTConfig();
    MainSolver mainSolver = new MainSolver(logic, config, "opensmt-test");

    mainSolver.push();
    mainSolver.insertFormula(f);

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.False());
  }

  @Test
  public void testUninterpretedFunctionLogic() {
    Logic logic = LogicFactory.getInstance(Logic_t.QF_UF);

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

    SMTConfig config = new SMTConfig();
    MainSolver mainSolver = new MainSolver(logic, config, "opensmt-test");

    mainSolver.push();
    mainSolver.insertFormula(f0);
    mainSolver.push();
    mainSolver.insertFormula(f1);

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.False());
  }

  @Test
  public void testUninterpretedFunctionInterpol() {
    Logic logic = LogicFactory.getInstance(Logic_t.QF_UF);

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

    SMTConfig config = new SMTConfig();
    config.setOption(":produce-interpolants", new SMTOption(true));
    MainSolver mainSolver = new MainSolver(logic, config, "opensmt-test");

    mainSolver.push();
    mainSolver.insertFormula(f0);
    mainSolver.push();
    mainSolver.insertFormula(f1);

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
    ArithLogic logic = LogicFactory.getLAInstance(Logic_t.QF_LIA);

    // Declare variables
    PTRef varA = logic.mkIntVar("a");
    PTRef varC = logic.mkIntVar("c");

    // Create integer constants
    PTRef const0 = logic.mkIntConst("0");
    PTRef const3 = logic.mkIntConst("3");

    // Terms a+3 < c, c ≥ 0
    PTRef f0 = logic.mkLt(logic.mkPlus(varA, const3), varC);
    PTRef f1 = logic.mkGeq(varC, const0);

    SMTConfig config = new SMTConfig();
    MainSolver mainSolver = new MainSolver(logic, config, "opensmt-test");

    mainSolver.push();
    mainSolver.insertFormula(f0);
    mainSolver.push();
    mainSolver.insertFormula(f1);

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.True());
  }

  @Test
  public void testLinearIntegerInterpol() {
    ArithLogic logic = LogicFactory.getLAInstance(Logic_t.QF_LIA);

    // Declare variables
    PTRef varA = logic.mkIntVar("a");
    PTRef varB = logic.mkIntVar("b");
    PTRef varC = logic.mkIntVar("c");

    // Term a>b ∧ b>c
    PTRef f0 = logic.mkAnd(logic.mkGt(varA, varB), logic.mkGt(varB, varC));

    // Term c>a
    PTRef f1 = logic.mkGt(varC, varA);

    SMTConfig config = new SMTConfig();
    config.setOption(":produce-interpolants", new SMTOption(true));
    MainSolver solver = new MainSolver(logic, config, "opensmt-test");

    solver.push();
    solver.insertFormula(f0);
    solver.push();
    solver.insertFormula(f1);

    sstat r = solver.check();
    assertThat(r).isEqualTo(sstat.False());

    InterpolationContext context = solver.getInterpolationContext();
    VectorInt mask = new VectorInt();
    mask.add(0);

    // Verify interpolant
    PTRef interpol = context.getSingleInterpolant(mask);
    assertThat(verifyInterpolant(logic, f0, f1, interpol)).isTrue();

    // Switch interpolation algorithm to 'LraDecompositionWeak'
    config.setOption(":interpolation-lra-algorithm", new SMTOption(5));

    // Verify second interpolant
    PTRef interpolDweak = context.getSingleInterpolant(mask);
    assertThat(verifyInterpolant(logic, f0, f1, interpolDweak)).isTrue();
  }

  @Test
  public void testIntegerArray() {
    ArithLogic logic = LogicFactory.getLAInstance(Logic_t.QF_ALIA);

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
    SMTConfig config = new SMTConfig();
    MainSolver solver = new MainSolver(logic, config, "opensmt-test");

    solver.push();
    solver.insertFormula(f);

    sstat r = solver.check();
    assertThat(r).isEqualTo(sstat.False());
  }

  @Test
  public void testFormulaIntrospection() {
    ArithLogic logic = LogicFactory.getLAInstance(Logic_t.QF_LIA);

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
    ArithLogic logic = LogicFactory.getLAInstance(Logic_t.QF_LIA);

    // Define function negate(a) = -1*a

    // NOTE: We have to use "negateA" instead of just "a" as variable name as
    // OpenSMT does not properly scope formal arguments.
    PTRef negateA = logic.mkIntVar("negateA");
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

    SMTConfig config = new SMTConfig();
    MainSolver solver = new MainSolver(logic, config, "opensmt-test");

    solver.push();
    solver.insertFormula(f);

    sstat r = solver.check();
    assertThat(r).isEqualTo(sstat.False());
  }

  @Test
  public void testAbort() {
    ArithLogic logic = LogicFactory.getLAInstance(Logic_t.QF_LIA);

    // Declare variables
    PTRef varA = logic.mkIntVar("a");
    PTRef varC = logic.mkIntVar("c");

    // Create integer constants
    PTRef const0 = logic.mkIntConst("0");
    PTRef const3 = logic.mkIntConst("3");

    // Terms a+3 < c, c ≥ 0
    PTRef f0 = logic.mkLt(logic.mkPlus(varA, const3), varC);
    PTRef f1 = logic.mkGeq(varC, const0);

    SMTConfig config = new SMTConfig();
    MainSolver mainSolver = new MainSolver(logic, config, "opensmt-test");

    mainSolver.push();
    mainSolver.insertFormula(f0);
    mainSolver.push();
    mainSolver.insertFormula(f1);

    mainSolver.stop();

    sstat r = mainSolver.check();
    assertThat(r).isEqualTo(sstat.Undef());
  }
}
