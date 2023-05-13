// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lob.java_smt.solvers.opensmt;

import static org.junit.Assert.assertTrue;

import org.sosy_lab.common.NativeLibraries;
import org.junit.Test;

import opensmt.*;

public class OpenSmtNativeAPITest {
  static {
    NativeLibraries.loadLibrary("opensmt");
    NativeLibraries.loadLibrary("opensmtjava");
  }

  /**
   * Return free variables
   */
  private VectorPTRef variables(Logic logic, PTRef term) {
    if(logic.isVar(term)) {
      VectorPTRef vars = new VectorPTRef();
      vars.add(term);
      return vars;
    } else {
      VectorPTRef vars = new VectorPTRef();
      for(PTRef sub : logic.getSubterms(term)) {
        VectorPTRef res = variables(logic, sub);
        vars.addAll(res);
      }
      return vars;
    }
  }

  /**
   * Verify that interpolant conditions are fullfilled
   * See VerificationUtils.h in OpenSmt
   */
  private boolean verifyInterpolant(Logic logic, PTRef partA, PTRef partB, PTRef interpol) {
    SMTConfig config = new SMTConfig();
    MainSolver solver = new MainSolver(logic, config, "opensmt-verifier");
    
    // Check A ⊨ I
    solver.push(logic.mkNot(logic.mkImpl(partA, interpol)));
    if(!solver.check().isFalse()) return false;
    solver.pop();
    
    // Check I ⊨ ¬B
    solver.push(logic.mkNot(logic.mkImpl(interpol, logic.mkNot(partB))));
    if(!solver.check().isFalse()) return false;
    solver.pop();
    
    VectorPTRef vars_partA = variables(logic, partA);
    VectorPTRef vars_partB = variables(logic, partB);
    VectorPTRef vars_interpol = variables(logic, interpol);

    // Check symb(I) ⊆ symb(A) ∩ symb(B)
    return vars_partA.containsAll(vars_interpol) && vars_partB.containsAll(vars_interpol);
    }
  
  @Test
  public void testBooleanLogic() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_bool, "opensmt-test", false);
    Logic logic = osmt.getLogic();

    // a ∧ ¬a
    PTRef a  = logic.mkBoolVar("a");
    PTRef na = logic.mkNot(a);
    PTRef f  = logic.mkAnd(a, na);
    
    MainSolver mainSolver = osmt.getMainSolver();
    mainSolver.push(f);
    
    sstat r = mainSolver.check();
    assertTrue(r.isFalse());
  }

  @Test
  public void testUninterpretedFunctionLogic() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_uf, "opensmt-test", false);
    Logic logic = osmt.getLogic();

    // Declare sort U
    SRef mysort = logic.declareUninterpretedSort("U");

    // Declare variable a, b
    PTRef var_a = logic.mkVar(mysort, "a");
    PTRef var_b = logic.mkVar(mysort, "b");

    // Term a=b
    PTRef f0 = logic.mkEq(var_a, var_b);
    
    // Declare function f(x)
    VectorSRef sig_f = new VectorSRef();
    sig_f.add(mysort);
    SymRef uf_f = logic.declareFun("f", mysort, sig_f);

    // Instantiate f for a
    VectorPTRef arg_fa = new VectorPTRef();
    arg_fa.add(var_a);
    PTRef app_fa = logic.mkUninterpFun(uf_f, arg_fa);

    // Instantiate f for b
    VectorPTRef arg_fb = new VectorPTRef();
    arg_fb.add(var_b);
    PTRef app_fb = logic.mkUninterpFun(uf_f, arg_fb);
    
    // Term f(a)≠f(b)
    VectorPTRef dist = new VectorPTRef();
    dist.add(app_fa);
    dist.add(app_fb);
    PTRef f1 = logic.mkDistinct(dist);
    
    MainSolver mainSolver = osmt.getMainSolver();
    mainSolver.push(f0);
    mainSolver.push(f1);
    
    sstat r = mainSolver.check();
    assertTrue(r.isFalse());
  }
  
  @Test
  public void testUninterpretedFunctionInterpol() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_uf, "opensmt-test", true);
    Logic logic = osmt.getLogic();

    // Declare sort U
    SRef mysort = logic.declareUninterpretedSort("U");

    // Declare variable a, b, c
    PTRef var_a = logic.mkVar(mysort, "a");
    PTRef var_b = logic.mkVar(mysort, "b");
    PTRef var_c = logic.mkVar(mysort, "c");

    // Term a=b ∧ b=c
    PTRef f0 = logic.mkAnd(logic.mkEq(var_a, var_b), logic.mkEq(var_b, var_c));
    
    // Term a≠c
    VectorPTRef dist = new VectorPTRef();
    dist.add(var_a);
    dist.add(var_c);
    PTRef f1 = logic.mkDistinct(dist);

    MainSolver mainSolver = osmt.getMainSolver();
    mainSolver.push(f0);
    mainSolver.push(f1);

    sstat r = mainSolver.check();
    assertTrue(r.isFalse());
    
    InterpolationContext context = mainSolver.getInterpolationContext();
    VectorInt mask = new VectorInt();
    mask.add(0);
    
    // Verify interpolant
    PTRef interpol = context.getSingleInterpolant(mask);
    assertTrue(verifyInterpolant(logic, f0, f1, interpol));
  }
  
  @Test
  public void testLinearIntegerLogic() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_lia, "opensmt-test", false);
    ArithLogic logic = osmt.getLIALogic();

    // Declare variables
    PTRef var_a = logic.mkIntVar("a");
    PTRef var_c = logic.mkIntVar("c");

    // Create integer constants
    PTRef const_0 = logic.mkIntConst("0");
    PTRef const_3 = logic.mkIntConst("3");

    // Terms a+3 < c, c ≥ 0
    PTRef f_0 = logic.mkLt(logic.mkPlus(var_a, const_3), var_c);
    PTRef f_1 = logic.mkGeq(var_c, const_0);
    
    MainSolver mainSolver = osmt.getMainSolver();
    mainSolver.push(f_0);
    mainSolver.push(f_1);
    
    sstat r = mainSolver.check();
    assertTrue(r.isTrue());
  }
  
  @Test
  public void testLinearIntegerInterpol() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_lia, "opensmt-test", true);
    ArithLogic logic = osmt.getLIALogic();

    // Declare variables
    PTRef var_a = logic.mkIntVar("a");
    PTRef var_b = logic.mkIntVar("b");
    PTRef var_c = logic.mkIntVar("c");

    // Term a>b ∧ b>c
    PTRef f0 = logic.mkAnd(logic.mkGt(var_a, var_b), logic.mkGt(var_b, var_c));

    // Term c>a
    PTRef f1 = logic.mkGt(var_c, var_a);

    MainSolver solver = osmt.getMainSolver();
    solver.push(f0);
    solver.push(f1);
    
    sstat r = solver.check();
    assertTrue(r.isFalse());
    
    InterpolationContext context = solver.getInterpolationContext();
    VectorInt mask = new VectorInt();
    mask.add(0);
    
    // Verify interpolant
    PTRef interpol = context.getSingleInterpolant(mask);
    assertTrue(verifyInterpolant(logic, f0, f1, interpol));
    
    // Switch interpolation algorithm
    SMTConfig config = osmt.getConfig();
    config.setLRAInterpolationAlgorithm(ItpAlgorithm.getLraDecomposingWeak());
    
    // Verify second interpolant
    PTRef interpol_dweak = context.getSingleInterpolant(mask);
    assertTrue(verifyInterpolant(logic, f0, f1, interpol_dweak));
  }
  
  @Test
  public void testIntegerArray() {
    // TODO: add array test
  }
  
  @Test
  public void testFormulaIntrospection() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_lia, "opensmt-test", false);
    ArithLogic logic = osmt.getLIALogic();
    
    // Declare variables
    PTRef var_a = logic.mkIntVar("a");
    PTRef var_b = logic.mkIntVar("b");
    PTRef var_c = logic.mkIntVar("c");
    
    // Term a+b < -c 
    PTRef f = logic.mkLt(logic.mkPlus(var_a, var_b), logic.mkNeg(var_c));

    // Check that there are 3 variables in the term
    VectorPTRef vars = variables(logic, f);
    assertTrue(vars.size() == 3);
  }
  
  @Test
  public void testFunctionTemplates() {
    OpenSmt osmt = new OpenSmt(opensmt_logic.qf_lia, "opensmt-test", false);
    ArithLogic logic = osmt.getLIALogic();
    
    // Define function negate(a) = -1*a

    // FIXME: This will fail the test. Are formal arguments not scoped?
    // PTRef negate_a = logic.mkIntVar("a");
    
    PTRef negate_a = logic.mkIntVar("negate_a");
    PTRef negate_body = logic.mkTimes(logic.getTerm_IntMinusOne(), negate_a);
    
    VectorPTRef negate_args = new VectorPTRef();
    negate_args.add(negate_a);
    TemplateFunction negate_tf = new TemplateFunction("negate", negate_args, logic.getSort_int(), negate_body);
    
    // Declare variable a
    PTRef var_a = logic.mkIntVar("a");
    
    // Instantiate negate for a
    VectorPTRef arg_0 = new VectorPTRef();
    arg_0.add(var_a);
    PTRef app_0 = logic.instantiateFunctionTemplate(negate_tf, arg_0);
    
    // Instantiate negate for negate(a)
    VectorPTRef arg_1 = new VectorPTRef();
    arg_1.add(app_0);
    PTRef app_1 = logic.instantiateFunctionTemplate(negate_tf, arg_1);
    
    // Term negate(negate(a)) ≠ a
    PTRef f = logic.mkNot(logic.mkEq(app_1, var_a));
    
    MainSolver solver = osmt.getMainSolver();
    solver.push(f);
    
    sstat r = solver.check();    
    assertTrue(r.isFalse());
  }  
}
