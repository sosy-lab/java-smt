/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.solver.test;

import static com.google.common.collect.Lists.newArrayList;
import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.fail;
import static org.sosy_lab.solver.api.FormulaType.BooleanType;
import static org.sosy_lab.solver.api.FormulaType.IntegerType;

import com.google.common.collect.Lists;
import com.google.common.truth.TruthJUnit;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.basicimpl.tactics.Tactic;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

@RunWith(Parameterized.class)
public class SolverTacticsTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Test
  public void nnfTacticDefaultTest1() throws SolverException, InterruptedException {
    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula not_a_b = bmgr.not(bmgr.equivalence(a, b));

    BooleanFormula nnf = mgr.applyTactic(not_a_b, Tactic.NNF);
    assertThatFormula(nnf).isEquivalentTo(not_a_b);
    NNFChecker checker = new NNFChecker(mgr);
    bmgr.visit(nnf, checker);
    assertThat(checker.isInNNF()).isTrue();
  }

  @Test
  public void nnfTacticDefaultTest2() throws SolverException, InterruptedException {
    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula c = bmgr.makeVariable("c");
    BooleanFormula not_ITE_a_b_c = bmgr.not(bmgr.ifThenElse(a, b, c));

    BooleanFormula nnf = mgr.applyTactic(not_ITE_a_b_c, Tactic.NNF);
    assertThatFormula(nnf).isEquivalentTo(not_ITE_a_b_c);
    NNFChecker checker = new NNFChecker(mgr);
    checker.visit(nnf);
    assertThat(checker.isInNNF()).isTrue();
  }

  @Test
  public void cnfTacticDefaultTest1() throws SolverException, InterruptedException {
    TruthJUnit.assume().that(solver).isEqualTo(Solvers.Z3);
    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula equiv_a_b = bmgr.equivalence(a, b);
    BooleanFormula not_equiv_a_b = bmgr.not(equiv_a_b);

    BooleanFormula cnf_equiv_a_b = mgr.applyTactic(equiv_a_b, Tactic.TSEITIN_CNF);
    assertThatFormula(cnf_equiv_a_b).isEquisatisfiableTo(equiv_a_b);
    CNFChecker checker = new CNFChecker(mgr);
    checker.visit(cnf_equiv_a_b);
    assertThat(checker.isInCNF()).isTrue();

    BooleanFormula cnf_not_equiv_a_b = mgr.applyTactic(not_equiv_a_b, Tactic.TSEITIN_CNF);
    assertThatFormula(cnf_not_equiv_a_b).isEquisatisfiableTo(not_equiv_a_b);
    checker = new CNFChecker(mgr);
    checker.visit(cnf_not_equiv_a_b);
    assertThat(checker.isInCNF()).isTrue();
  }

  @Test
  public void cnfTacticDefaultTest2() throws SolverException, InterruptedException {
    TruthJUnit.assume().that(solver).isEqualTo(Solvers.Z3);
    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula c = bmgr.makeVariable("c");
    BooleanFormula ITE_a_b_c = bmgr.ifThenElse(a, b, c);
    BooleanFormula not_ITE_a_b_c = bmgr.not(bmgr.ifThenElse(a, b, c));

    BooleanFormula cnf_ITE_a_b_c = mgr.applyTactic(ITE_a_b_c, Tactic.TSEITIN_CNF);
    assertThatFormula(cnf_ITE_a_b_c).isEquisatisfiableTo(ITE_a_b_c);
    CNFChecker checker = new CNFChecker(mgr);
    checker.visit(cnf_ITE_a_b_c);
    assertThat(checker.isInCNF()).isTrue();

    BooleanFormula cnf_not_ITE_a_b_c = mgr.applyTactic(not_ITE_a_b_c, Tactic.TSEITIN_CNF);

    assertThatFormula(cnf_not_ITE_a_b_c).isEquisatisfiableTo(not_ITE_a_b_c);
    checker = new CNFChecker(mgr);
    checker.visit(cnf_not_ITE_a_b_c);
    assertThat(checker.isInCNF()).isTrue();
  }

  @Test
  public void cnfTacticDefaultTest3() throws SolverException, InterruptedException {
    TruthJUnit.assume().that(solver).isEqualTo(Solvers.Z3);
    BooleanFormula x = bmgr.makeVariable("x");
    BooleanFormula y = bmgr.makeVariable("y");
    BooleanFormula z = bmgr.makeVariable("z");
    BooleanFormula w = bmgr.makeVariable("w");
    BooleanFormula u = bmgr.makeVariable("u");
    BooleanFormula v = bmgr.makeVariable("v");
    List<BooleanFormula> disjuncts = new ArrayList<>();
    disjuncts.add(bmgr.and(x, y));
    disjuncts.add(bmgr.and(z, w));
    disjuncts.add(bmgr.and(u, v));
    BooleanFormula f = bmgr.or(disjuncts);

    BooleanFormula cnf = mgr.applyTactic(f, Tactic.TSEITIN_CNF);
    assertThatFormula(cnf).isEquisatisfiableTo(f);
    CNFChecker checker = new CNFChecker(mgr);
    checker.visit(cnf);
    assertThat(checker.isInCNF()).isTrue();
  }

  @Test
  public void ufEliminationSimpleTest() throws SolverException, InterruptedException {
    // f := uf(v1, v3) == uf(v2, v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");
    BooleanFormula v1EqualsV2 = imgr.equal(variable1, variable2);
    BooleanFormula v3EqualsV4 = imgr.equal(variable3, variable4);

    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf", BooleanType, Lists.newArrayList(IntegerType, IntegerType));
    BooleanFormula f1 = fmgr.callUF(uf2Decl, Lists.newArrayList(variable1, variable3));
    BooleanFormula f2 = fmgr.callUF(uf2Decl, Lists.newArrayList(variable2, variable4));
    BooleanFormula f = bmgr.equivalence(f1, f2);
    BooleanFormula argsEqual = bmgr.and(v1EqualsV2, v3EqualsV4);

    BooleanFormula withOutUfs = mgr.applyTactic(f, Tactic.ACKERMANNIZATION);
    assertThatFormula(argsEqual).implies(f); // sanity check
    assertThatFormula(argsEqual).implies(withOutUfs);

    // check that UFs were really eliminated
    Map<String, Formula> variablesAndUFs = mgr.extractVariablesAndUFs(withOutUfs);
    Map<String, Formula> variables = mgr.extractVariables(withOutUfs);
    assertThat(variablesAndUFs).doesNotContainKey("uf");
    assertThat(variablesAndUFs).isEqualTo(variables);
  }

  @Test
  public void ufEliminationNestedUfsTest() throws SolverException, InterruptedException {
    // f :=uf2(uf1(v1, v2), v3) == uf2(uf1(v2, v1), v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");
    BooleanFormula v1EqualsV2 = imgr.equal(variable1, variable2);
    BooleanFormula v3EqualsV4 = imgr.equal(variable3, variable4);

    FunctionDeclaration<IntegerFormula> uf1Decl =
        fmgr.declareUF("uf1", IntegerType, Lists.newArrayList(IntegerType, IntegerType));
    Formula uf1a = fmgr.callUF(uf1Decl, variable1, variable2);
    Formula uf1b = fmgr.callUF(uf1Decl, variable2, variable1);
    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf2", BooleanType, Lists.newArrayList(IntegerType, IntegerType));
    BooleanFormula f1 = fmgr.callUF(uf2Decl, Lists.newArrayList(uf1a, variable3));
    BooleanFormula f2 = fmgr.callUF(uf2Decl, Lists.newArrayList(uf1b, variable4));
    BooleanFormula f = bmgr.equivalence(f1, f2);
    BooleanFormula argsEqual = bmgr.and(v1EqualsV2, v3EqualsV4);

    BooleanFormula withOutUfs = mgr.applyTactic(f, Tactic.ACKERMANNIZATION);
    assertThatFormula(argsEqual).implies(f); // sanity check
    assertThatFormula(argsEqual).implies(withOutUfs);

    // check that UFs were really eliminated
    Map<String, Formula> variablesAndUFs = mgr.extractVariablesAndUFs(withOutUfs);
    Map<String, Formula> variables = mgr.extractVariables(withOutUfs);
    assertThat(variablesAndUFs).doesNotContainKey("uf1");
    assertThat(variablesAndUFs).doesNotContainKey("uf2");
    assertThat(variablesAndUFs).isEqualTo(variables);
  }

  @Test
  public void ufEliminationNesteQuantifierTest() throws InterruptedException {
    requireQuantifiers();
    // f := exists v1,v2v,v3,v4 : uf(v1, v3) == uf(v2, v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");

    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf", BooleanType, Lists.newArrayList(IntegerType, IntegerType));
    BooleanFormula f1 = fmgr.callUF(uf2Decl, Lists.newArrayList(variable1, variable3));
    BooleanFormula f2 = fmgr.callUF(uf2Decl, Lists.newArrayList(variable2, variable4));
    BooleanFormula f =
        qmgr.exists(
            newArrayList(variable1, variable2, variable3, variable4), bmgr.equivalence(f1, f2));

    try {
      mgr.applyTactic(f, Tactic.ACKERMANNIZATION);
      fail();
    } catch (IllegalArgumentException expected) {
    }
  }

  private static class CNFChecker implements BooleanFormulaVisitor<Void> {

    private final BooleanFormulaManager bfmgr;

    boolean startsWithAnd = false;
    boolean containsMoreAnd = false;
    boolean started = false;

    protected CNFChecker(FormulaManager pFmgr) {
      bfmgr = pFmgr.getBooleanFormulaManager();
    }

    Void visit(BooleanFormula f) {
      // TODO rewrite using RecursiveBooleanFormulaVisitor should make this class easier
      return bfmgr.visit(f, this);
    }

    public boolean isInCNF() {
      return (startsWithAnd && !containsMoreAnd) || (started && !startsWithAnd);
    }

    @Override
    public Void visitConstant(boolean value) {
      started = true;
      return null;
    }

    @Override
    public Void visitBoundVar(BooleanFormula f, int deBruijnIdx) {
      started = true;
      return null;
    }

    @Override
    public Void visitAtom(BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> decl) {
      started = true;
      return null;
    }

    @Override
    public Void visitNot(BooleanFormula pOperand) {
      started = true;
      return visit(pOperand);
    }

    @Override
    public Void visitAnd(List<BooleanFormula> pOperands) {
      if (!started) {
        started = true;
        startsWithAnd = true;
      } else {
        containsMoreAnd = true;
      }
      pOperands.forEach(this::visit);
      return null;
    }

    @Override
    public Void visitOr(List<BooleanFormula> pOperands) {
      if (started) {
        pOperands.forEach(this::visit);
      }
      return null;
    }

    @Override
    public Void visitXor(BooleanFormula operand1, BooleanFormula operand2) {
      started = true;
      return null;
    }

    @Override
    public Void visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
      if (started) {
        visit(pOperand1);
        visit(pOperand2);
      }
      return null;
    }

    @Override
    public Void visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
      if (started) {
        visit(pOperand1);
        visit(pOperand2);
      }
      return null;
    }

    @Override
    public Void visitIfThenElse(
        BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
      if (started) {
        visit(pCondition);
        visit(pThenFormula);
        visit(pElseFormula);
      }
      return null;
    }

    @Override
    public Void visitQuantifier(
        Quantifier quantifier,
        BooleanFormula quantifierAST,
        List<Formula> boundVars,
        BooleanFormula pBody) {
      if (started) {
        visit(pBody);
      }
      return null;
    }
  }

  private static class NNFChecker implements BooleanFormulaVisitor<Void> {

    private final BooleanFormulaManager bfmgr;

    boolean wasLastVisitNot = false;
    boolean notOnlyAtAtoms = true;

    protected NNFChecker(FormulaManager pFmgr) {
      bfmgr = pFmgr.getBooleanFormulaManager();
    }

    Void visit(BooleanFormula f) {
      // TODO rewrite using RecursiveBooleanFormulaVisitor should make this class easier
      return bfmgr.visit(f, this);
    }

    public boolean isInNNF() {
      return notOnlyAtAtoms;
    }

    @Override
    public Void visitConstant(boolean value) {
      wasLastVisitNot = false;
      return null;
    }

    @Override
    public Void visitBoundVar(BooleanFormula var, int deBruijnIdx) {
      wasLastVisitNot = false;
      return null;
    }

    @Override
    public Void visitAtom(BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> decl) {
      wasLastVisitNot = false;
      return null;
    }

    @Override
    public Void visitNot(BooleanFormula pOperand) {
      wasLastVisitNot = true;
      return visit(pOperand);
    }

    @Override
    public Void visitAnd(List<BooleanFormula> pOperands) {
      if (wasLastVisitNot) {
        notOnlyAtAtoms = false;
      } else {
        pOperands.forEach(this::visit);
      }
      return null;
    }

    @Override
    public Void visitOr(List<BooleanFormula> pOperands) {
      if (wasLastVisitNot) {
        notOnlyAtAtoms = false;
      } else {
        pOperands.forEach(this::visit);
      }
      return null;
    }

    @Override
    public Void visitXor(BooleanFormula operand1, BooleanFormula operand2) {
      return null;
    }

    @Override
    public Void visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
      if (wasLastVisitNot) {
        notOnlyAtAtoms = false;
      } else {
        visit(pOperand1);
        visit(pOperand2);
      }
      return null;
    }

    @Override
    public Void visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
      if (wasLastVisitNot) {
        notOnlyAtAtoms = false;
      } else {
        visit(pOperand1);
        visit(pOperand2);
      }
      return null;
    }

    @Override
    public Void visitIfThenElse(
        BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
      if (wasLastVisitNot) {
        notOnlyAtAtoms = false;
      } else {
        visit(pCondition);
        visit(pThenFormula);
        visit(pElseFormula);
      }
      return null;
    }

    @Override
    public Void visitQuantifier(
        Quantifier quantifier,
        BooleanFormula quantifierAST,
        List<Formula> boundVars,
        BooleanFormula pBody) {
      if (wasLastVisitNot) {
        notOnlyAtAtoms = false;
      } else {
        visit(pBody);
      }
      return null;
    }
  }
}
