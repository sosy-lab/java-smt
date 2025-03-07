/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;

import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class QuantifierEliminationTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void testSolverIndependentQuantifierEliminationWithUltimateEliminator()
      throws SolverException, InterruptedException {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.YICES2, Solvers.MATHSAT5);

    qmgr.setOption(ProverOptions.SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION);

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    // Formula: forall z, (z = x => z > y)
    BooleanFormula query =
        qmgr.forall(z, bmgr.implication(imgr.equal(z, x), imgr.greaterThan(z, y)));
    query = qmgr.eliminateQuantifiers(query);

    assertThatFormula(query).isEquivalentTo(imgr.greaterThan(x, y));
  }

  @Test
  public void testSolverIndependentQuantifierEliminationWithUltimateEliminatorWithArray()
      throws SolverException, InterruptedException {
    requireIntegers();
    requireArrays();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.MATHSAT5);

    qmgr.setOption(ProverOptions.SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION);

    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula i = imgr.makeVariable("i");

    ArrayFormula<IntegerFormula, IntegerFormula> var =
        amgr.makeArray("arr", FormulaType.IntegerType, FormulaType.IntegerType);
    BooleanFormula query = qmgr.forall(var, imgr.equal(amgr.select(var, k), amgr.select(var, i)));

    query = qmgr.eliminateQuantifiers(query);

    assertThatFormula(query).isEquivalentTo(imgr.equal(k, i));
  }

  @Test
  public void testSolverIndependentQuantifierEliminationWithUltimateEliminatormkWithoutQuantifier()
      throws SolverException, InterruptedException {
    requireIntegers();
    requireArrays();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5);

    qmgr.setOption(ProverOptions.SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION_BEFORE);

    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula i = imgr.makeVariable("i");

    ArrayFormula<IntegerFormula, IntegerFormula> var =
        amgr.makeArray("arr", FormulaType.IntegerType, FormulaType.IntegerType);

    BooleanFormula query = qmgr.forall(var, imgr.equal(amgr.select(var, k), amgr.select(var, i)));

    assertThatFormula(query).isEquivalentTo(imgr.equal(k, i));
  }

  @Test
  public void testSolverIndependentQuantifierEliminationWithoutArraysBefore()
      throws SolverException, InterruptedException {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.YICES2);

    qmgr.setOption(ProverOptions.SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION_BEFORE);

    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula two = imgr.makeNumber(2);
    IntegerFormula five = imgr.makeNumber(5);

    BooleanFormula query =
        qmgr.forall(k, bmgr.or(imgr.lessOrEquals(k, five), imgr.greaterOrEquals(k, two)));

    assertThatFormula(query).isSatisfiable();
  }
}
