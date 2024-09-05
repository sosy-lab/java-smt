/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableSetCopy;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import java.util.Collection;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractInterpolatingProver<F> extends AbstractProverWithAllSat<F>
    implements InterpolatingProverEnvironment<F> {

  private final FormulaCreator<F, ?, ?, ?> creator;
  private final QuantifiedFormulaManager qfmgr;
  private final BooleanFormulaManager bmgr;
  private final InterpolatingProverEnvironment<F> prover;

  protected AbstractInterpolatingProver(
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier,
      FormulaCreator<F, ?, ?, ?> pCreator,
      QuantifiedFormulaManager pQfmgr,
      InterpolatingProverEnvironment<F> pProver) {
    super(pOptions, pBmgr, pShutdownNotifier);
    bmgr = pBmgr;
    creator = pCreator;
    qfmgr = pQfmgr;
    prover = pProver;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<F> pFormulasOfA)
      throws SolverException, InterruptedException {
    return getModelBasedInterpolant(pFormulasOfA);
  }

  /**
   * As = free_arith_vars(A)
   * Bs = free_arith_vars(B)
   *
   * shared = [s for s in As & Bs ]
   *
   * Itp = z3.Function('Itp', [s.sort() for s in shared] + [z3.BoolSort()])
   * left = z3.ForAll([a for a in As], z3.Implies(A, Itp(shared)))
   * right = z3.ForAll([b for b in Bs], z3.Implies(Itp(shared), z3.Not(B)))
   *
   * res, answer = solve_horn([left, right])
   *
   * if res == z3.sat:
   *    return answer.eval(Itp(shared))
   * return None
   */
  private BooleanFormula getModelBasedInterpolant(Collection<F> pFormulasOfA)
      throws SolverException, InterruptedException {
    checkState(!closed);
    checkArgument(getAssertedConstraintIds().containsAll(pFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    // free arithmetic variables a and b
    final Set<F> assertedFormulas = transformedImmutableSetCopy(getAssertedFormulas(),
        creator::extractInfo);
    final Set<F> a = ImmutableSet.copyOf(pFormulasOfA);
    final Set<F> b = Sets.difference(assertedFormulas, a);

    // shared variables between a and b
    final Set<F> shared = Sets.intersection(a, b); // nur formeln, brauche aber variablen ->
    // extractVariables...
    // visitor -> formula creator

    // itp(shared) => callFunction (ausfuehren der itp), declare
    // schau in tests: ufmanagertest
    // F in BooleanFOrmula umwandeln kann fehlschlagen
    // instanceOF herausfinden welchen Typ, getBitvectortype

    // siehe code

    // abstrakte implementierungen: floatingpointformulaimpl, ... -> manager bzw. formula
    // (interface implementierungen anschauen wie z.B. EMmurationFOrmula, numeralformula, ...)

    // bekomme dann eine Booleanformula itp(shared)

    prover.push();

    // itp(shared)
    BooleanFormula itp = prover.getInterpolant(shared);

    // a und b nicht casten, sondern liste separat als bmgr.and() formel und das Ergebnis fuer
    // ein neues bmgr.and()

    // left: A /\ NOT I
    // z3.ForAll([a for a in As], z3.Implies(A, Itp(shared)))
    // BooleanFormula left = qfmgr.forall((List<? extends Formula>) a, (bmgr.and(a, bmgr.not(itp)
    // )));

    // right: I /\ B
    // z3.ForAll([b for b in Bs], z3.Implies(Itp(shared), z3.Not(B)))
    // BooleanFormula right = qfmgr.forall((List<? extends Formula>) b, (bmgr.and(itp, b)));

    boolean result = prover.isUnsat();
    if (!result) {
      // BooleanFormula answer = prover.getModel().evaluate(itp); // ??? isUnsat should be false?
      // return prover.getInterpolant((Collection<F>) itp);
      // else { false } // makefalse in BOoleanFOrmulamanager
    }

    prover.pop(); // ??? hier stack wieder aufbauen

    // return answer;
    return null;
  }
}
