// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.solvers.smtinterpol.UltimateEliminatorParser;

class Z3QuantifiedFormulaManager extends AbstractQuantifiedFormulaManager<Long, Long, Long, Long> {

  private final long z3context;
  private final Z3FormulaCreator z3FormulaCreator;

  private Optional<Z3FormulaManager> fmgr;

  Z3QuantifiedFormulaManager(Z3FormulaCreator creator,
                             LogManager pLogger) {
    super(creator, pLogger);
    this.z3context = creator.getEnv();
    z3FormulaCreator = creator;
    fmgr = Optional.empty();
  }

  @Override
  public Long mkQuantifier(Quantifier q, List<Long> pVariables, Long pBody) {
    checkArgument(!pVariables.isEmpty(), "List of quantified variables can not be empty");
    return Native.mkQuantifierConst(
        z3context,
        q == Quantifier.FORALL,
        0,
        pVariables.size(),
        Longs.toArray(pVariables),
        0,
        new long[0],
        pBody);
  }

  @Override
  public BooleanFormula mkWithoutQuantifier(Quantifier pQ, List<Long> pVariables, Long pBody) {
    throw new UnsupportedOperationException();
  }

  @Override
  protected Long eliminateQuantifiers(Long pExtractInfo)
      throws SolverException, InterruptedException {
    // It is recommended (personal communication with Nikolaj Bjorner)
    // to run "qe-light" before "qe".
    // "qe" does not perform a "qe-light" as a preprocessing on its own!

    // One might want to run the tactic "ctx-solver-simplify" on the result.

    return z3FormulaCreator.applyTactics(z3context, pExtractInfo, "qe-light", "qe");
  }

  @Override
  protected Long eliminateQuantifiersUltimateEliminator(Long pExtractInfo)
      throws UnsupportedOperationException {
    Z3FormulaManager formulaManager = fmgr.get();
    Term formula =
        getUltimateEliminatorWrapper().parse(
            formulaManager.dumpFormulaImpl(pExtractInfo));
    formula = getUltimateEliminatorWrapper().simplify(formula);
    Long result =
        formulaManager.parseImpl(UltimateEliminatorParser.dumpFormula(formula).toString());
    return result;
  }

  public void setFormulaManager(Z3FormulaManager pFmgr) {
    fmgr = Optional.of(pFmgr);
  }
}
