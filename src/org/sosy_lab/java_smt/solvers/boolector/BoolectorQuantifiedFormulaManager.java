// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.collect.ImmutableList;
import com.google.common.primitives.Longs;
import java.util.List;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BoolectorQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Long, Long, Long, Long> {

  private final long btor;

  BoolectorQuantifiedFormulaManager(FormulaCreator<Long, Long, Long, Long> pCreator,
                                    LogManager pLogger) {
    super(pCreator, pLogger);
    btor = getFormulaCreator().getEnv();
  }

  @Override
  protected Long eliminateQuantifiers(Long pExtractInfo)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Boolector can not eliminate quantifier.");
  }

  /**
   * Note: Boolector only supports bitvector quantifier! The vars used MUST be boolector_param (not
   * boolector_var)! Therefore, we have to change every var into param with the visitor!
   * Additionally, no param may be used twice (Boolector will end if you do!).
   */
  // TODO with the comment above, the user has no way to call boolector_param.
  //      This implementation seems to be broken and not usable.
  @Override
  public Long mkQuantifier(Quantifier pQ, List<Long> pVars, Long pBody) {
    checkArgument(!pVars.isEmpty(), "List of quantified variables can not be empty");
    for (long param : pVars) {
      checkArgument(
          BtorJNI.boolector_is_param(btor, param),
          "pVariables need to be parameter nodes in boolector.");
    }
    final long newQuantifier;
    final long[] varsArray = Longs.toArray(pVars);
    if (pQ == Quantifier.FORALL) {
      newQuantifier = BtorJNI.boolector_forall(btor, varsArray, varsArray.length, pBody);
    } else {
      newQuantifier = BtorJNI.boolector_exists(btor, varsArray, varsArray.length, pBody);
    }
    return newQuantifier;
  }

  @Override
  public BooleanFormula mkWithoutQuantifier(Quantifier pQ, List<Long> pVariables, Long pBody) {
    throw new UnsupportedOperationException();
  }

  static class QuantifiedFormula {
    private final boolean isForall; // false for EXISTS, true for FORALL
    private final long body;
    private final ImmutableList<Long> boundVariables;

    QuantifiedFormula(boolean pIsForall, long pBody, List<Long> pVars) {
      isForall = pIsForall;
      body = pBody;
      boundVariables = ImmutableList.copyOf(pVars);
    }

    public boolean isForall() {
      return isForall;
    }

    public long getBody() {
      return body;
    }

    public ImmutableList<Long> getBoundVariables() {
      return boundVariables;
    }
  }
}
