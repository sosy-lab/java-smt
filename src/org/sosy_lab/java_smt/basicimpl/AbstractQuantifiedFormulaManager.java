// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.Lists;
import java.io.IOException;
import java.util.List;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.test.ultimate.UltimateEliminatorWrapper;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements QuantifiedFormulaManager {
  private ProverOptions option;


  private final UltimateEliminatorWrapper ultimateEliminatorWrapper;


  protected AbstractQuantifiedFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator,
      LogManager pLogger) {
    super(pCreator);
    ultimateEliminatorWrapper = new UltimateEliminatorWrapper(pLogger);
  }

  private BooleanFormula wrap(TFormulaInfo formulaInfo) {
    return getFormulaCreator().encapsulateBoolean(formulaInfo);
  }

  @Override
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException, UnsupportedOperationException {
    if (option != null && option.equals(ProverOptions.SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION)) {
      try {
        return wrap(eliminateQuantifiersUltimateEliminator(extractInfo(pF), option));
      } catch (UnsupportedOperationException e) {
        System.out.println(
            "Solver does not support parsing yet. Falling back to native "
                + "quantifier elimination.");
        return wrap(eliminateQuantifiers(extractInfo(pF)));
      } catch (IOException e) {
        System.out.println(
            "Independent quantifier elimination via Ultimate failed. Falling back to native "
                + "quantifier elimination.");
        return wrap(eliminateQuantifiers(extractInfo(pF)));
      }
    }
    return wrap(eliminateQuantifiers(extractInfo(pF)));
  }

  protected TFormulaInfo eliminateQuantifiersUltimateEliminator(
      TFormulaInfo pExtractInfo,
      ProverOptions pOptions)
      throws UnsupportedOperationException, IOException {
    throw new UnsupportedOperationException();
  }

  protected TFormulaInfo eliminateQuantifiersUltimateEliminator(TFormulaInfo pExtractInfo)
      throws UnsupportedOperationException, IOException {
    throw new UnsupportedOperationException();
  }

  protected abstract TFormulaInfo eliminateQuantifiers(TFormulaInfo pExtractInfo)
      throws SolverException, InterruptedException;

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) {
    if (option != null && option.equals(ProverOptions
        .SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION_BEFORE)) {
      return mkWithoutQuantifier(q, Lists.transform(pVariables, this::extractInfo),
          extractInfo(pBody));
    }
    return wrap(
        mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
  }

  public abstract TFormulaInfo mkQuantifier(
      Quantifier q, List<TFormulaInfo> vars, TFormulaInfo body);


  public abstract BooleanFormula mkWithoutQuantifier(
      Quantifier pQ,
      List<TFormulaInfo> pVariables,
      TFormulaInfo pBody);


  @Override
  public ProverOptions getOption() {
    return option;
  }

  @Override
  public void setOption(ProverOptions opt) {
    option = opt;
  }

  public UltimateEliminatorWrapper getUltimateEliminatorWrapper() {
    return ultimateEliminatorWrapper;
  }
}
