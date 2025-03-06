// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.Lists;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.test.ultimate.UltimateEliminatorWrapper;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements QuantifiedFormulaManager {
  private ProverOptions option;
  private Optional<AbstractFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>> fmgr;

  private final UltimateEliminatorWrapper ultimateEliminatorWrapper;

  protected AbstractQuantifiedFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator, LogManager pLogger) {
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
        System.out.println("Eliminating quantifiers via UltimateEliminator.");
        return wrap(eliminateQuantifiersUltimateEliminator(extractInfo(pF)));
      } catch (UnsupportedOperationException e) {
        System.out.println(
            "Solver does not support eliminating via UltimateEliminator yet. Falling back to "
                + "native "
                + "quantifier elimination.");
        return wrap(eliminateQuantifiers(extractInfo(pF)));
      } catch (IOException e) {
        System.out.println(
            "Independent quantifier elimination via UltimateEliminator failed. Falling back to "
                + "native "
                + "quantifier elimination.");
        return wrap(eliminateQuantifiers(extractInfo(pF)));
      }
    }
    return wrap(eliminateQuantifiers(extractInfo(pF)));
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
    if (option != null
        && option.equals(ProverOptions.SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION_BEFORE)) {
      try {
        System.out.println(
            "Eliminating quantifiers via UltimateEliminator before formula creation.");
        return mkWithoutQuantifier(
            q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody));
      } catch (IOException e) {
        System.out.println(
            "Independent quantifier elimination via UltimateEliminator before formula creation "
                + "failed.");
      }
    }
    return wrap(
        mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
  }

  public abstract TFormulaInfo mkQuantifier(
      Quantifier q, List<TFormulaInfo> vars, TFormulaInfo body);

  private BooleanFormula mkWithoutQuantifier(
      Quantifier pQ, List<TFormulaInfo> pVariables, TFormulaInfo pBody) throws IOException {
    String form = fmgr.get().dumpFormulaImpl(pBody);
    Term ultimateBody = getUltimateEliminatorWrapper().parse(form);
    List<String> nameList = new ArrayList<>();
    List<Sort> sortList = new ArrayList<>();

    for (TFormulaInfo var : pVariables) {
      String dumpedVar = fmgr.get().dumpFormulaImpl(var);
      Term ultimateVar = getUltimateEliminatorWrapper().parse(dumpedVar);
      Sort varType = ultimateVar.getSort();
      String varName = ((ApplicationTerm) ultimateVar).getFunction().getName();
      if (varName != null && varType != null) {
        sortList.add(varType);
        nameList.add(varName);
      }
    }
    String ultimateFormula = buildUltimateEliminatorFormula(pQ, nameList, sortList, ultimateBody);

    Term parsedResult = getUltimateEliminatorWrapper().parse(ultimateFormula);
    Term resultFormula = getUltimateEliminatorWrapper().simplify(parsedResult);

    BooleanFormula result =
        fmgr.get().parse(getUltimateEliminatorWrapper().dumpFormula(resultFormula).toString());
    return result;
  }

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

  public FormulaManager getFormulaManager() {
    if (fmgr.isEmpty()) {
      throw new RuntimeException("FormulaManager is not set");
    }
    return fmgr.get();
  }

  public void setFmgr(AbstractFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> pFmgr) {
    fmgr = Optional.of(pFmgr);
  }

  private String buildUltimateEliminatorFormula(
      Quantifier pQ, List<String> pNameList, List<Sort> pSortList, Term pUltimateBody) {
    StringBuilder sb = new StringBuilder();
    sb.append("(assert (").append(pQ.toString().toLowerCase(Locale.getDefault())).append(" (");
    if (!pNameList.isEmpty()) {
      for (int i = 0; i < pNameList.size(); i++) {
        sb.append("(").append(pNameList.get(i)).append(" ").append(pSortList.get(i)).append(")");
      }
    }
    sb.append(") ");
    sb.append(pUltimateBody);
    sb.append(" ))");
    return sb.toString();
  }
}
