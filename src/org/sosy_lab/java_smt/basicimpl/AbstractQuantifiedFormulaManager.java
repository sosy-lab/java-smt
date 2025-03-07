// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.Lists;
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
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
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
        return wrap(eliminateQuantifiersUltimateEliminator(extractInfo(pF)));
      } catch (UnsupportedOperationException | IOException e) {
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
        return mkWithoutQuantifier(q, pVariables, pBody);
      } catch (IOException e) {
        return wrap(
            mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
      }
    }
    return wrap(
        mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
  }

  public abstract TFormulaInfo mkQuantifier(
      Quantifier q, List<TFormulaInfo> vars, TFormulaInfo body);

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

  private BooleanFormula mkWithoutQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) throws IOException {
    List<String> nameList = new ArrayList<>();
    List<String> sortList = new ArrayList<>();

    String form = fmgr.get().dumpFormulaImpl(extractInfo(pBody));
    Term ultimateBody = getUltimateEliminatorWrapper().parse(form);
    for (Formula var : pVariables) {
      formulaCreator.visit(
          var,
          new DefaultFormulaVisitor<>() {
            @Override
            protected TraversalProcess visitDefault(Formula f) {
              return TraversalProcess.CONTINUE;
            }

            @Override
            public TraversalProcess visitFreeVariable(Formula f, String name) {
              nameList.add(name);
              String sort = "";
              if (fmgr.get().getFormulaType(f).toString().contains("Array")) {
                sort = "(" + fmgr.get().getFormulaType(f) + ")";
              } else {
                sort = fmgr.get().getFormulaType(f).toString();
              }
              sortList.add(mapTypeToUltimateSort(sort));
              return TraversalProcess.CONTINUE;
            }
          });
    }
    String ultimateFormula = buildUltimateEliminatorFormula(q, nameList, sortList, ultimateBody);

    Term parsedResult = getUltimateEliminatorWrapper().parse(ultimateFormula);
    Term resultFormula = getUltimateEliminatorWrapper().simplify(parsedResult);

    BooleanFormula result =
        fmgr.get().parse(getUltimateEliminatorWrapper().dumpFormula(resultFormula).toString());
    return result;
  }

  private String mapTypeToUltimateSort(String pSort) {
    return pSort
        .replace("<", " ")
        .replace(">", "")
        .replace(",", " ")
        .replace("Integer", "Int")
        .replace("Boolean", "Bool");
  }

  private String buildUltimateEliminatorFormula(
      Quantifier pQ, List<String> pNameList, List<String> pSortList, Term pUltimateBody) {
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
