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
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.test.ultimate.UltimateEliminatorWrapper;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements QuantifiedFormulaManager {
  /*
  For parsing and dumping formula between UltimateEliminator and the native solver.
   */
  private Optional<AbstractFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>> fmgr;
  /*
  for logging warnings.
   */
  private final LogManager logger;

  private final UltimateEliminatorWrapper ultimateEliminatorWrapper;

  protected AbstractQuantifiedFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator, LogManager pLogger) {
    super(pCreator);
    ultimateEliminatorWrapper = new UltimateEliminatorWrapper(pLogger);
    logger = pLogger;
  }

  private BooleanFormula wrap(TFormulaInfo formulaInfo) {
    return getFormulaCreator().encapsulateBoolean(formulaInfo);
  }

  @Override
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException {
    return wrap(eliminateQuantifiers(extractInfo(pF)));
  }

  @Override
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF, QuantifierEliminationMethod pMethod)
      throws InterruptedException, SolverException {
    assert pMethod != null : "Quantifier elimination method cannot be null";
    switch (pMethod) {
      case ULTIMATE_ELIMINATOR:
        return handleUltimateEliminator(
            pF,
            Level.SEVERE,
            "UltimateEliminator failed. Please adjust the option if you want to use the native "
                + "quantifier elimination",
            false);

      case ULTIMATE_ELIMINATOR_FALLBACK_ON_FAILURE:
        return handleUltimateEliminator(pF, null, null, true);

      case ULTIMATE_ELIMINATOR_FALLBACK_WITH_WARNING_ON_FAILURE:
        return handleUltimateEliminator(
            pF,
            Level.WARNING,
            "UltimateEliminator failed. Reverting to native quantifier elimination",
            true);

      case NATIVE:
        return handleNativeElimination(
            pF,
            Level.SEVERE,
            "Native quantifier elimination failed. Please adjust the option if you want to use the"
                + " UltimateEliminator quantifier elimination",
            false);

      case NATIVE_FALLBACK_ON_FAILURE:
        return handleNativeElimination(pF, null, null, true);

      case NATIVE_FALLBACK_WITH_WARNING_ON_FAILURE:
        return handleNativeElimination(
            pF,
            Level.WARNING,
            "Default quantifier elimination failed. Switching to UltimateEliminator",
            true);

      default:
        break;
    }
    return pF;
  }

  protected TFormulaInfo eliminateQuantifiersUltimateEliminator(BooleanFormula pExtractInfo) {
    String form = dumpFormula(pExtractInfo);
    Term formula = ultimateEliminatorWrapper.parse(form);
    formula = ultimateEliminatorWrapper.simplify(formula);
    return extractInfo(parseFormula(ultimateEliminatorWrapper.dumpFormula(formula).toString()));
  }

  protected abstract TFormulaInfo eliminateQuantifiers(TFormulaInfo pExtractInfo)
      throws SolverException, InterruptedException;

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) {
    return wrap(
        mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
  }

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier q,
      List<? extends Formula> pVariables,
      BooleanFormula pBody,
      QuantifierCreationMethod pMethod) {
    switch (pMethod) {
      case ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION:
        try {
          return eliminateQuantifierBeforeMakingFormula(q, pVariables, pBody);
        } catch (UnsupportedOperationException e) {
          logger.logException(Level.WARNING, e, "External quantifier creation failed.");
          throw e;
        }

      case ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION_FALLBACK:
        try {
          return eliminateQuantifierBeforeMakingFormula(q, pVariables, pBody);
        } catch (UnsupportedOperationException e) {
          return wrap(
              mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
        }

      case ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION_FALLBACK_WARN_ON_FAILURE:
        try {
          return eliminateQuantifierBeforeMakingFormula(q, pVariables, pBody);
        } catch (UnsupportedOperationException e) {
          logger.logException(
              Level.WARNING, e, "External quantifier creation failed. Falling back to native");
          return wrap(
              mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
        }

      default:
        return wrap(
            mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
    }
  }

  public abstract TFormulaInfo mkQuantifier(
      Quantifier q, List<TFormulaInfo> vars, TFormulaInfo body);

  protected FormulaManager getFmgr() {
    return fmgr.orElseThrow();
  }

  protected void setFmgr(AbstractFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> pFmgr) {
    fmgr = Optional.of(pFmgr);
  }

  private BooleanFormula eliminateQuantifierBeforeMakingFormula(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) {
    List<String> boundVariablesNameList = new ArrayList<>();
    List<String> boundVariablesSortList = new ArrayList<>();

    String form = dumpFormula(pBody);
    Term ultimateBody = ultimateEliminatorWrapper.parse(form);
    for (Formula var : pVariables) {
      enrichBoundVariablesNameAndSortList(var, boundVariablesNameList, boundVariablesSortList);
    }
    String ultimateFormula =
        buildSmtlib2Formula(q, boundVariablesNameList, boundVariablesSortList, ultimateBody);

    Term parsedResult = ultimateEliminatorWrapper.parse(ultimateFormula);
    Term resultFormula = ultimateEliminatorWrapper.simplify(parsedResult);

    BooleanFormula result =
        parseFormula(ultimateEliminatorWrapper.dumpFormula(resultFormula).toString());
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

  private String buildSmtlib2Formula(
      Quantifier pQ,
      List<String> pBoundVariablesNameList,
      List<String> pBoundVariablesSortList,
      Term pUltimateBody) {
    StringBuilder sb = new StringBuilder();
    sb.append("(assert (").append(pQ.toString().toLowerCase(Locale.getDefault())).append(" (");
    if (!pBoundVariablesNameList.isEmpty()) {
      for (int i = 0; i < pBoundVariablesNameList.size(); i++) {
        sb.append("(")
            .append(pBoundVariablesNameList.get(i))
            .append(" ")
            .append(pBoundVariablesSortList.get(i))
            .append(")");
      }
    }
    sb.append(") ");
    sb.append(pUltimateBody);
    sb.append(" ))");
    return sb.toString();
  }

  private String getSortAsString(Formula pF) {
    if (fmgr.orElseThrow().getFormulaType(pF) instanceof FormulaType.ArrayFormulaType) {
      return "(" + fmgr.orElseThrow().getFormulaType(pF) + ")";
    } else {
      return fmgr.orElseThrow().getFormulaType(pF).toString();
    }
  }

  private void enrichBoundVariablesNameAndSortList(
      Formula pF, List<String> nameList, List<String> sortList) {
    try {
      formulaCreator.visit(
          pF,
          new DefaultFormulaVisitor<TraversalProcess>() {

            @Override
            protected TraversalProcess visitDefault(Formula f) {
              return TraversalProcess.CONTINUE;
            }

            @Override
            public TraversalProcess visitFreeVariable(Formula f, String name) {
              nameList.add(name);
              String sort = getSortAsString(f);
              sortList.add(mapTypeToUltimateSort(sort));
              return TraversalProcess.CONTINUE;
            }
          });
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  private BooleanFormula handleNativeElimination(
      BooleanFormula pF, Level logLevel, String logMessage, boolean fallback)
      throws SolverException, InterruptedException {
    try {
      return wrap(eliminateQuantifiers(extractInfo(pF)));
    } catch (SolverException | InterruptedException e) {
      if (logLevel != null) {
        logger.logException(logLevel, e, logMessage);
      }
      if (!fallback) {
        throw e;
      }
      return wrap(eliminateQuantifiersUltimateEliminator(pF));
    }
  }

  private BooleanFormula handleUltimateEliminator(
      BooleanFormula pF, Level logLevel, String logMessage, boolean fallback)
      throws SolverException, InterruptedException {
    try {
      return wrap(eliminateQuantifiersUltimateEliminator(pF));
    } catch (UnsupportedOperationException | IllegalArgumentException e) {
      if (logLevel != null && logMessage != null) {
        logger.logException(logLevel, e, logMessage);
      }
      if (!fallback) {
        throw e;
      }
      return wrap(eliminateQuantifiers(extractInfo(pF)));
    }
  }

  private BooleanFormula handleQuantifierCreation(
      Quantifier q,
      List<? extends Formula> pVariables,
      BooleanFormula pBody,
      Level logLevel,
      String logMessage,
      boolean fallback) {
    try {
      return eliminateQuantifierBeforeMakingFormula(q, pVariables, pBody);
    } catch (UnsupportedOperationException e) {
      if (logLevel != null && logMessage != null) {
        logger.logException(logLevel, e, logMessage);
      }
      if (!fallback) {
        throw e;
      }
      return wrap(
          mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
    }
  }

  protected String dumpFormula(BooleanFormula bf) {
    return fmgr.orElseThrow().dumpFormula(bf).toString();
  }

  protected BooleanFormula parseFormula(String pFormula) {
    return fmgr.orElseThrow().parse(pFormula);
  }
}
