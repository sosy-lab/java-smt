// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.collect.Lists;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
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
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.test.ultimate.UltimateEliminatorWrapper;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements QuantifiedFormulaManager {
  /*
  For activating UltimateEliminator with different setting e.g. warning and falling back to
  the native quantifier elimination or creation method in case of an error.
  */
  private final List<ProverOptions> options;
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
    options = new ArrayList<>();
  }

  private BooleanFormula wrap(TFormulaInfo formulaInfo) {
    return getFormulaCreator().encapsulateBoolean(formulaInfo);
  }

  @Override
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException {
    List<ProverOptions> proverOptions = extractQuantifierEliminationOptions();
    if (proverOptions.contains(ProverOptions.SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION)) {
      try {
        return wrap(eliminateQuantifiersUltimateEliminator(pF));
      } catch (UnsupportedOperationException | IllegalArgumentException e) {
        if (proverOptions.contains(ProverOptions.QUANTIFIER_ELIMINATION_FALLBACK_WARN_ON_FAILURE)) {
          logger.logException(
              Level.WARNING,
              e,
              "UltimateEliminator failed. " + "Reverting to native " + "quantifier elimination");
          return wrap(eliminateQuantifiers(extractInfo(pF)));
        }

        if (proverOptions.contains(ProverOptions.QUANTIFIER_ELIMINATION_FALLBACK)) {
          return wrap(eliminateQuantifiers(extractInfo(pF)));
        } else {
          logger.logException(
              Level.SEVERE,
              e,
              "UltimateEliminator failed. Please adjust the "
                  + "option if you want to use the native quantifier elimination");

          throw e;
        }
      }
    }

    try {
      return wrap(eliminateQuantifiers(extractInfo(pF)));
    } catch (Exception e1) {
      if (proverOptions.contains(ProverOptions.QUANTIFIER_ELIMINATION_FALLBACK_WARN_ON_FAILURE)) {
        logger.logException(
            Level.WARNING,
            e1,
            "Default quantifier elimination failed. Switching to UltimateEliminator");
        try {
          return wrap(eliminateQuantifiersUltimateEliminator(pF));
        } catch (Exception e2) {
          logger.logException(Level.SEVERE, e2, "UltimateEliminator also failed.");
          throw e2;
        }
      }

      if (proverOptions.contains(ProverOptions.QUANTIFIER_ELIMINATION_FALLBACK)) {
        try {
          return wrap(eliminateQuantifiersUltimateEliminator(pF));
        } catch (Exception e3) {
          logger.logException(Level.SEVERE, e3, "Quantifier elimination failed.");
          throw e3;
        }
      } else {
        logger.logException(
            Level.SEVERE,
            e1,
            "Native quantifier elimination failed. Please adjust the "
                + "option if you want to use the UltimateEliminator quantifier elimination");
        throw e1;
      }
    }
  }

  protected TFormulaInfo eliminateQuantifiersUltimateEliminator(BooleanFormula pExtractInfo) {
    FormulaManager formulaManager = fmgr.orElseThrow();
    Term formula =
        ultimateEliminatorWrapper.parse(formulaManager.dumpFormula(pExtractInfo).toString());
    formula = ultimateEliminatorWrapper.simplify(formula);
    return extractInfo(
        formulaManager.parse(ultimateEliminatorWrapper.dumpFormula(formula).toString()));
  }

  protected abstract TFormulaInfo eliminateQuantifiers(TFormulaInfo pExtractInfo)
      throws SolverException, InterruptedException;

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) throws IOException {
    List<ProverOptions> proverOptions = extractQuantifierEliminationOptions();
    if (proverOptions.contains(ProverOptions.EXTERNAL_QUANTIFIER_CREATION)) {
      try {
        return mkWithoutQuantifier(q, pVariables, pBody);
      } catch (IOException | UnsupportedOperationException e) {
        if (proverOptions.contains(
            ProverOptions.EXTERNAL_QUANTIFIER_CREATION_FALLBACK_WARN_ON_FAILURE)) {
          logger.logException(
              Level.WARNING, e, "External quantifier creation failed. Falling back to native");
          return wrap(
              mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
        } else if (proverOptions.contains(ProverOptions.EXTERNAL_QUANTIFIER_CREATION_FALLBACK)) {
          return wrap(
              mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
        } else {
          logger.logException(Level.WARNING, e, "External quantifier creation failed.");
          throw e;
        }
      }
    }
    return wrap(
        mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
  }

  public abstract TFormulaInfo mkQuantifier(
      Quantifier q, List<TFormulaInfo> vars, TFormulaInfo body);

  @Override
  public void setOptions(ProverOptions... opt) {
    options.addAll(Arrays.asList(opt));
  }

  public void setFmgr(AbstractFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> pFmgr) {
    fmgr = Optional.of(pFmgr);
  }

  private BooleanFormula mkWithoutQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) throws IOException {
    List<String> boundVariablesNameList = new ArrayList<>();
    List<String> boundVariablesSortList = new ArrayList<>();

    String form = fmgr.orElseThrow().dumpFormulaImpl(extractInfo(pBody));
    Term ultimateBody = ultimateEliminatorWrapper.parse(form);
    for (Formula var : pVariables) {
      enrichBoundVariablesNameAndSortList(var, boundVariablesNameList, boundVariablesSortList);
    }
    String ultimateFormula =
        buildSmtlib2Formula(q, boundVariablesNameList, boundVariablesSortList, ultimateBody);

    Term parsedResult = ultimateEliminatorWrapper.parse(ultimateFormula);
    Term resultFormula = ultimateEliminatorWrapper.simplify(parsedResult);

    BooleanFormula result =
        fmgr.orElseThrow().parse(ultimateEliminatorWrapper.dumpFormula(resultFormula).toString());
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

  private List<ProverOptions> extractQuantifierEliminationOptions() {
    List<ProverOptions> validOptions = new ArrayList<>();
    boolean fallback = false;
    boolean fallbackWarning = false;
    boolean externalCreationFallbackWarning = false;
    boolean externalCreationFallback = false;

    for (ProverOptions option : options) {
      switch (option) {
        case SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION:
          validOptions.add(option);
          break;
        case QUANTIFIER_ELIMINATION_FALLBACK:
          fallback = true;
          validOptions.add(option);
          break;
        case QUANTIFIER_ELIMINATION_FALLBACK_WARN_ON_FAILURE:
          fallbackWarning = true;
          validOptions.add(option);
          break;
        case EXTERNAL_QUANTIFIER_CREATION:
          validOptions.add(option);
          break;
        case EXTERNAL_QUANTIFIER_CREATION_FALLBACK:
          externalCreationFallback = true;
          validOptions.add(option);
          break;
        case EXTERNAL_QUANTIFIER_CREATION_FALLBACK_WARN_ON_FAILURE:
          externalCreationFallbackWarning = true;
          validOptions.add(option);
          break;
        default:
          break;
      }
    }

    checkArgument(
        !fallbackWarning || !fallback,
        "Incompatible options: "
            + "QUANTIFIER_ELIMINATION_FALLBACK and "
            + "QUANTIFIER_ELIMINATION_FALLBACK_WITHOUT_WARNING cannot be used together.");

    checkArgument(
        !externalCreationFallbackWarning || !externalCreationFallback,
        "Incompatible options: "
            + "EXTERNAL_QUANTIFIER_CREATION_FALLBACK_WARN_ON_FAILURE and "
            + "EXTERNAL_QUANTIFIER_CREATION_FALLBACK_WARN_ON_FAILURE cannot be used together.");

    return validOptions;
  }
}
