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

  /**
   * Eliminates quantifiers using the UltimateEliminator.
   *
   * @param pExtractInfo The BooleanFormula to process.
   * @return The quantifier-free formula in the internal representation.
   */
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

  /**
   * Eliminates quantifiers before creating a formula.
   *
   * @param q The quantifier (e.g., FORALL or EXISTS).
   * @param pVariables The list of variables bound by the quantifier.
   * @param pBody The body of the formula.
   * @return A quantifier-free Boolean formula.
   */
  private BooleanFormula eliminateQuantifierBeforeMakingFormula(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) {
    List<String> boundVariablesNameList = new ArrayList<>();
    List<String> boundVariablesTypeList = new ArrayList<>();

    String form = dumpFormula(pBody);
    Term ultimateBody = ultimateEliminatorWrapper.parse(form);
    for (Formula var : pVariables) {
      enrichBoundVariablesNameAndTypeList(var, boundVariablesNameList, boundVariablesTypeList);
    }
    String ultimateFormula =
        buildSmtlib2Formula(q, boundVariablesNameList, boundVariablesTypeList, ultimateBody);

    Term parsedResult = ultimateEliminatorWrapper.parse(ultimateFormula);
    Term resultFormula = ultimateEliminatorWrapper.simplify(parsedResult);

    BooleanFormula result =
        parseFormula(ultimateEliminatorWrapper.dumpFormula(resultFormula).toString());
    return result;
  }

  /**
   * Maps a given type String to its corresponding Ultimate type representation.
   *
   * @param pType The type String to be mapped.
   * @return The Ultimate type-String representation of the type String.
   */
  private String mapTypeToUltimateType(String pType) {
    return pType
        .replace("<", " ")
        .replace(">", "")
        .replace(",", " ")
        .replace("Integer", "Int")
        .replace("Boolean", "Bool");
  }

  /**
   * Builds an SMT-LIB 2 formula string representation for a quantified formula.
   *
   * @param pQ The quantifier (e.g., FORALL or EXISTS).
   * @param pBoundVariablesNameList The list of bound variable names.
   * @param pBoundVariablesTypeList The list of bound variable types.
   * @param pUltimateBody The body of the formula as a Term (Ultimate datatype).
   * @return The SMT-LIB 2 string representation of the quantified formula.
   */
  private String buildSmtlib2Formula(
      Quantifier pQ,
      List<String> pBoundVariablesNameList,
      List<String> pBoundVariablesTypeList,
      Term pUltimateBody) {
    StringBuilder sb = new StringBuilder();
    sb.append("(assert (").append(pQ.toString().toLowerCase(Locale.getDefault())).append(" (");
    if (!pBoundVariablesNameList.isEmpty()) {
      for (int i = 0; i < pBoundVariablesNameList.size(); i++) {
        sb.append("(")
            .append(pBoundVariablesNameList.get(i))
            .append(" ")
            .append(pBoundVariablesTypeList.get(i))
            .append(")");
      }
    }
    sb.append(") ");
    sb.append(pUltimateBody);
    sb.append(" ))");
    return sb.toString();
  }

  /**
   * Retrieves the type of a given formula as a string.
   *
   * @param pF The formula whose type is to be retrieved.
   * @return The type of the formula as a string.
   */
  private String getTypeAsString(Formula pF) {
    if (fmgr.orElseThrow().getFormulaType(pF) instanceof FormulaType.ArrayFormulaType) {
      return "(" + fmgr.orElseThrow().getFormulaType(pF) + ")";
    } else {
      return fmgr.orElseThrow().getFormulaType(pF).toString();
    }
  }

  /**
   * Visit the given formula (of a bound variable) and fill the lists of bound variable names and
   * types with data gained.
   *
   * @param pF The formula to process.
   * @param nameList The list to store variable names.
   * @param typeList The list to store variable types.
   */
  private void enrichBoundVariablesNameAndTypeList(
      Formula pF, List<String> nameList, List<String> typeList) {
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
              String type = getTypeAsString(f);
              typeList.add(mapTypeToUltimateType(type));
              return TraversalProcess.CONTINUE;
            }
          });
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  /**
   * Handles quantifier elimination using the native solver.
   *
   * @param pF The BooleanFormula to process.
   * @param logLevel The logging level for errors.
   * @param logMessage The message to log in case of failure.
   * @param fallback Whether to fall back to UltimateEliminator on failure.
   * @return The quantifier-free formula.
   * @throws SolverException If the solver encounters an error.
   * @throws InterruptedException If the operation is interrupted.
   */
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

  /**
   * Handles quantifier elimination using UltimateEliminator.
   *
   * @param pF The BooleanFormula to process.
   * @param logLevel The logging level for errors.
   * @param logMessage The message to log in case of failure.
   * @param fallback Whether to fall back to the native solver on failure.
   * @return The quantifier-free formula.
   * @throws SolverException If the solver encounters an error.
   * @throws InterruptedException If the operation is interrupted.
   */
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

  /**
   * Handles the creation of a formula with quantifier, with optional fallback behavior.
   *
   * @param q The quantifier (e.g., FORALL or EXISTS).
   * @param pVariables The list of variables bound by the quantifier.
   * @param pBody The body of the formula.
   * @param logLevel The logging level for errors.
   * @param logMessage The message to log in case of failure.
   * @param fallback Whether to fall back to native quantifier creation on failure.
   * @return The created formula.
   */
  private BooleanFormula handleQuantifierFormulaCreation(
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
