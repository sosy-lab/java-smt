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
import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.logging.Level;
import javax.annotation.Nonnull;
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
  private ProverOptions[] options;
  private Optional<AbstractFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>> fmgr;
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
  public BooleanFormula eliminateQuantifiers(@Nonnull BooleanFormula pF)
      throws InterruptedException, SolverException, IOException {
    if (options != null
        && Arrays.asList(options)
            .contains(ProverOptions.SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION)) {
      try {
        return wrap(eliminateQuantifiersUltimateEliminator(pF));
      } catch (UnsupportedOperationException | IOException | IllegalArgumentException e) {
        if (Arrays.asList(options).contains(ProverOptions.QUANTIFIER_ELIMINATION_FALLBACK)) {
          logger.logException(
              Level.WARNING,
              e,
              "UltimateEliminator failed. " + "Reverting to native " + "quantifier elimination");
          return wrap(eliminateQuantifiers(extractInfo(pF)));
        }

        if (Arrays.asList(options)
            .contains(ProverOptions.QUANTIFIER_ELIMINATION_FALLBACK_WITHOUT_WARNING)) {
          return wrap(eliminateQuantifiers(extractInfo(pF)));
        } else {
          logger.logException(
              Level.SEVERE,
              e,
              "UltimateEliminator failed. Please adjust the "
                  + "option if you want to use the native quantifier elimination");

          throw e; // TODO is this the correct way to abort?
        }
      }
    }

    try {
      return wrap(eliminateQuantifiers(extractInfo(pF)));
    } catch (Exception e) {
      if (Arrays.asList(options).contains(ProverOptions.QUANTIFIER_ELIMINATION_FALLBACK)) {
        logger.logException(
            Level.WARNING,
            e,
            "Default quantifier elimination failed. Switching to UltimateEliminator");
        try {
          return wrap(eliminateQuantifiersUltimateEliminator(pF));
        } catch (IOException pE) {
          logger.logException(Level.SEVERE, e, "UltimateEliminator also failed.");
          throw pE; // TODO is this the correct way to abort?
        }
      }

      if (Arrays.asList(options)
          .contains(ProverOptions.QUANTIFIER_ELIMINATION_FALLBACK_WITHOUT_WARNING)) {
        try {
          return wrap(eliminateQuantifiersUltimateEliminator(pF));
        } catch (IOException pE) {
          logger.logException(Level.SEVERE, e, "Quantifier elimination failed.");
          throw e; // TODO is this the correct way to abort?
        }
      } else {
        logger.logException(
            Level.SEVERE,
            e,
            "Native quantifier elimination failed. Please adjust the "
                + "option if you want to use the UltimateEliminator quantifier elimination");
        throw e; // TODO is this the correct way to abort?
      }
    }
  }

  protected TFormulaInfo eliminateQuantifiersUltimateEliminator(BooleanFormula pExtractInfo)
      throws UnsupportedOperationException, IOException {
    FormulaManager formulaManager = getFormulaManager();
    Term formula =
        getUltimateEliminatorWrapper().parse(formulaManager.dumpFormula(pExtractInfo).toString());
    formula = getUltimateEliminatorWrapper().simplify(formula);
    return extractInfo(
        formulaManager.parse(getUltimateEliminatorWrapper().dumpFormula(formula).toString()));
  }

  protected abstract TFormulaInfo eliminateQuantifiers(TFormulaInfo pExtractInfo)
      throws SolverException, InterruptedException;

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) {
    if (options != null
        && Arrays.asList(options)
            .contains(ProverOptions.SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION_BEFORE)) {
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
  public ProverOptions[] getOptions() {
    return options;
  }

  @Override
  public void setOptions(ProverOptions... opt) {
    options = opt;
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
              String sort;
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
