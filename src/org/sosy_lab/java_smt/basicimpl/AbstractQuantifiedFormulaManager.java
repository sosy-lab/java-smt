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
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
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
  private Optional<AbstractFormulaManager> fmgr;

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
      TFormulaInfo pExtractInfo, ProverOptions pOptions)
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
    if (option != null
        && option.equals(ProverOptions.SOLVER_INDEPENDENT_QUANTIFIER_ELIMINATION_BEFORE)) {
      try {
        return mkWithoutQuantifier(
            q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody));
      } catch (IOException e) {
        System.out.println(
            "Independent quantifier elimination via Ultimate before formula creation " + "failed.");
      }
    }
    return wrap(
        mkQuantifier(q, Lists.transform(pVariables, this::extractInfo), extractInfo(pBody)));
  }

  public abstract TFormulaInfo mkQuantifier(
      Quantifier q, List<TFormulaInfo> vars, TFormulaInfo body);

  private BooleanFormula mkWithoutQuantifier(
      Quantifier pQ, List<TFormulaInfo> pVariables, TFormulaInfo pBody) throws IOException {
    int quantifier;
    if (pQ == Quantifier.EXISTS) {
      quantifier = Script.EXISTS;
    } else {
      quantifier = Script.FORALL;
    }

    String form = fmgr.get().dumpFormulaImpl(pBody);
    Term ultimateBody = getUltimateEliminatorWrapper().parse(form);
    List<TermVariable> boundVars = new ArrayList<>();

    for (TFormulaInfo var : pVariables) {
      String dumpedVar = fmgr.get().dumpFormulaImpl(var);
      Term ultimateVar = getUltimateEliminatorWrapper().parse(dumpedVar);
      Sort varType = ultimateVar.getSort();
      String varName = ((ApplicationTerm) ultimateVar).getFunction().getName();
      TermVariable tv =
          getUltimateEliminatorWrapper().getUltimateEliminator().variable(varName, varType);
      boundVars.add(tv);
    }
    Term quantifiedFormula =
        getUltimateEliminatorWrapper()
            .getUltimateEliminator()
            .quantifier(
                quantifier, boundVars.toArray(new TermVariable[0]), ultimateBody, (Term[]) null);

    Term resultFormula = getUltimateEliminatorWrapper().simplify(quantifiedFormula);
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

  public void setFmgr(AbstractFormulaManager pFmgr) {
    fmgr = Optional.of(pFmgr);
  }
}
