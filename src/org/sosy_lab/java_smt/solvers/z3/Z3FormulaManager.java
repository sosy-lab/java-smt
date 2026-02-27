// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class Z3FormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

  private final Z3FormulaCreator formulaCreator;

  @SuppressWarnings("checkstyle:parameternumber")
  Z3FormulaManager(
      Z3FormulaCreator pFormulaCreator,
      Z3UFManager pFunctionManager,
      Z3BooleanFormulaManager pBooleanManager,
      Z3IntegerFormulaManager pIntegerManager,
      Z3RationalFormulaManager pRationalManager,
      Z3BitvectorFormulaManager pBitpreciseManager,
      Z3FloatingPointFormulaManager pFloatingPointManager,
      Z3QuantifiedFormulaManager pQuantifiedManager,
      Z3ArrayFormulaManager pArrayManager,
      Z3StringFormulaManager pStringManager,
      Z3EnumerationFormulaManager pEnumerationManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitpreciseManager,
        pFloatingPointManager,
        pQuantifiedManager,
        pArrayManager,
        null,
        pStringManager,
        pEnumerationManager);
    formulaCreator = pFormulaCreator;
  }

  @Override
  public Long equalImpl(Long pArg1, Long pArgs) {
    // We need to add a phantom reference here, otherwise Z3 will hang
    // TODO Remove this hack
    var term = Native.mkEq(getEnvironment(), pArg1, pArgs);
    Native.incRef(getEnvironment(), term);
    return term;
  }

  @Override
  public Long distinctImpl(Iterable<Long> pArgs) {
    long[] array = Longs.toArray(ImmutableList.copyOf(pArgs));
    if (array.length < 2) {
      return Native.mkTrue(getEnvironment());
    } else {
      return Native.mkDistinct(getEnvironment(), array.length, array);
    }
  }

  @Override
  protected List<Long> parseAllImpl(String pSmtScript) throws IllegalArgumentException {

    // Z3 does not access the existing symbols on its own,
    // but requires all symbols as part of the query.
    // Thus, we track the used symbols on our own and give them to the parser call, if required.
    // Later, we collect all symbols from the parsed query and
    // define them again to have them tracked.

    final long env = getEnvironment();

    // JavaSMT does currently not allow defining new sorts, future work?
    long[] sortSymbols = new long[0];
    long[] sorts = new long[0];

    // first step: lets try to parse the query directly, without additional information
    List<Long> declSymbols = new ArrayList<>();
    List<Long> decls = new ArrayList<>();

    long parsedAssertionsAsVector = 0;
    boolean finished = false;
    while (!finished) {
      try {
        parsedAssertionsAsVector =
            Native.parseSmtlib2String(
                env,
                pSmtScript,
                sorts.length,
                sortSymbols,
                sorts,
                declSymbols.size(),
                Longs.toArray(declSymbols),
                Longs.toArray(decls));
        finished = true;

      } catch (Z3Exception nested) {
        // get the missing symbol and restart the parsing with them
        Pattern pattern =
            Pattern.compile(
                "\\(error \"line \\d+ column \\d+: unknown constant"
                    + " (?<name>.*?)\\s?(?<sorts>\\(.*\\))?\\s?\\\"\\)\\n");
        Matcher matcher = pattern.matcher(nested.getMessage());
        if (matcher.matches()) {
          String missingSymbol = matcher.group(1);
          Long appDecl = formulaCreator.getKnownDeclaration(missingSymbol);
          if (appDecl != null) { // if the symbol is known, then use it
            declSymbols.add(Native.mkStringSymbol(env, missingSymbol));
            decls.add(appDecl);
            continue; // restart the parsing
          }
        }
        throw new IllegalArgumentException(nested);
      }
    }

    Preconditions.checkState(parsedAssertionsAsVector != 0, "parsing aborted");
    final int size = Native.astVectorSize(env, parsedAssertionsAsVector);
    ImmutableList.Builder<Long> result = ImmutableList.builder();
    for (int i = 0; i < size; i++) {
      long term = Native.astVectorGet(env, parsedAssertionsAsVector, i);
      // last step: all parsed symbols need to be declared again to have them tracked in the
      // creator.
      declareAllSymbols(term);
      result.add(term);
    }

    return result.build();
  }

  @SuppressWarnings("CheckReturnValue")
  private void declareAllSymbols(final long term) {
    final long env = getEnvironment();
    final Map<String, Long> symbols = formulaCreator.extractVariablesAndUFs(term, true);
    for (Map.Entry<String, Long> symbol : symbols.entrySet()) {
      long sym = symbol.getValue();
      String name = symbol.getKey();
      assert Native.isApp(env, sym);
      int arity = Native.getAppNumArgs(env, sym);
      if (arity == 0) { // constants
        formulaCreator.makeVariable(Native.getSort(env, sym), name);
      } else {
        ImmutableList.Builder<Long> argTypes = ImmutableList.builder();
        for (int j = 0; j < arity; j++) {
          argTypes.add(Native.getSort(env, Native.getAppArg(env, sym, j)));
        }
        formulaCreator.declareUFImpl(name, Native.getSort(env, sym), argTypes.build());
      }
    }
  }

  @Override
  protected BooleanFormula applyQELightImpl(BooleanFormula pF)
      throws InterruptedException, SolverException {
    return applyTacticImpl(pF, "qe-light");
  }

  @Override
  protected BooleanFormula applyCNFImpl(BooleanFormula pF)
      throws InterruptedException, SolverException {
    return applyTacticImpl(pF, "tseitin-cnf");
  }

  @Override
  protected BooleanFormula applyNNFImpl(BooleanFormula pF)
      throws InterruptedException, SolverException {
    return applyTacticImpl(pF, "nnf");
  }

  private BooleanFormula applyTacticImpl(BooleanFormula pF, String tacticName)
      throws InterruptedException, SolverException {
    long out =
        formulaCreator.applyTactic(getFormulaCreator().getEnv(), extractInfo(pF), tacticName);
    return formulaCreator.encapsulateBoolean(out);
  }

  @Override
  public String dumpFormulaImpl(final Long expr) {
    assert getFormulaCreator().getFormulaType(expr) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    // Serializing a solver is the simplest way to dump a formula in Z3,
    // cf https://github.com/Z3Prover/z3/issues/397
    long z3solver = Native.mkSolver(getEnvironment());
    Native.solverIncRef(getEnvironment(), z3solver);
    Native.solverAssert(getEnvironment(), z3solver, expr);
    String serialized = Native.solverToString(getEnvironment(), z3solver);
    Native.solverDecRef(getEnvironment(), z3solver);
    return serialized;
  }

  @Override
  protected Long simplify(Long pF) throws InterruptedException {
    try {
      try {
        return Native.simplify(getFormulaCreator().getEnv(), pF);
      } catch (Z3Exception exp) {
        throw formulaCreator.handleZ3Exception(exp);
      }
    } catch (SolverException e) {
      // ignore exception and return original formula AS-IS.
      return pF;
    }
  }

  @Override
  public <T extends Formula> T substitute(
      final T f, final Map<? extends Formula, ? extends Formula> fromToMapping) {
    long[] changeFrom = new long[fromToMapping.size()];
    long[] changeTo = new long[fromToMapping.size()];
    int idx = 0;
    for (Map.Entry<? extends Formula, ? extends Formula> e : fromToMapping.entrySet()) {
      changeFrom[idx] = extractInfo(e.getKey());
      changeTo[idx] = extractInfo(e.getValue());
      idx++;
    }
    FormulaType<T> type = getFormulaType(f);
    return getFormulaCreator()
        .encapsulate(
            type,
            Native.substitute(
                getFormulaCreator().getEnv(),
                extractInfo(f),
                fromToMapping.size(),
                changeFrom,
                changeTo));
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula other, FormulaManager otherManager) {
    if (otherManager instanceof Z3FormulaManager) {
      long otherZ3Context = ((Z3FormulaManager) otherManager).getEnvironment();
      if (otherZ3Context == getEnvironment()) {

        // Same context.
        return other;
      } else {

        // Z3-to-Z3 translation.
        long translatedAST = Native.translate(otherZ3Context, extractInfo(other), getEnvironment());
        return getFormulaCreator().encapsulateBoolean(translatedAST);
      }
    }
    return super.translateFrom(other, otherManager);
  }
}
