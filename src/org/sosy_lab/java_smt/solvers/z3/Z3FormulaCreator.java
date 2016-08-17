/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;
import com.google.common.collect.Table;
import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_ast_kind;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_sort_kind;
import com.microsoft.z3.enumerations.Z3_symbol_kind;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3ArrayFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3BitvectorFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3BooleanFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3FloatingPointFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3IntegerFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3RationalFormula;
import org.sosy_lab.java_smt.visitors.FormulaVisitor;

import java.lang.ref.PhantomReference;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

@Options(prefix = "solver.z3")
class Z3FormulaCreator extends FormulaCreator<Long, Long, Long, Long> {

  private static final Map<Integer, Object> Z3_CONSTANTS =
      ImmutableMap.<Integer, Object>builder()
          .put(Z3_decl_kind.Z3_OP_TRUE.toInt(), true)
          .put(Z3_decl_kind.Z3_OP_FALSE.toInt(), false)
          .put(Z3_decl_kind.Z3_OP_FPA_PLUS_ZERO.toInt(), +0.0)
          .put(Z3_decl_kind.Z3_OP_FPA_MINUS_ZERO.toInt(), -0.0)
          .put(Z3_decl_kind.Z3_OP_FPA_PLUS_INF.toInt(), Double.POSITIVE_INFINITY)
          .put(Z3_decl_kind.Z3_OP_FPA_MINUS_INF.toInt(), Double.NEGATIVE_INFINITY)
          .put(Z3_decl_kind.Z3_OP_FPA_NAN.toInt(), Double.NaN)
          .build();

  // Set of error messages that might occur if Z3 is interrupted.
  private static final ImmutableSet<String> Z3_INTERRUPT_ERRORS =
      ImmutableSet.of(
          "canceled",
          // These occur on interrupts during interpolation
          "interpolation cannot proceed without a model", // cf. Z3 commit 654780b
          "Proof error!");

  @Option(secure = true, description = "Whether to use PhantomReferences for discarding Z3 AST")
  private boolean usePhantomReferences = false;

  private final Table<Long, Long, Long> allocatedArraySorts = HashBasedTable.create();

  /**
   * Automatic clean-up of Z3 ASTs.
   */
  private final ReferenceQueue<Z3Formula> referenceQueue = new ReferenceQueue<>();
  private final Map<PhantomReference<? extends Z3Formula>, Long> referenceMap =
      Maps.newIdentityHashMap();

  // todo: getters for statistic.
  private final Timer cleanupTimer = new Timer();
  protected final ShutdownNotifier shutdownNotifier;

  Z3FormulaCreator(
      long pEnv,
      long pBoolType,
      long pIntegerType,
      long pRealType,
      Configuration config,
      ShutdownNotifier pShutdownNotifier)
      throws InvalidConfigurationException {
    super(pEnv, pBoolType, pIntegerType, pRealType);
    shutdownNotifier = pShutdownNotifier;
    config.inject(this);
  }

  final Z3Exception handleZ3Exception(Z3Exception e) throws Z3Exception, InterruptedException {
    if (Z3_INTERRUPT_ERRORS.contains(e.getMessage())) {
      shutdownNotifier.shutdownIfNecessary();
    }
    throw e;
  }

  @Override
  public Long makeVariable(Long type, String varName) {
    long z3context = getEnv();
    long symbol = Native.mkStringSymbol(z3context, varName);
    return Native.mkConst(z3context, symbol, type);
  }

  @Override
  public Long extractInfo(Formula pT) {
    return Z3FormulaManager.getZ3Expr(pT);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    Long term = extractInfo(pFormula);
    return (FormulaType<T>) getFormulaType(term);
  }

  public FormulaType<?> getFormulaTypeFromSort(Long pSort) {
    long z3context = getEnv();
    Z3_sort_kind sortKind = Z3_sort_kind.fromInt(Native.getSortKind(z3context, pSort));
    switch (sortKind) {
      case Z3_BOOL_SORT:
        return FormulaType.BooleanType;
      case Z3_INT_SORT:
        return FormulaType.IntegerType;
      case Z3_REAL_SORT:
        return FormulaType.RationalType;
      case Z3_BV_SORT:
        return FormulaType.getBitvectorTypeWithSize(Native.getBvSortSize(z3context, pSort));
      case Z3_ARRAY_SORT:
        long domainSort = Native.getArraySortDomain(z3context, pSort);
        long rangeSort = Native.getArraySortRange(z3context, pSort);
        return FormulaType.getArrayType(
            getFormulaTypeFromSort(domainSort), getFormulaTypeFromSort(rangeSort));
      case Z3_FLOATING_POINT_SORT:
        return FormulaType.getFloatingPointType(
            Native.fpaGetEbits(z3context, pSort), Native.fpaGetSbits(z3context, pSort));
      case Z3_ROUNDING_MODE_SORT:
        return FormulaType.FloatingPointRoundingModeType;
      case Z3_DATATYPE_SORT:
      case Z3_RELATION_SORT:
      case Z3_FINITE_DOMAIN_SORT:
      case Z3_SEQ_SORT:
      case Z3_RE_SORT:
      case Z3_UNKNOWN_SORT:
      case Z3_UNINTERPRETED_SORT:
        // TODO: support for remaining sorts.
        throw new IllegalArgumentException(
            "Unknown formula type "
                + Native.sortToString(z3context, pSort)
                + " with sort "
                + sortKind);
      default:
        throw new UnsupportedOperationException("Unexpected state.");
    }
  }

  @Override
  public FormulaType<?> getFormulaType(Long pFormula) {
    long sort = Native.getSort(getEnv(), pFormula);
    return getFormulaTypeFromSort(sort);
  }

  @Override
  protected <TD extends Formula, TR extends Formula> FormulaType<TR> getArrayFormulaElementType(
      ArrayFormula<TD, TR> pArray) {
    return ((Z3ArrayFormula<TD, TR>) pArray).getElementType();
  }

  @Override
  protected <TD extends Formula, TR extends Formula> FormulaType<TD> getArrayFormulaIndexType(
      ArrayFormula<TD, TR> pArray) {
    return ((Z3ArrayFormula<TD, TR>) pArray).getIndexType();
  }

  @Override
  protected <TD extends Formula, TR extends Formula> ArrayFormula<TD, TR> encapsulateArray(
      Long pTerm, FormulaType<TD> pIndexType, FormulaType<TR> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType));
    cleanupReferences();
    return storePhantomReference(
        new Z3ArrayFormula<>(getEnv(), pTerm, pIndexType, pElementType), pTerm);
  }

  private <T extends Z3Formula> T storePhantomReference(T out, Long pTerm) {
    if (usePhantomReferences) {
      PhantomReference<T> ref = new PhantomReference<>(out, referenceQueue);
      referenceMap.put(ref, pTerm);
    }
    return out;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Long pTerm) {
    assert pType.equals(getFormulaType(pTerm))
            || (pType.equals(FormulaType.RationalType)
                && getFormulaType(pTerm).equals(FormulaType.IntegerType))
        : String.format(
            "Trying to encapsulate formula of type %s as %s", getFormulaType(pTerm), pType);
    cleanupReferences();
    if (pType.isBooleanType()) {
      return (T) storePhantomReference(new Z3BooleanFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isIntegerType()) {
      return (T) storePhantomReference(new Z3IntegerFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isRationalType()) {
      return (T) storePhantomReference(new Z3RationalFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isBitvectorType()) {
      return (T) storePhantomReference(new Z3BitvectorFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isFloatingPointType()) {
      return (T) storePhantomReference(new Z3FloatingPointFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isFloatingPointRoundingModeType()) {
      return (T)
          storePhantomReference(new Z3FloatingPointRoundingModeFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T)
          storePhantomReference(
              new Z3ArrayFormula<>(getEnv(), pTerm, arrFt.getIndexType(), arrFt.getElementType()),
              pTerm);
    }

    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in Z3");
  }

  @Override
  public BooleanFormula encapsulateBoolean(Long pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    cleanupReferences();
    return storePhantomReference(new Z3BooleanFormula(getEnv(), pTerm), pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Long pTerm) {
    assert getFormulaType(pTerm).isBitvectorType();
    cleanupReferences();
    return storePhantomReference(new Z3BitvectorFormula(getEnv(), pTerm), pTerm);
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Long pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType();
    cleanupReferences();
    return storePhantomReference(new Z3FloatingPointFormula(getEnv(), pTerm), pTerm);
  }

  @Override
  public Long getArrayType(Long pIndexType, Long pElementType) {
    Long allocatedArraySort = allocatedArraySorts.get(pIndexType, pElementType);
    if (allocatedArraySort == null) {
      allocatedArraySort = Native.mkArraySort(getEnv(), pIndexType, pElementType);
      Native.incRef(getEnv(), allocatedArraySort);
      allocatedArraySorts.put(pIndexType, pElementType, allocatedArraySort);
    }
    return allocatedArraySort;
  }

  @Override
  public Long getBitvectorType(int pBitwidth) {
    checkArgument(pBitwidth > 0, "Cannot use bitvector type with size %s", pBitwidth);
    long bvSort = Native.mkBvSort(getEnv(), pBitwidth);
    Native.incRef(getEnv(), Native.sortToAst(getEnv(), bvSort));
    return bvSort;
  }

  @Override
  public Long getFloatingPointType(FormulaType.FloatingPointType type) {
    long fpSort = Native.mkFpaSort(getEnv(), type.getExponentSize(), type.getMantissaSize());
    Native.incRef(getEnv(), Native.sortToAst(getEnv(), fpSort));
    return fpSort;
  }

  private void cleanupReferences() {
    if (!usePhantomReferences) {
      return;
    }
    cleanupTimer.start();
    try {
      Reference<? extends Z3Formula> ref;
      while ((ref = referenceQueue.poll()) != null) {
        long z3ast = referenceMap.remove(ref);
        Native.decRef(environment, z3ast);
      }
    } finally {
      cleanupTimer.stop();
    }
  }

  private String getAppName(long f) {
    long funcDecl = Native.getAppDecl(environment, f);
    long symbol = Native.getDeclName(environment, funcDecl);
    return symbolToString(symbol);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Formula formula, final Long f) {
    switch (Z3_ast_kind.fromInt(Native.getAstKind(environment, f))) {
      case Z3_NUMERAL_AST:
        return visitor.visitConstant(formula, convertValue(f));
      case Z3_APP_AST:
        int arity = Native.getAppNumArgs(environment, f);

        if (arity == 0) {

          // constants
          int declKind = Native.getDeclKind(environment, Native.getAppDecl(environment, f));
          Object value = Z3_CONSTANTS.get(declKind);
          if (value != null) {
            return visitor.visitConstant(formula, value);

          } else if (declKind == Z3_decl_kind.Z3_OP_FPA_NUM.toInt()
              || Native.getSortKind(environment, Native.getSort(environment, f))
                  == Z3_sort_kind.Z3_ROUNDING_MODE_SORT.toInt()) {
            return visitor.visitConstant(formula, convertValue(f));

          } else {

            // Has to be a variable otherwise.
            // TODO: assert that.
            return visitor.visitFreeVariable(formula, getAppName(f));
          }
        }

        ImmutableList.Builder<Formula> args = ImmutableList.builder();
        ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();
        for (int i = 0; i < arity; i++) {
          long arg = Native.getAppArg(environment, f, i);
          FormulaType<?> argumentType = getFormulaType(arg);
          args.add(encapsulate(argumentType, arg));
          argTypes.add(argumentType);
        }
        return visitor.visitFunction(
            formula,
            args.build(),
            FunctionDeclarationImpl.of(
                getAppName(f),
                getDeclarationKind(f),
                argTypes.build(),
                getFormulaType(f),
                Native.getAppDecl(environment, f)));
      case Z3_VAR_AST:
        int deBruijnIdx = Native.getIndexValue(environment, f);
        return visitor.visitBoundVariable(formula, deBruijnIdx);
      case Z3_QUANTIFIER_AST:
        BooleanFormula body = encapsulateBoolean(Native.getQuantifierBody(environment, f));
        Quantifier q =
            Native.isQuantifierForall(environment, f) ? Quantifier.FORALL : Quantifier.EXISTS;
        return visitor.visitQuantifier((BooleanFormula) formula, q, getBoundVars(f), body);

      case Z3_SORT_AST:
      case Z3_FUNC_DECL_AST:
      case Z3_UNKNOWN_AST:
      default:
        throw new UnsupportedOperationException(
            "Input should be a formula AST, " + "got unexpected type instead");
    }
  }

  protected String symbolToString(long symbol) {
    switch (Z3_symbol_kind.fromInt(Native.getSymbolKind(environment, symbol))) {
      case Z3_STRING_SYMBOL:
        return Native.getSymbolString(environment, symbol);
      case Z3_INT_SYMBOL:

        // Bound variable.
        return "#" + Native.getSymbolInt(environment, symbol);
      default:
        throw new UnsupportedOperationException("Unexpected state");
    }
  }

  private List<Formula> getBoundVars(long f) {
    int numBound = Native.getQuantifierNumBound(environment, f);
    List<Formula> boundVars = new ArrayList<>(numBound);
    for (int i = 0; i < numBound; i++) {
      long varName = Native.getQuantifierBoundName(environment, f, i);
      long varSort = Native.getQuantifierBoundSort(environment, f, i);
      boundVars.add(
          encapsulate(
              getFormulaTypeFromSort(varSort), Native.mkConst(environment, varName, varSort)));
    }
    return boundVars;
  }

  private FunctionDeclarationKind getDeclarationKind(long f) {
    assert Native.getArity(environment, Native.getAppDecl(environment, f)) > 0
        : "Variables should be handled in other branch.";
    if (getAppName(f).equals("div0")) {
      // Z3 segfaults in getDeclKind for this term (cf. https://github.com/Z3Prover/z3/issues/669)
      return FunctionDeclarationKind.OTHER;
    }
    Z3_decl_kind decl =
        Z3_decl_kind.fromInt(Native.getDeclKind(environment, Native.getAppDecl(environment, f)));
    switch (decl) {
      case Z3_OP_AND:
        return FunctionDeclarationKind.AND;
      case Z3_OP_NOT:
        return FunctionDeclarationKind.NOT;
      case Z3_OP_OR:
        return FunctionDeclarationKind.OR;
      case Z3_OP_IFF:
        return FunctionDeclarationKind.IFF;
      case Z3_OP_ITE:
        return FunctionDeclarationKind.ITE;
      case Z3_OP_XOR:
        return FunctionDeclarationKind.XOR;
      case Z3_OP_DISTINCT:
        return FunctionDeclarationKind.DISTINCT;
      case Z3_OP_IMPLIES:
        return FunctionDeclarationKind.IMPLIES;

      case Z3_OP_SUB:
        return FunctionDeclarationKind.SUB;
      case Z3_OP_ADD:
        return FunctionDeclarationKind.ADD;
      case Z3_OP_DIV:
        return FunctionDeclarationKind.DIV;
      case Z3_OP_MUL:
        return FunctionDeclarationKind.MUL;
      case Z3_OP_MOD:
        return FunctionDeclarationKind.MODULO;

      case Z3_OP_UNINTERPRETED:
        return FunctionDeclarationKind.UF;

      case Z3_OP_LT:
        return FunctionDeclarationKind.LT;
      case Z3_OP_LE:
        return FunctionDeclarationKind.LTE;
      case Z3_OP_GT:
        return FunctionDeclarationKind.GT;
      case Z3_OP_GE:
        return FunctionDeclarationKind.GTE;
      case Z3_OP_EQ:
        return FunctionDeclarationKind.EQ;

      case Z3_OP_STORE:
        return FunctionDeclarationKind.STORE;
      case Z3_OP_SELECT:
        return FunctionDeclarationKind.SELECT;

      case Z3_OP_TRUE:
      case Z3_OP_FALSE:
      case Z3_OP_ANUM:
      case Z3_OP_AGNUM:
        throw new UnsupportedOperationException("Unexpected state: constants not expected");
      case Z3_OP_OEQ:
        throw new UnsupportedOperationException("Unexpected state: not a proof");
      case Z3_OP_INTERP:
        // TODO: should we treat those separately?
        throw new UnsupportedOperationException("Unexpected state: interpolant marks not expected");
      case Z3_OP_UMINUS:
        return FunctionDeclarationKind.UMINUS;
      case Z3_OP_IDIV:

        // TODO: different handling for integer division?
        return FunctionDeclarationKind.DIV;
      default:
        return FunctionDeclarationKind.OTHER;
    }
  }

  /**
   * @param value Z3_ast
   * @return Whether the value is a constant and can be passed to {@link #convertValue(long)}.
   */
  public boolean isConstant(long value) {
    return Native.isNumeralAst(environment, value)
        || Native.isAlgebraicNumber(environment, value)
        || isOP(environment, value, Z3_decl_kind.Z3_OP_TRUE.toInt())
        || isOP(environment, value, Z3_decl_kind.Z3_OP_FALSE.toInt());
  }

  /**
   * @param value Z3_ast representing a *value*.
   * @return BigInteger|Double|Rational.
   */
  public Object convertValue(long value) {
    assert isConstant(value) : "value is not constant";
    Native.incRef(environment, value);

    Object constantValue =
        Z3_CONSTANTS.get(Native.getDeclKind(environment, Native.getAppDecl(environment, value)));
    if (constantValue != null) {
      return constantValue;
    }

    try {
      FormulaType<?> type = getFormulaType(value);
      if (type.isBooleanType()) {
        return isOP(environment, value, Z3_decl_kind.Z3_OP_TRUE.toInt());
      } else if (type.isIntegerType()) {
        return new BigInteger(Native.getNumeralString(environment, value));
      } else if (type.isRationalType()) {
        return Rational.ofString(Native.getNumeralString(environment, value));
      } else if (type.isBitvectorType()) {
        return new BigInteger(Native.getNumeralString(environment, value));
      } else if (type.isFloatingPointType()) {
        // Converting to Rational and reading that is easier.
        return convertValue(Native.simplify(environment, Native.mkFpaToReal(environment, value)));

      } else {

        // Unknown type --- return string serialization.
        return Native.astToString(environment, value);
      }

    } finally {
      Native.decRef(environment, value);
    }
  }

  @Override
  public Long callFunctionImpl(FunctionDeclarationImpl<?, Long> declaration, List<Long> args) {
    return Native.mkApp(
        environment, declaration.getSolverDeclaration(), args.size(), Longs.toArray(args));
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Long pLong) {
    return Native.getAppDecl(getEnv(), pLong);
  }

  /** returns, if the function of the expression is the given operation. */
  static boolean isOP(long z3context, long expr, int op) {
    if (!Native.isApp(z3context, expr)) {
      return false;
    }

    long decl = Native.getAppDecl(z3context, expr);
    return Native.getDeclKind(z3context, decl) == op;
  }

  /**
   * Apply multiple tactics in sequence.
   * @throws InterruptedException thrown by JNI code in case of termination request
   * @throws SolverException thrown by JNI code in case of error
   */
  public long applyTactics(long z3context, final Long pF, String... pTactics)
      throws InterruptedException, SolverException {
    long overallResult = pF;
    for (String tactic : pTactics) {
      long tacticResult = applyTactic(z3context, overallResult, tactic);
      if (overallResult != pF) {
        Native.decRef(z3context, overallResult);
      }
      overallResult = tacticResult;
    }
    return overallResult;
  }

  /**
   * Apply tactic on a Z3_ast object, convert the result back to Z3_ast.
   *
   * @param z3context Z3_context
   * @param tactic Z3 Tactic Name
   * @param pF Z3_ast
   * @return Z3_ast
   *
   * @throws InterruptedException If execution gets interrupted.
   */
  public long applyTactic(long z3context, long pF, String tactic) throws InterruptedException {
    long tacticObject = Native.mkTactic(z3context, tactic);
    Native.tacticIncRef(z3context, tacticObject);

    long goal = Native.mkGoal(z3context, true, false, false);
    Native.goalIncRef(z3context, goal);
    Native.goalAssert(z3context, goal, pF);

    long result;
    try {
      result = Native.tacticApply(z3context, tacticObject, goal);
    } catch (Z3Exception exp) {
      throw handleZ3Exception(exp);
    }
    Native.applyResultIncRef(z3context, result);

    try {
      return applyResultToAST(z3context, result);
    } finally {
      Native.applyResultDecRef(z3context, result);
      Native.goalDecRef(z3context, goal);
      Native.tacticDecRef(z3context, tacticObject);
    }
  }

  private long applyResultToAST(long z3context, long applyResult) {
    int subgoalsCount = Native.applyResultGetNumSubgoals(z3context, applyResult);
    long[] goalFormulas = new long[subgoalsCount];

    for (int i = 0; i < subgoalsCount; i++) {
      long subgoal = Native.applyResultGetSubgoal(z3context, applyResult, i);
      Native.goalIncRef(z3context, subgoal);
      long subgoalAst = goalToAST(z3context, subgoal);
      Native.incRef(z3context, subgoalAst);
      goalFormulas[i] = subgoalAst;
      Native.goalDecRef(z3context, subgoal);
    }
    try {
      return goalFormulas.length == 1
          ? goalFormulas[0]
          : Native.mkOr(z3context, goalFormulas.length, goalFormulas);
    } finally {
      for (int i = 0; i < subgoalsCount; i++) {
        Native.decRef(z3context, goalFormulas[i]);
      }
    }
  }

  private long goalToAST(long z3context, long goal) {
    int subgoalFormulasCount = Native.goalSize(z3context, goal);
    long[] subgoalFormulas = new long[subgoalFormulasCount];
    for (int k = 0; k < subgoalFormulasCount; k++) {
      long f = Native.goalFormula(z3context, goal, k);
      Native.incRef(z3context, f);
      subgoalFormulas[k] = f;
    }
    try {
      return subgoalFormulas.length == 1
          ? subgoalFormulas[0]
          : Native.mkAnd(z3context, subgoalFormulas.length, subgoalFormulas);
    } finally {
      for (int k = 0; k < subgoalFormulasCount; k++) {
        Native.decRef(z3context, subgoalFormulas[k]);
      }
    }
  }

  /**
   * Closing the context.
   */
  public void forceClose() {
    cleanupReferences();

    // Force clean all ASTs, even those which were not GC'd yet.
    for (long ast : referenceMap.values()) {
      Native.decRef(getEnv(), ast);
    }
  }
}
