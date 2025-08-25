// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Table;
import com.google.common.primitives.Longs;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_ast_kind;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_sort_kind;
import com.microsoft.z3.enumerations.Z3_symbol_kind;
import java.lang.ref.PhantomReference;
import java.lang.ref.ReferenceQueue;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
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
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3ArrayFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3BitvectorFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3BooleanFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3EnumerationFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3FloatingPointFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3IntegerFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3RationalFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3RegexFormula;
import org.sosy_lab.java_smt.solvers.z3.Z3Formula.Z3StringFormula;

@Options(prefix = "solver.z3")
class Z3FormulaCreator extends FormulaCreator<Long, Long, Long, Long> {

  private static final ImmutableMap<Integer, Object> Z3_CONSTANTS =
      ImmutableMap.<Integer, Object>builder()
          .put(Z3_decl_kind.Z3_OP_TRUE.toInt(), true)
          .put(Z3_decl_kind.Z3_OP_FALSE.toInt(), false)
          .put(
              Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN.toInt(),
              FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN)
          .put(
              Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY.toInt(),
              FloatingPointRoundingMode.NEAREST_TIES_AWAY)
          .put(
              Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_POSITIVE.toInt(),
              FloatingPointRoundingMode.TOWARD_POSITIVE)
          .put(
              Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_NEGATIVE.toInt(),
              FloatingPointRoundingMode.TOWARD_NEGATIVE)
          .put(Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_ZERO.toInt(), FloatingPointRoundingMode.TOWARD_ZERO)
          .buildOrThrow();

  private static final ImmutableSet<Integer> Z3_FP_CONSTANTS =
      ImmutableSet.of(
          Z3_decl_kind.Z3_OP_FPA_PLUS_ZERO.toInt(),
          Z3_decl_kind.Z3_OP_FPA_MINUS_ZERO.toInt(),
          Z3_decl_kind.Z3_OP_FPA_PLUS_INF.toInt(),
          Z3_decl_kind.Z3_OP_FPA_MINUS_INF.toInt(),
          Z3_decl_kind.Z3_OP_FPA_NAN.toInt());

  // Set of error messages that might occur if Z3 is interrupted.
  private static final ImmutableSet<String> Z3_INTERRUPT_ERRORS =
      ImmutableSet.of(
          "canceled", // Z3::src/util/common_msgs.cpp
          "push canceled", // src/smt/smt_context.cpp
          "interrupted from keyboard", // Z3: src/solver/check_sat_result.cpp
          "Proof error!",
          "interrupted", // Z3::src/solver/check_sat_result.cpp
          "maximization suspended" // Z3::src/opt/opt_solver.cpp
          );

  @Option(secure = true, description = "Whether to use PhantomReferences for discarding Z3 AST")
  private boolean usePhantomReferences = false;

  /**
   * We need to track all created symbols for parsing.
   *
   * <p>This map stores symbols (names) and their declaration (type information).
   */
  private final Map<String, Long> symbolsToDeclarations = new LinkedHashMap<>();

  private final Table<Long, Long, Long> allocatedArraySorts = HashBasedTable.create();

  /** Automatic clean-up of Z3 ASTs. */
  private final ReferenceQueue<Z3Formula> referenceQueue = new ReferenceQueue<>();

  private final Z3AstReference referenceListHead;

  // todo: getters for statistic.
  private final Timer cleanupTimer = new Timer();
  protected final ShutdownNotifier shutdownNotifier;

  @SuppressWarnings("ParameterNumber")
  Z3FormulaCreator(
      long pEnv,
      long pBoolType,
      long pIntegerType,
      long pRealType,
      long pStringType,
      long pRegexType,
      Configuration config,
      ShutdownNotifier pShutdownNotifier)
      throws InvalidConfigurationException {
    super(pEnv, pBoolType, pIntegerType, pRealType, pStringType, pRegexType);
    shutdownNotifier = pShutdownNotifier;
    config.inject(this);

    if (usePhantomReferences) {
      // Setup sentinel nodes for doubly-linked phantom reference list.
      Z3AstReference head = new Z3AstReference();
      Z3AstReference tail = new Z3AstReference();
      head.next = tail;
      tail.prev = head;
      referenceListHead = head;
    } else {
      referenceListHead = null;
    }
  }

  /**
   * This method throws an {@link InterruptedException} if Z3 was interrupted by a shutdown hook.
   * Otherwise, the given exception is wrapped and thrown as a SolverException.
   */
  @CanIgnoreReturnValue
  final SolverException handleZ3Exception(Z3Exception e)
      throws SolverException, InterruptedException {
    if (Z3_INTERRUPT_ERRORS.contains(e.getMessage())) {
      shutdownNotifier.shutdownIfNecessary();
    }
    throw new SolverException("Z3 has thrown an exception", e);
  }

  /**
   * This method handles a Z3Exception, however it only throws a RuntimeException. This method is
   * used in places where we cannot throw a checked exception in JavaSMT due to API restrictions.
   *
   * @param e the Z3Exception to handle
   * @return nothing, always throw a RuntimeException
   * @throws RuntimeException always thrown for the given Z3Exception
   */
  final RuntimeException handleZ3ExceptionAsRuntimeException(Z3Exception e) {
    try {
      throw handleZ3Exception(e);
    } catch (InterruptedException ex) {
      Thread.currentThread().interrupt();
      throw sneakyThrow(e);
    } catch (SolverException ex) {
      throw sneakyThrow(e);
    }
  }

  @SuppressWarnings("unchecked")
  private static <E extends Throwable> RuntimeException sneakyThrow(Throwable e) throws E {
    throw (E) e;
  }

  @Override
  public Long makeVariable(Long type, String varName) {
    long z3context = getEnv();
    long symbol = Native.mkStringSymbol(z3context, varName);
    long var = Native.mkConst(z3context, symbol, type);
    Native.incRef(z3context, var);
    symbolsToDeclarations.put(varName, Native.getAppDecl(z3context, var));
    return var;
  }

  @Override
  public Long extractInfo(Formula pT) {
    if (pT instanceof Z3Formula) {
      return ((Z3Formula) pT).getFormulaInfo();
    }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + " in the Solver!");
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
            Native.fpaGetEbits(z3context, pSort), Native.fpaGetSbits(z3context, pSort) - 1);
      case Z3_ROUNDING_MODE_SORT:
        return FormulaType.FloatingPointRoundingModeType;
      case Z3_RE_SORT:
        return FormulaType.RegexType;
      case Z3_DATATYPE_SORT:
        int n = Native.getDatatypeSortNumConstructors(z3context, pSort);
        ImmutableSet.Builder<String> elements = ImmutableSet.builder();
        for (int i = 0; i < n; i++) {
          long decl = Native.getDatatypeSortConstructor(z3context, pSort, i);
          elements.add(symbolToString(Native.getDeclName(z3context, decl)));
        }
        return FormulaType.getEnumerationType(
            Native.sortToString(z3context, pSort), elements.build());
      case Z3_RELATION_SORT:
      case Z3_FINITE_DOMAIN_SORT:
      case Z3_SEQ_SORT:
      case Z3_UNKNOWN_SORT:
      case Z3_UNINTERPRETED_SORT:
        if (Native.isStringSort(z3context, pSort)) {
          return FormulaType.StringType;
        } else {
          // TODO: support for remaining sorts.
          throw new IllegalArgumentException(
              "Unknown formula type "
                  + Native.sortToString(z3context, pSort)
                  + " with sort "
                  + sortKind);
        }
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
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> FormulaType<TR> getArrayFormulaElementType(
      ArrayFormula<TD, TR> pArray) {
    return ((Z3ArrayFormula<TD, TR>) pArray).getElementType();
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> FormulaType<TD> getArrayFormulaIndexType(
      ArrayFormula<TD, TR> pArray) {
    return ((Z3ArrayFormula<TD, TR>) pArray).getIndexType();
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> ArrayFormula<TD, TR> encapsulateArray(
      Long pTerm, FormulaType<TD> pIndexType, FormulaType<TR> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType));
    cleanupReferences();
    return storePhantomReference(
        new Z3ArrayFormula<>(getEnv(), pTerm, pIndexType, pElementType), pTerm);
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
    } else if (pType.isStringType()) {
      return (T) storePhantomReference(new Z3StringFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isRegexType()) {
      return (T) storePhantomReference(new Z3RegexFormula(getEnv(), pTerm), pTerm);
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
    } else if (pType.isEnumerationType()) {
      return (T) storePhantomReference(new Z3EnumerationFormula(getEnv(), pTerm), pTerm);
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
  protected StringFormula encapsulateString(Long pTerm) {
    assert getFormulaType(pTerm).isStringType()
        : String.format(
            "Term %s has unexpected type %s.",
            Native.astToString(getEnv(), pTerm),
            Native.sortToString(getEnv(), Native.getSort(getEnv(), pTerm)));
    cleanupReferences();
    return storePhantomReference(new Z3StringFormula(getEnv(), pTerm), pTerm);
  }

  @Override
  protected RegexFormula encapsulateRegex(Long pTerm) {
    assert getFormulaType(pTerm).isRegexType()
        : String.format(
            "Term %s has unexpected type %s.",
            Native.astToString(getEnv(), pTerm),
            Native.sortToString(getEnv(), Native.getSort(getEnv(), pTerm)));
    cleanupReferences();
    return storePhantomReference(new Z3RegexFormula(getEnv(), pTerm), pTerm);
  }

  @Override
  protected EnumerationFormula encapsulateEnumeration(Long pTerm) {
    assert getFormulaType(pTerm).isEnumerationType()
        : String.format(
            "Term %s has unexpected type %s.",
            Native.astToString(getEnv(), pTerm),
            Native.sortToString(getEnv(), Native.getSort(getEnv(), pTerm)));
    cleanupReferences();
    return storePhantomReference(new Z3EnumerationFormula(getEnv(), pTerm), pTerm);
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
    long fpSort = Native.mkFpaSort(getEnv(), type.getExponentSize(), type.getMantissaSize() + 1);
    Native.incRef(getEnv(), Native.sortToAst(getEnv(), fpSort));
    return fpSort;
  }

  private static final class Z3AstReference extends PhantomReference<Z3Formula> {
    private final long z3Ast;
    private @Nullable Z3AstReference prev;
    private @Nullable Z3AstReference next;

    // To generate dummy head and tail nodes
    private Z3AstReference() {
      this(null, null, 0);
    }

    private Z3AstReference(Z3Formula referent, ReferenceQueue<? super Z3Formula> q, long z3Ast) {
      super(referent, q);
      this.z3Ast = z3Ast;
    }

    private void insert(Z3AstReference ref) {
      assert next != null;
      ref.prev = this;
      ref.next = this.next;
      ref.next.prev = ref;
      this.next = ref;
    }

    private void cleanup(long environment) {
      Native.decRef(environment, z3Ast);
      assert (prev != null && next != null);
      prev.next = next;
      next.prev = prev;
    }
  }

  private <T extends Z3Formula> T storePhantomReference(T out, long pTerm) {
    if (usePhantomReferences) {
      referenceListHead.insert(new Z3AstReference(out, referenceQueue, pTerm));
    }
    return out;
  }

  private void cleanupReferences() {
    if (!usePhantomReferences) {
      return;
    }
    cleanupTimer.start();
    try {
      Z3AstReference ref;
      while ((ref = (Z3AstReference) referenceQueue.poll()) != null) {
        ref.cleanup(environment);
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

  @SuppressWarnings("deprecation")
  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Formula formula, final Long f) {
    switch (Z3_ast_kind.fromInt(Native.getAstKind(environment, f))) {
      case Z3_NUMERAL_AST:
        return visitor.visitConstant(formula, convertValue(f));
      case Z3_APP_AST:
        int arity = Native.getAppNumArgs(environment, f);
        int declKind = Native.getDeclKind(environment, Native.getAppDecl(environment, f));

        if (arity == 0) {
          // constants
          Object value = Z3_CONSTANTS.get(declKind);
          if (value != null) {
            return visitor.visitConstant(formula, value);

          } else if (Z3_FP_CONSTANTS.contains(declKind)) {
            return visitor.visitConstant(formula, convertValue(f));

            // Rounding mode
          } else if (declKind == Z3_decl_kind.Z3_OP_FPA_NUM.toInt()
              || Native.getSortKind(environment, Native.getSort(environment, f))
                  == Z3_sort_kind.Z3_ROUNDING_MODE_SORT.toInt()) {
            return visitor.visitConstant(formula, convertValue(f));

            // string constant
          } else if (declKind == Z3_decl_kind.Z3_OP_INTERNAL.toInt()
              && Native.getSortKind(environment, Native.getSort(environment, f))
                  == Z3_sort_kind.Z3_SEQ_SORT.toInt()) {
            return visitor.visitConstant(formula, convertValue(f));

            // Free variable
          } else if (declKind == Z3_decl_kind.Z3_OP_UNINTERPRETED.toInt()
              || declKind == Z3_decl_kind.Z3_OP_INTERNAL.toInt()) {
            return visitor.visitFreeVariable(formula, getAppName(f));

            // enumeration constant
          } else if (declKind == Z3_decl_kind.Z3_OP_DT_CONSTRUCTOR.toInt()) {
            return visitor.visitConstant(formula, convertValue(f));
          } // else: fall-through with a function application

        } else if (arity == 3) {

          // FP from BV
          if (declKind == Z3_decl_kind.Z3_OP_FPA_FP.toInt()) {
            final var signBv = Native.getAppArg(environment, f, 0);
            final var expoBv = Native.getAppArg(environment, f, 1);
            final var mantBv = Native.getAppArg(environment, f, 2);
            if (isConstant(signBv) && isConstant(expoBv) && isConstant(mantBv)) {
              return visitor.visitConstant(formula, convertValue(f));
            }
          }
        }

        // Function application with zero or more parameters
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
        return visitQuantifier(visitor, (BooleanFormula) formula, f);
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

  private <R> R visitQuantifier(FormulaVisitor<R> pVisitor, BooleanFormula pFormula, Long pF) {
    int numBound = Native.getQuantifierNumBound(environment, pF);
    long[] freeVars = new long[numBound];
    for (int i = 0; i < numBound; i++) {
      long varName = Native.getQuantifierBoundName(environment, pF, i);
      long varSort = Native.getQuantifierBoundSort(environment, pF, i);
      long freeVar = Native.mkConst(environment, varName, varSort);
      Native.incRef(environment, freeVar);
      freeVars[i] = freeVar;
    }

    // For every bound variable (de-Bruijn index from 0 to numBound), we replace the bound variable
    // with its free version.
    long body = Native.getQuantifierBody(environment, pF);
    long substBody = Native.substituteVars(environment, body, numBound, freeVars);

    Quantifier q =
        Native.isQuantifierForall(environment, pF) ? Quantifier.FORALL : Quantifier.EXISTS;

    return pVisitor.visitQuantifier(
        pFormula,
        q,
        Longs.asList(freeVars).stream()
            .map(this::encapsulateWithTypeOf)
            .collect(Collectors.toList()),
        encapsulateBoolean(substBody));
  }

  private FunctionDeclarationKind getDeclarationKind(long f) {
    final int arity = Native.getArity(environment, Native.getAppDecl(environment, f));
    assert arity > 0
        : String.format(
            "Unexpected arity '%s' for formula '%s' for handling a function application.",
            arity, Native.astToString(environment, f));
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
      case Z3_OP_TO_INT:
        return FunctionDeclarationKind.FLOOR;
      case Z3_OP_TO_REAL:
        return FunctionDeclarationKind.TO_REAL;
      case Z3_OP_INT2BV:
        return FunctionDeclarationKind.INT_TO_BV;

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
      case Z3_OP_CONST_ARRAY:
        return FunctionDeclarationKind.CONST;

      case Z3_OP_TRUE:
      case Z3_OP_FALSE:
      case Z3_OP_ANUM:
      case Z3_OP_AGNUM:
        throw new UnsupportedOperationException("Unexpected state: constants not expected");
      case Z3_OP_OEQ:
        throw new UnsupportedOperationException("Unexpected state: not a proof");
      case Z3_OP_UMINUS:
        return FunctionDeclarationKind.UMINUS;
      case Z3_OP_IDIV:

        // TODO: different handling for integer division?
        return FunctionDeclarationKind.DIV;

      case Z3_OP_EXTRACT:
        return FunctionDeclarationKind.BV_EXTRACT;
      case Z3_OP_CONCAT:
        return FunctionDeclarationKind.BV_CONCAT;
      case Z3_OP_BNOT:
        return FunctionDeclarationKind.BV_NOT;
      case Z3_OP_BNEG:
        return FunctionDeclarationKind.BV_NEG;
      case Z3_OP_BAND:
        return FunctionDeclarationKind.BV_AND;
      case Z3_OP_BOR:
        return FunctionDeclarationKind.BV_OR;
      case Z3_OP_BXOR:
        return FunctionDeclarationKind.BV_XOR;
      case Z3_OP_ULT:
        return FunctionDeclarationKind.BV_ULT;
      case Z3_OP_SLT:
        return FunctionDeclarationKind.BV_SLT;
      case Z3_OP_ULEQ:
        return FunctionDeclarationKind.BV_ULE;
      case Z3_OP_SLEQ:
        return FunctionDeclarationKind.BV_SLE;
      case Z3_OP_UGT:
        return FunctionDeclarationKind.BV_UGT;
      case Z3_OP_SGT:
        return FunctionDeclarationKind.BV_SGT;
      case Z3_OP_UGEQ:
        return FunctionDeclarationKind.BV_UGE;
      case Z3_OP_SGEQ:
        return FunctionDeclarationKind.BV_SGE;
      case Z3_OP_BADD:
        return FunctionDeclarationKind.BV_ADD;
      case Z3_OP_BSUB:
        return FunctionDeclarationKind.BV_SUB;
      case Z3_OP_BMUL:
        return FunctionDeclarationKind.BV_MUL;
      case Z3_OP_BUDIV:
      case Z3_OP_BUDIV_I: // same as above, and divisor is non-zero
        return FunctionDeclarationKind.BV_UDIV;
      case Z3_OP_BSDIV:
      case Z3_OP_BSDIV_I: // same as above, and divisor is non-zero
        return FunctionDeclarationKind.BV_SDIV;
      case Z3_OP_BUREM:
      case Z3_OP_BUREM_I: // same as above, and divisor is non-zero
        return FunctionDeclarationKind.BV_UREM;
      case Z3_OP_BSREM:
      case Z3_OP_BSREM_I: // same as above, and divisor is non-zero
        return FunctionDeclarationKind.BV_SREM;
      case Z3_OP_BSMOD:
      case Z3_OP_BSMOD_I: // same as above, and divisor is non-zero
        return FunctionDeclarationKind.BV_SMOD;
      case Z3_OP_BSHL:
        return FunctionDeclarationKind.BV_SHL;
      case Z3_OP_BLSHR:
        return FunctionDeclarationKind.BV_LSHR;
      case Z3_OP_BASHR:
        return FunctionDeclarationKind.BV_ASHR;
      case Z3_OP_SIGN_EXT:
        return FunctionDeclarationKind.BV_SIGN_EXTENSION;
      case Z3_OP_ZERO_EXT:
        return FunctionDeclarationKind.BV_ZERO_EXTENSION;
      case Z3_OP_ROTATE_LEFT:
        return FunctionDeclarationKind.BV_ROTATE_LEFT_BY_INT;
      case Z3_OP_ROTATE_RIGHT:
        return FunctionDeclarationKind.BV_ROTATE_RIGHT_BY_INT;
      case Z3_OP_EXT_ROTATE_LEFT:
        return FunctionDeclarationKind.BV_ROTATE_LEFT;
      case Z3_OP_EXT_ROTATE_RIGHT:
        return FunctionDeclarationKind.BV_ROTATE_RIGHT;
      case Z3_OP_BV2INT:
        return FunctionDeclarationKind.UBV_TO_INT;
      case Z3_OP_SBV2INT:
        return FunctionDeclarationKind.SBV_TO_INT;

      case Z3_OP_FPA_NEG:
        return FunctionDeclarationKind.FP_NEG;
      case Z3_OP_FPA_ABS:
        return FunctionDeclarationKind.FP_ABS;
      case Z3_OP_FPA_MAX:
        return FunctionDeclarationKind.FP_MAX;
      case Z3_OP_FPA_MIN:
        return FunctionDeclarationKind.FP_MIN;
      case Z3_OP_FPA_SQRT:
        return FunctionDeclarationKind.FP_SQRT;
      case Z3_OP_FPA_SUB:
        return FunctionDeclarationKind.FP_SUB;
      case Z3_OP_FPA_ADD:
        return FunctionDeclarationKind.FP_ADD;
      case Z3_OP_FPA_DIV:
        return FunctionDeclarationKind.FP_DIV;
      case Z3_OP_FPA_MUL:
        return FunctionDeclarationKind.FP_MUL;
      case Z3_OP_FPA_REM:
        return FunctionDeclarationKind.FP_REM;
      case Z3_OP_FPA_LT:
        return FunctionDeclarationKind.FP_LT;
      case Z3_OP_FPA_LE:
        return FunctionDeclarationKind.FP_LE;
      case Z3_OP_FPA_GE:
        return FunctionDeclarationKind.FP_GE;
      case Z3_OP_FPA_GT:
        return FunctionDeclarationKind.FP_GT;
      case Z3_OP_FPA_EQ:
        return FunctionDeclarationKind.FP_EQ;
      case Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN:
        return FunctionDeclarationKind.FP_ROUND_EVEN;
      case Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY:
        return FunctionDeclarationKind.FP_ROUND_AWAY;
      case Z3_OP_FPA_RM_TOWARD_POSITIVE:
        return FunctionDeclarationKind.FP_ROUND_POSITIVE;
      case Z3_OP_FPA_RM_TOWARD_NEGATIVE:
        return FunctionDeclarationKind.FP_ROUND_NEGATIVE;
      case Z3_OP_FPA_RM_TOWARD_ZERO:
        return FunctionDeclarationKind.FP_ROUND_ZERO;
      case Z3_OP_FPA_ROUND_TO_INTEGRAL:
        return FunctionDeclarationKind.FP_ROUND_TO_INTEGRAL;
      case Z3_OP_FPA_TO_FP_UNSIGNED:
        return FunctionDeclarationKind.BV_UCASTTO_FP;
      case Z3_OP_FPA_TO_SBV:
        return FunctionDeclarationKind.FP_CASTTO_SBV;
      case Z3_OP_FPA_TO_UBV:
        return FunctionDeclarationKind.FP_CASTTO_UBV;
      case Z3_OP_FPA_TO_IEEE_BV:
        return FunctionDeclarationKind.FP_AS_IEEEBV;
      case Z3_OP_FPA_TO_FP:
        // use the last argument. other arguments can be part of rounding or casting.
        long arg = Native.getAppArg(environment, f, Native.getAppNumArgs(environment, f) - 1);
        Z3_sort_kind sortKind =
            Z3_sort_kind.fromInt(Native.getSortKind(environment, Native.getSort(environment, arg)));
        if (Z3_sort_kind.Z3_BV_SORT == sortKind) {
          return FunctionDeclarationKind.BV_SCASTTO_FP;
        } else {
          return FunctionDeclarationKind.FP_CASTTO_FP;
        }
      case Z3_OP_FPA_IS_NAN:
        return FunctionDeclarationKind.FP_IS_NAN;
      case Z3_OP_FPA_IS_INF:
        return FunctionDeclarationKind.FP_IS_INF;
      case Z3_OP_FPA_IS_ZERO:
        return FunctionDeclarationKind.FP_IS_ZERO;
      case Z3_OP_FPA_IS_NEGATIVE:
        return FunctionDeclarationKind.FP_IS_NEGATIVE;
      case Z3_OP_FPA_IS_SUBNORMAL:
        return FunctionDeclarationKind.FP_IS_SUBNORMAL;
      case Z3_OP_FPA_IS_NORMAL:
        return FunctionDeclarationKind.FP_IS_NORMAL;

      case Z3_OP_SEQ_CONCAT:
        return FunctionDeclarationKind.STR_CONCAT;
      case Z3_OP_SEQ_PREFIX:
        return FunctionDeclarationKind.STR_PREFIX;
      case Z3_OP_SEQ_SUFFIX:
        return FunctionDeclarationKind.STR_SUFFIX;
      case Z3_OP_SEQ_CONTAINS:
        return FunctionDeclarationKind.STR_CONTAINS;
      case Z3_OP_SEQ_EXTRACT:
        return FunctionDeclarationKind.STR_SUBSTRING;
      case Z3_OP_SEQ_REPLACE:
        return FunctionDeclarationKind.STR_REPLACE;
      case Z3_OP_SEQ_AT:
        return FunctionDeclarationKind.STR_CHAR_AT;
      case Z3_OP_SEQ_LENGTH:
        return FunctionDeclarationKind.STR_LENGTH;
      case Z3_OP_SEQ_INDEX:
        return FunctionDeclarationKind.STR_INDEX_OF;
      case Z3_OP_SEQ_TO_RE:
        return FunctionDeclarationKind.STR_TO_RE;
      case Z3_OP_SEQ_IN_RE:
        return FunctionDeclarationKind.STR_IN_RE;
      case Z3_OP_STR_TO_INT:
        return FunctionDeclarationKind.STR_TO_INT;
      case Z3_OP_STR_TO_CODE:
        return FunctionDeclarationKind.STR_TO_CODE;
      case Z3_OP_STR_FROM_CODE:
        return FunctionDeclarationKind.STR_FROM_CODE;
      case Z3_OP_INT_TO_STR:
        return FunctionDeclarationKind.INT_TO_STR;
      case Z3_OP_STRING_LT:
        return FunctionDeclarationKind.STR_LT;
      case Z3_OP_STRING_LE:
        return FunctionDeclarationKind.STR_LE;
      case Z3_OP_RE_PLUS:
        return FunctionDeclarationKind.RE_PLUS;
      case Z3_OP_RE_STAR:
        return FunctionDeclarationKind.RE_STAR;
      case Z3_OP_RE_OPTION:
        return FunctionDeclarationKind.RE_OPTIONAL;
      case Z3_OP_RE_CONCAT:
        return FunctionDeclarationKind.RE_CONCAT;
      case Z3_OP_RE_UNION:
        return FunctionDeclarationKind.RE_UNION;
      case Z3_OP_RE_RANGE:
        return FunctionDeclarationKind.RE_RANGE;
      case Z3_OP_RE_INTERSECT:
        return FunctionDeclarationKind.RE_INTERSECT;
      case Z3_OP_RE_COMPLEMENT:
        return FunctionDeclarationKind.RE_COMPLEMENT;

      default:
        return FunctionDeclarationKind.OTHER;
    }
  }

  /**
   * @param value Z3_ast
   * @return Whether the value is a constant and can be passed to {@link #convertValue(Long)}.
   */
  public boolean isConstant(long value) {
    return Native.isNumeralAst(environment, value)
        || Native.isAlgebraicNumber(environment, value)
        || Native.isString(environment, value)
        || isOP(environment, value, Z3_decl_kind.Z3_OP_FPA_FP) // FP from IEEE-BV
        || isOP(environment, value, Z3_decl_kind.Z3_OP_TRUE)
        || isOP(environment, value, Z3_decl_kind.Z3_OP_FALSE)
        || isOP(environment, value, Z3_decl_kind.Z3_OP_DT_CONSTRUCTOR); // enumeration value
  }

  /**
   * @param value Z3_ast representing a constant value.
   * @return {@link BigInteger} or {@link Double} or {@link Rational} or {@link Boolean} or {@link
   *     FloatingPointRoundingMode} or {@link String}.
   */
  @Override
  public Object convertValue(Long value) {
    if (!isConstant(value)) {
      return null;
    }

    Native.incRef(environment, value);

    Object constantValue =
        Z3_CONSTANTS.get(Native.getDeclKind(environment, Native.getAppDecl(environment, value)));
    if (constantValue != null) {
      return constantValue;
    }

    try {
      FormulaType<?> type = getFormulaType(value);
      if (type.isBooleanType()) {
        return isOP(environment, value, Z3_decl_kind.Z3_OP_TRUE);
      } else if (type.isIntegerType()) {
        return new BigInteger(Native.getNumeralString(environment, value));
      } else if (type.isRationalType()) {
        Rational ratValue = Rational.ofString(Native.getNumeralString(environment, value));
        return ratValue.isIntegral() ? ratValue.getNum() : ratValue;
      } else if (type.isStringType()) {
        String str = Native.getString(environment, value);
        return AbstractStringFormulaManager.unescapeUnicodeForSmtlib(str);
      } else if (type.isBitvectorType()) {
        return new BigInteger(Native.getNumeralString(environment, value));
      } else if (type.isFloatingPointType()) {
        return convertFloatingPoint((FloatingPointType) type, value);
      } else if (type.isEnumerationType()) {
        return Native.astToString(environment, value);
      } else {

        // Explicitly crash on unknown type.
        throw new IllegalArgumentException("Unexpected type encountered: " + type);
      }

    } finally {
      Native.decRef(environment, value);
    }
  }

  private FloatingPointNumber convertFloatingPoint(FloatingPointType pType, Long pValue) {
    if (isOP(environment, pValue, Z3_decl_kind.Z3_OP_FPA_FP)) {
      final var signBv = Native.getAppArg(environment, pValue, 0);
      final var expoBv = Native.getAppArg(environment, pValue, 1);
      final var mantBv = Native.getAppArg(environment, pValue, 2);
      assert isConstant(signBv) && isConstant(expoBv) && isConstant(mantBv);
      final var sign = Native.getNumeralString(environment, signBv);
      assert "0".equals(sign) || "1".equals(sign);
      final var expo = new BigInteger(Native.getNumeralString(environment, expoBv));
      final var mant = new BigInteger(Native.getNumeralString(environment, mantBv));
      return FloatingPointNumber.of(
          Sign.of(sign.charAt(0) == '1'),
          expo,
          mant,
          pType.getExponentSize(),
          pType.getMantissaSize());

    } else if (Native.fpaIsNumeralInf(environment, pValue)) {
      // Floating Point Inf uses:
      //  - a sign for positive/negative infinity,
      //  - "11..11" as exponent,
      //  - "00..00" as mantissa.
      String sign = getSign(pValue).isNegative() ? "1" : "0";
      return FloatingPointNumber.of(
          sign + "1".repeat(pType.getExponentSize()) + "0".repeat(pType.getMantissaSize()),
          pType.getExponentSize(),
          pType.getMantissaSize());

    } else if (Native.fpaIsNumeralNan(environment, pValue)) {
      // TODO We are underspecified here and choose several bits on our own.
      //  This is not sound, if we combine FP anf BV theory.
      // Floating Point NaN uses:
      //  - an unspecified sign (we choose "0"),
      //  - "11..11" as exponent,
      //  - an unspecified mantissa (we choose all "1").
      return FloatingPointNumber.of(
          "0" + "1".repeat(pType.getExponentSize()) + "1".repeat(pType.getMantissaSize()),
          pType.getExponentSize(),
          pType.getMantissaSize());

    } else {
      Sign sign = getSign(pValue);
      var exponentBv = Native.fpaGetNumeralExponentBv(environment, pValue, true);
      var exponent = Native.getNumeralString(environment, exponentBv);
      var mantissaBv = Native.fpaGetNumeralSignificandBv(environment, pValue);
      var mantissa = Native.getNumeralString(environment, mantissaBv);
      return FloatingPointNumber.of(
          sign,
          new BigInteger(exponent),
          new BigInteger(mantissa),
          pType.getExponentSize(),
          pType.getMantissaSize());
    }
  }

  private Sign getSign(Long pValue) {
    Native.IntPtr signPtr = new Native.IntPtr();
    Preconditions.checkState(
        Native.fpaGetNumeralSign(environment, pValue, signPtr), "Sign is not a Boolean value");
    var sign = signPtr.value != 0;
    return Sign.of(sign);
  }

  @Override
  public Long declareUFImpl(String pName, Long returnType, List<Long> pArgTypes) {
    long symbol = Native.mkStringSymbol(environment, pName);
    long[] sorts = Longs.toArray(pArgTypes);
    long func = Native.mkFuncDecl(environment, symbol, sorts.length, sorts, returnType);
    Native.incRef(environment, func);
    symbolsToDeclarations.put(pName, func);
    return func;
  }

  @Override
  public Long callFunctionImpl(Long declaration, List<Long> args) {
    return Native.mkApp(environment, declaration, args.size(), Longs.toArray(args));
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Long pLong) {
    return Native.getAppDecl(getEnv(), pLong);
  }

  /** returns, if the function of the expression is the given operation. */
  static boolean isOP(long z3context, long expr, Z3_decl_kind op) {
    if (!Native.isApp(z3context, expr)) {
      return false;
    }

    long decl = Native.getAppDecl(z3context, expr);
    return Native.getDeclKind(z3context, decl) == op.toInt();
  }

  /**
   * Apply multiple tactics in sequence.
   *
   * @throws InterruptedException thrown by JNI code in case of termination request
   * @throws SolverException thrown by JNI code in case of error
   */
  public long applyTactics(long z3context, final Long pF, String... pTactics)
      throws InterruptedException, SolverException {
    long overallResult = pF;
    for (String tactic : pTactics) {
      overallResult = applyTactic(z3context, overallResult, tactic);
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
   * @throws InterruptedException If execution gets interrupted.
   */
  public long applyTactic(long z3context, long pF, String tactic)
      throws InterruptedException, SolverException {
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

    try {
      return applyResultToAST(z3context, result);
    } finally {
      Native.goalDecRef(z3context, goal);
      Native.tacticDecRef(z3context, tacticObject);
    }
  }

  private long applyResultToAST(long z3context, long applyResult) {
    int subgoalsCount = Native.applyResultGetNumSubgoals(z3context, applyResult);
    long[] goalFormulas = new long[subgoalsCount];
    for (int i = 0; i < subgoalsCount; i++) {
      long subgoal = Native.applyResultGetSubgoal(z3context, applyResult, i);
      goalFormulas[i] = goalToAST(z3context, subgoal);
    }
    return goalFormulas.length == 1
        ? goalFormulas[0]
        : Native.mkOr(z3context, goalFormulas.length, goalFormulas);
  }

  private long goalToAST(long z3context, long goal) {
    int subgoalFormulasCount = Native.goalSize(z3context, goal);
    long[] subgoalFormulas = new long[subgoalFormulasCount];
    for (int k = 0; k < subgoalFormulasCount; k++) {
      subgoalFormulas[k] = Native.goalFormula(z3context, goal, k);
    }
    return subgoalFormulas.length == 1
        ? subgoalFormulas[0]
        : Native.mkAnd(z3context, subgoalFormulas.length, subgoalFormulas);
  }

  /** Closing the context. */
  @SuppressWarnings("empty-statement")
  public void forceClose() {
    // Force clean all ASTs, even those which were not GC'd yet.
    if (usePhantomReferences) {
      Z3AstReference cur = referenceListHead.next;
      assert cur != null;
      while (cur.next != null) {
        Native.decRef(environment, cur.z3Ast);
        cur = cur.next;
      }
      Z3AstReference tail = cur;
      // Bulk delete everything between head and tail
      referenceListHead.next = tail;
      tail.prev = referenceListHead;

      // Remove already enqueued references.
      while (referenceQueue.poll() != null) {
        // NOTE: Together with the above list deletion, this empty loop will guarantee that no more
        // ast references are reachable by the GC making them all eligible for garbage collection
        // and preventing them from getting enqueued into the reference queue in the future.
      }
    }
  }

  /**
   * get a previously created application declaration, or <code>NULL</code> if the symbol is
   * unknown.
   */
  @Nullable Long getKnownDeclaration(String symbolName) {
    return symbolsToDeclarations.get(symbolName);
  }
}
