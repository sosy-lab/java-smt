// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Table;
import com.google.common.primitives.Longs;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorFormula.BoolectorArrayFormula;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorFormula.BoolectorBitvectorFormula;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorFormula.BoolectorBooleanFormula;

public class BoolectorFormulaCreator extends FormulaCreator<Long, Long, Long, Long> {

  // Boolector can give back 'x' for an arbitrary value that we change to this
  private static final char ARBITRARY_VALUE = '1';

  /**
   * Maps a name and a variable or function type to a concrete formula node. We allow only 1 type
   * per var name, meaning there is only 1 column per row!
   */
  private final Table<String, Long, Long> formulaCache = HashBasedTable.create();

  // Remember uf sorts, as Boolector does not give them back correctly
  private final Map<Long, List<Long>> ufArgumentsSortMap = new HashMap<>();

  // Possibly we need to split this up into vars, ufs, and arrays

  BoolectorFormulaCreator(Long btor) {
    super(btor, BtorJNI.boolector_bool_sort(btor), null, null, null, null);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    if (pFormula instanceof BitvectorFormula) {
      long sort = BtorJNI.boolector_get_sort(getEnv(), extractInfo(pFormula));
      checkArgument(
          BtorJNI.boolector_is_bitvec_sort(getEnv(), sort),
          "BitvectorFormula with type missmatch: %s",
          pFormula);
      return (FormulaType<T>)
          FormulaType.getBitvectorTypeWithSize(
              BtorJNI.boolector_get_width(getEnv(), extractInfo(pFormula)));
    } else if (pFormula instanceof ArrayFormula<?, ?>) {
      FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
      FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public Long extractInfo(Formula pT) {
    return BoolectorFormulaManager.getBtorTerm(pT);
  }

  @Override
  public FormulaType<?> getFormulaType(Long pFormula) {
    long sort = BtorJNI.boolector_get_sort(getEnv(), pFormula);
    // Careful, Boolector interprets nearly everything as a fun!
    if (!BtorJNI.boolector_is_array_sort(getEnv(), sort)
        && !BtorJNI.boolector_is_bitvec_sort(getEnv(), sort)
        && BtorJNI.boolector_is_fun_sort(getEnv(), sort)) {
      sort = BtorJNI.boolector_fun_get_codomain_sort(getEnv(), pFormula);
    }
    return getFormulaTypeFromSortAndFormula(pFormula, sort);
  }

  /**
   * Returns the proper FormulaType for the sort entered.
   *
   * @param pFormula Some Boolector node. Either the node of the sort, or its parent. Only has to be
   *     accurate for arrays.
   * @param sort The actual sort you want the FormulaType of.
   * @return FormulaType for the sort.
   */
  private FormulaType<?> getFormulaTypeFromSortAndFormula(Long pFormula, Long sort) {
    if (BtorJNI.boolector_is_array_sort(getEnv(), sort)) {
      int indexWidth = BtorJNI.boolector_get_index_width(getEnv(), pFormula);
      int elementWidth = BtorJNI.boolector_get_width(getEnv(), pFormula);
      return FormulaType.getArrayType(
          FormulaType.getBitvectorTypeWithSize(indexWidth),
          FormulaType.getBitvectorTypeWithSize(elementWidth));
    } else if (BtorJNI.boolector_is_bitvec_sort(getEnv(), sort)) {
      int width = BtorJNI.boolector_bitvec_sort_get_width(getEnv(), sort);
      if (width == 1) {
        return FormulaType.BooleanType;
      } else {
        return FormulaType.getBitvectorTypeWithSize(width);
      }
    }
    throw new IllegalArgumentException("Unknown formula type for " + pFormula);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Long pTerm) {
    assert pType.equals(getFormulaType(pTerm))
        : String.format(
            "Trying to encapsulate formula of type %s as %s", getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new BoolectorBooleanFormula(pTerm, getEnv());
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T)
          new BoolectorArrayFormula<>(
              pTerm, arrFt.getIndexType(), arrFt.getElementType(), getEnv());
    } else if (pType.isBitvectorType()) {
      return (T) new BoolectorBitvectorFormula(pTerm, getEnv());
    }
    throw new IllegalArgumentException(
        "Cannot create formulas of type " + pType + " in Boolector.");
  }

  @Override
  public BooleanFormula encapsulateBoolean(Long pTerm) {
    assert getFormulaType(pTerm).isBooleanType()
        : "Unexpected formula type for Boolean formula: " + getFormulaType(pTerm);
    return new BoolectorBooleanFormula(pTerm, getEnv());
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Long pTerm) {
    assert getFormulaType(pTerm).isBitvectorType()
        : "Unexpected formula type for BV formula: " + getFormulaType(pTerm);
    return new BoolectorBitvectorFormula(pTerm, getEnv());
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Long pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).isArrayType()
        : "Unexpected formula type for array formula: " + getFormulaType(pTerm);
    return new BoolectorArrayFormula<>(pTerm, pIndexType, pElementType, getEnv());
  }

  @Override
  public Long getBitvectorType(int pBitwidth) {
    return BtorJNI.boolector_bitvec_sort(getEnv(), pBitwidth);
  }

  @Override
  public Long getFloatingPointType(FloatingPointType pType) {
    throw new UnsupportedOperationException(
        "Boolector does not support floating point operations.");
  }

  @Override
  public Long getArrayType(Long pIndexType, Long pElementType) {
    return BtorJNI.boolector_array_sort(getEnv(), pIndexType, pElementType);
  }

  // Checks if there is a variable with the exact same name and type and gives that back, or a new
  // one, potentially with a new internal name (see cache).
  @Override
  public Long makeVariable(Long type, String varName) {
    Long maybeFormula = formulaCache.get(varName, type);
    if (maybeFormula != null) {
      return maybeFormula;
    }
    if (formulaCache.containsRow(varName)) {
      throw new IllegalArgumentException("Symbol already used: " + varName);
    }
    long newVar = BtorJNI.boolector_var(getEnv(), type, varName);
    formulaCache.put(varName, type, newVar);
    return newVar;
  }

  // This method is a massive problem... you CAN'T get the value formulas(nodes) because they are
  // only build and used internally in Boolector. (See visit1 for help)
  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, Long f) {
    throw new UnsupportedOperationException(
        "Boolector has no methods to access internal nodes for visitation.");
  }

  // Hopefully a helpful template for when visitor gets implemented
  // Btor only has bitvec arrays and ufs with bitvecs and arrays of bitvecs
  // (and quantifier with bitvecs only)
  @SuppressWarnings({"deprecation", "unused"})
  private <R> R visit1(FormulaVisitor<R> visitor, Formula formula, Long f) {
    if (BtorJNI.boolector_is_const(getEnv(), f)) {
      // Handles all constants (bitvec, bool)
      String bits = BtorJNI.boolector_get_bits(getEnv(), f);
      return visitor.visitConstant(formula, convertValue(f, parseBitvector(bits)));
    } else if (BtorJNI.boolector_is_param(getEnv(), f)) {
      // Quantifier have their own variables called param.
      // They can only be bound once! (use them as bitvec)
      int deBruijnIdx = 0; // TODO: Ask Developers for this because this is WRONG!
      return visitor.visitBoundVariable(formula, deBruijnIdx);
    } else if (false) {
      // Quantifier
      // there is currently no way to find out if the formula is a quantifier
      // do we need them separately?
      /*
       * return visitor .visitQuantifier( (BoolectorBooleanFormula) formula, quantifier,
       * boundVariables, new BoolectorBooleanFormula(body, getEnv()));
       */
    } else if (BtorJNI.boolector_is_var(getEnv(), f)) {
      // bitvec var (size 1 is bool!)
      return visitor.visitFreeVariable(formula, getName(f));
    } else {
      ImmutableList.Builder<Formula> args = ImmutableList.builder();

      ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();

      return visitor.visitFunction(
          formula,
          args.build(),
          FunctionDeclarationImpl.of(
              getName(f), getDeclarationKind(f), argTypes.build(), getFormulaType(f), f));
    } // TODO: fix declaration in visitFunction
    return null;
  }

  // TODO: returns kind of formula (add, uf etc....) once methods are provided
  private FunctionDeclarationKind getDeclarationKind(@SuppressWarnings("unused") long f) {
    return null;
  }

  @Override
  public Long callFunctionImpl(Long pDeclaration, List<Long> pArgs) {
    Preconditions.checkArgument(
        !pArgs.isEmpty(), "Boolector does not support UFs without arguments.");
    return BtorJNI.boolector_apply(getEnv(), Longs.toArray(pArgs), pArgs.size(), pDeclaration);
  }

  @Override
  public Long declareUFImpl(String name, Long pReturnType, List<Long> pArgTypes) {
    Preconditions.checkArgument(
        !pArgTypes.isEmpty(), "Boolector does not support UFs without arguments.");

    long[] funSorts = Longs.toArray(pArgTypes);
    long sort = BtorJNI.boolector_fun_sort(getEnv(), funSorts, funSorts.length, pReturnType);
    Long maybeFormula = formulaCache.get(name, sort);
    if (maybeFormula != null) {
      return maybeFormula;
    }
    if (formulaCache.containsRow(name)) {
      throw new IllegalArgumentException("Symbol already used: " + name);
    }
    long uf = BtorJNI.boolector_uf(getEnv(), sort, name);
    formulaCache.put(name, sort, uf);
    ufArgumentsSortMap.put(uf, pArgTypes);
    return uf;
  }

  @Override
  public Object convertValue(Long term) {
    String value;
    if (BtorJNI.boolector_is_const(getEnv(), term)) {
      value = BtorJNI.boolector_get_bits(getEnv(), term);
      return transformStringToBigInt(value);

    } else if (BtorJNI.boolector_is_bitvec_sort(
        getEnv(), BtorJNI.boolector_get_sort(getEnv(), term))) {
      value = BtorJNI.boolector_bv_assignment(getEnv(), term);
      return transformStringToBigInt(value);

    } else if (BtorJNI.boolector_is_fun(getEnv(), term)) {
      value = BtorJNI.boolector_uf_assignment_helper(getEnv(), term)[1][0];
      return transformStringToBigInt(value);

    } else if (BtorJNI.boolector_is_array(getEnv(), term)) {
      List<Object> arrayValues = new ArrayList<>();
      for (String stringArrayEntry : BtorJNI.boolector_array_assignment_helper(getEnv(), term)[1]) {
        arrayValues.add(transformStringToBigInt(stringArrayEntry));
      }
      return arrayValues;
    }
    throw new AssertionError("unknown sort and term");
  }

  protected Object transformStringToBigInt(String value) {
    // To get the correct type, we check the width of the term (== 1 means bool).
    int width = value.length();
    if (width == 1) {
      long longValue = parseBigInt(value).longValue();
      if (longValue == 1) {
        return true;
      } else if (longValue == 0) {
        return false;
      } else {
        throw new IllegalArgumentException("Unexpected type with value: " + value);
      }
    }
    return parseBigInt(value);
  }

  /**
   * Boolector puts out Strings containing 1,0 or x that have to be parsed. If you want different
   * values for x, change it in the constant! (BOOLECTOR_VARIABLE_ARBITRARI_REPLACEMENT)
   *
   * @param assignment String with the assignment of Boolector var.
   * @return BigInteger in decimal.
   */
  private BigInteger parseBigInt(String assignment) {
    try {
      return new BigInteger(assignment, 2);
    } catch (NumberFormatException e) {
      char[] charArray = assignment.toCharArray();
      for (int i = 0; i < charArray.length; i++) {
        if (charArray[i] == 'x') {
          charArray[i] = ARBITRARY_VALUE;
        } else if (charArray[i] != '0' && charArray[i] != '1') {
          throw new IllegalArgumentException(
              "Boolector gave back an assignment that is not parseable.");
        }
      }
      assignment = String.valueOf(charArray);
    }
    return new BigInteger(assignment, 2);
  }

  /**
   * Transforms String bitvec into Long.
   *
   * @param bitVec return value of Boolector
   * @return gives back the long version of the bitvector
   */
  private Long parseBitvector(String bitVec) {
    try {
      BigInteger bigInt = new BigInteger(bitVec, 2);
      return bigInt.longValue();
    } catch (NumberFormatException e) {
      char[] charArray = bitVec.toCharArray();
      for (int i = 0; i < charArray.length; i++) {
        if (charArray[i] == 'x') {
          charArray[i] = '1';
        } else if (charArray[i] != '0' && charArray[i] != '1') {
          throw new IllegalArgumentException(
              "Boolector gave back an assignment that is not parseable.");
        }
      }
      bitVec = String.valueOf(charArray);
    }
    BigInteger bigInt = new BigInteger(bitVec, 2);
    return bigInt.longValue();
  }

  String getName(long pKey) {
    return BtorJNI.boolector_get_symbol(getEnv(), pKey);
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Long pTFormulaInfo) {
    // declaration of constant or fun
    if (BtorJNI.boolector_is_const(getEnv(), pTFormulaInfo)) {
      return parseBitvector(BtorJNI.boolector_get_bits(getEnv(), pTFormulaInfo));
    } else if (BtorJNI.boolector_is_var(getEnv(), pTFormulaInfo)) {
      return parseBitvector(BtorJNI.boolector_bv_assignment(getEnv(), pTFormulaInfo));
    } else {
      throw new IllegalArgumentException(
          "Debug only! getBooleanVarDeclarationImpl in BtorFormulaCreator");
    }
  }

  // Returns the variables cache with keys variable name and type
  protected Table<String, Long, Long> getCache() {
    return formulaCache;
  }

  // True if the entered String has an existing variable in the cache.
  protected boolean formulaCacheContains(String variable) {
    // There is always only 1 type permitted per variable
    return formulaCache.containsRow(variable);
  }

  // Optional that contains the variable to the entered String if there is one.
  protected Optional<Long> getFormulaFromCache(String variable) {
    Iterator<java.util.Map.Entry<Long, Long>> entrySetIter =
        formulaCache.row(variable).entrySet().iterator();
    if (entrySetIter.hasNext()) {
      // If there is a non-empty row for an entry, there is only one entry
      return Optional.of(entrySetIter.next().getValue());
    }
    return Optional.empty();
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> FormulaType<TE> getArrayFormulaElementType(
      ArrayFormula<TI, TE> pArray) {
    return ((BoolectorArrayFormula<TI, TE>) pArray).getElementType();
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> FormulaType<TI> getArrayFormulaIndexType(
      ArrayFormula<TI, TE> pArray) {
    return ((BoolectorArrayFormula<TI, TE>) pArray).getIndexType();
  }
}
