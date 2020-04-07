/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.boolector;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Table;
import com.google.common.primitives.Longs;
import java.math.BigInteger;
import java.util.List;
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

  // Boolector can give back 'x' for a arbitrary value that we change to this
  private static final char ARBITRARY_VALUE = '1';

  /** Maps a name and a variable or function type to a concrete formula node. */
  private final Table<String, Long, Long> nameFormulaCache = HashBasedTable.create();

  BoolectorFormulaCreator(Long btor) {
    super(btor, BtorJNI.boolector_bool_sort(btor), null, null);
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
    if (BtorJNI.boolector_is_bitvec_sort(getEnv(), sort)) {
      if (sort == 1) {
        return FormulaType.BooleanType;
      } else {
        return FormulaType.getBitvectorTypeWithSize(
            BtorJNI.boolector_get_width(getEnv(), pFormula));
      }
    } else if (BtorJNI.boolector_is_array_sort(getEnv(), sort)) {
      int indexWidth = BtorJNI.boolector_get_index_width(getEnv(), pFormula);
      int elementWidth = BtorJNI.boolector_get_width(getEnv(), pFormula);
      return FormulaType.getArrayType(
          FormulaType.getBitvectorTypeWithSize(indexWidth),
          FormulaType.getBitvectorTypeWithSize(elementWidth));
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
    Long maybeFormula = nameFormulaCache.get(varName, type);
    if (maybeFormula != null) {
      return maybeFormula;
    }
    if (nameFormulaCache.containsRow(varName)) {
      throw new IllegalArgumentException("Symbol already used: " + varName);
    }
    long newVar = BtorJNI.boolector_var(getEnv(), type, varName);
    nameFormulaCache.put(varName, type, newVar);
    return newVar;
  }

  // This method is a massive problem... you CANT get the value formulas(nodes) because they are
  // only build and used internally in boolector. (See visit1 for help)
  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, Long f) {
    throw new UnsupportedOperationException(
        "We wait till the Boolector devs give us methods to do this.");
  }

  // Hopefully a helpful template for when visitor gets implemented
  // Btor only has bitvec arrays and ufs with bitvecs and arrays of bitvecs
  // (and quantifier with bitvecs only)
  @SuppressWarnings("unused")
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
    Long maybeFormula = nameFormulaCache.get(name, sort);
    if (maybeFormula != null) {
      return maybeFormula;
    }
    if (nameFormulaCache.containsRow(name)) {
      throw new IllegalArgumentException("Symbol already used: " + name);
    }
    long uf = BtorJNI.boolector_uf(getEnv(), sort, name);
    nameFormulaCache.put(name, sort, uf);
    return uf;
  }

  @Override
  public Object convertValue(Long key, Long term) {
    String value;
    if (BtorJNI.boolector_is_array(getEnv(), term)) {
      value = BtorJNI.boolector_bv_assignment(getEnv(), term);
    } else if (BtorJNI.boolector_is_const(getEnv(), term)) {
      value = BtorJNI.boolector_get_bits(getEnv(), term);
    } else if (BtorJNI.boolector_is_bitvec_sort(
        getEnv(), BtorJNI.boolector_get_sort(getEnv(), term))) {
      value = BtorJNI.boolector_bv_assignment(getEnv(), term);
    } else {
      throw new AssertionError("unknown sort and term");
      // value = BtorJNI.boolector_bv_assignment(getEnv(), term);
    }
    // To get the correct type, we check the width of the term (== 1 means bool).
    int width = BtorJNI.boolector_get_width(getEnv(), term);
    if (width == 1) {
      Long longValue = parseBigInt(value).longValue();
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
      BigInteger bigInt = new BigInteger(assignment, 2);
      return bigInt;
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
  public Object convertValue(Long pF) {
    throw new UnsupportedOperationException("Please use the other method.");
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

  /**
   * Returns current variables cache.
   *
   * @return variables cache.
   */
  protected Table<String, Long, Long> getCache() {
    return nameFormulaCache;
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
