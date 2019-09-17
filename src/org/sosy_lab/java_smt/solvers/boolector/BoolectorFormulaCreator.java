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

import com.google.common.collect.ImmutableList;
import com.google.common.primitives.Longs;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorFormula.BoolectorArrayFormula;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorFormula.BoolectorBitvectorFormula;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorFormula.BoolectorBooleanFormula;

public class BoolectorFormulaCreator
    extends FormulaCreator<Long, Long, BoolectorEnvironment, Long> {

  // Boolector can give back 'x' for a arbitrary value that we change to this
  private static final char arbitrary_value = '1';
  BoolectorVariablesCache cache;
  private long btor;

  BoolectorFormulaCreator(BoolectorEnvironment pEnv) {
    super(pEnv, pEnv.getBoolSort(), null, null);
    this.btor = getEnv().getBtor();
    cache = new BoolectorVariablesCache(btor);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    if (pFormula instanceof BitvectorFormula) {
      long sort = BtorJNI.boolector_get_sort(btor, extractInfo(pFormula));
      checkArgument(
          BtorJNI.boolector_is_bitvec_sort(btor, sort),
          "BitvectorFormula with type missmatch: " + pFormula);
      return (FormulaType<T>) FormulaType
          .getBitvectorTypeWithSize(BtorJNI.boolector_get_width(btor, extractInfo(pFormula)));
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
    long sort = BtorJNI.boolector_get_sort(btor, pFormula);
    if (BtorJNI.boolector_is_bitvec_sort(btor, sort)) {
      if (sort == 1) {
        return FormulaType.BooleanType;
      } else {
        return FormulaType
            .getBitvectorTypeWithSize(BtorJNI.boolector_get_width(btor, pFormula));
      }
    } else if (BtorJNI.boolector_is_array_sort(btor, sort)) {
      int indexWidth = BtorJNI.boolector_get_index_width(btor, pFormula);
      int elementWidth = BtorJNI.boolector_get_width(btor, pFormula);
      return FormulaType.getArrayType(
          FormulaType.getBitvectorTypeWithSize(indexWidth),
          FormulaType.getBitvectorTypeWithSize(elementWidth));
    }
    throw new IllegalArgumentException("Unknown formula type for " + pFormula);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Long pTerm) {
    assert pType.equals(getFormulaType(pTerm)) : String
        .format("Trying to encapsulate formula of type %s as %s", getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new BoolectorBooleanFormula(
          pTerm,
          btor);
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T) new BoolectorArrayFormula<>(
          pTerm,
          arrFt.getIndexType(),
          arrFt.getElementType(),
          btor);
    } else if (pType.isBitvectorType()) {
      return (T) new BoolectorBitvectorFormula(pTerm, btor);
    }
    throw new IllegalArgumentException(
        "Cannot create formulas of type " + pType + " in Boolector.");
  }

  @Override
  public BooleanFormula encapsulateBoolean(Long pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new BoolectorBooleanFormula(pTerm, btor);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Long pTerm) {
    assert getFormulaType(pTerm).isBitvectorType();
    return new BoolectorBitvectorFormula(pTerm, btor);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE>
      encapsulateArray(Long pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).isArrayType();
    return new BoolectorArrayFormula<>(pTerm, pIndexType, pElementType, btor);
  }



  // In Boolector a type is called a sort
  @Override
  public Long getBitvectorType(int pBitwidth) {
    return BtorJNI.boolector_bitvec_sort(btor, pBitwidth);
  }

  @Override
  public Long getFloatingPointType(FloatingPointType pType) {
    throw new UnsupportedOperationException(
        "Boolector does not support floating point operations.");
  }

  @Override
  public Long getArrayType(Long pIndexType, Long pElementType) {
    return BtorJNI.boolector_array_sort(btor, pIndexType, pElementType);
  }

  // Checks if there is a variable with the exact same name and type and gives that back, or a new
  // one, potentially with a new internal name (see cache).
  @Override
  public Long makeVariable(Long type, String varName) {
    String newName = varName;
    if (cache.isNameUsed(varName)) {
      Long maybeFormula = cache.getExistingFormula(varName, type);
      if (cache.getExistingFormula(varName, type) != null) {
        return maybeFormula;
      } else {
        newName = cache.getNewVarName(varName);
      }
    }
    long newVar = BtorJNI.boolector_var(btor, type, newName);
    cache.enterNewFormula(newName, varName, newVar);
    return newVar;
  }

  // This method is a massive problem... you CANT get the value formulas(nodes) of ufs because its
  // only build and used internally in boolector....
  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula pFormula, Long pF) {
    throw new UnsupportedOperationException(
        "We wait till the Boolector devs give us methods to do this.");
    if (BtorJNI.boolector_is_const(btor, pF)) {
      // Handles all constants (bitvec, bool)
      String f = BtorJNI.boolector_get_bits(btor, pF);
      return visitor.visitConstant(pFormula, convertValue(pF, parseBitvector(f)));
    } else if (BtorJNI.boolector_is_array(btor, pF)) {
      // array = function?!
    } else if (BtorJNI.boolector_is_uf(btor, pF)) {
      // UF
      String[][] ufAssignment = BtorJNI.boolector_uf_assignment_helper(btor, pF);
      int arity = BtorJNI.boolector_get_fun_arity(btor, pF);
      ImmutableList.Builder<Formula> args = ImmutableList.builder();
      ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();
      for (int i = 0; i < arity; i++) {
        FormulaType<?> argumentType = getFormulaType(arg);
        args.add(encapsulate(argumentType, arg));
        argTypes.add(argumentType);
      }
      return visitor.visitFunction(pFormula, args.build(), FunctionDeclarationImpl.of());
    } else if (BtorJNI.boolector_is_param(btor, pF)) {
      // Quantifier var (param)
      int deBruijnIdx; // TODO: how?
      return visitor.visitBoundVariable(pFormula, deBruijnIdx);
    } else if (bodyVars != null) {
      // Quantifier node
      QuantifiedFormulaManager.Quantifier quantifier = QuantifiedFormulaManager.Quantifier.FORALL;
      if (bodyVars.isForall()) {
        quantifier = QuantifiedFormulaManager.Quantifier.EXISTS;
      }
      List<Formula> boundVariables = new ArrayList<>();
      for (long arg : bodyVars.getBoundVariables()) {
        boundVariables.add(encapsulate(getFormulaType(arg), arg));
      }
      long body = bodyVars.getBody();
      FormulaType<?> argumentType = getFormulaType(body);
      // if this isnt working or too much, pass an empty list.
      // But Boolector simply holds not information at all about the quantifier besides the result.
      return visitor
          .visitQuantifier(
              (BoolectorBooleanFormula) pFormula,
              quantifier,
              boundVariables,
              new BoolectorBooleanFormula(body, btor));
    }
      else {
      // must be bitvector var at this point
      return visitor
          .visitFreeVariable(pFormula, getName(btor, pF));
    }
  }

  @Override
  public Long callFunctionImpl(Long pDeclaration, List<Long> pArgs) {
    return BtorJNI
        .boolector_apply(btor, Longs.toArray(pArgs), pArgs.size(), pDeclaration);
  }

  @Override
  public Long declareUFImpl(String name, Long pReturnType, List<Long> pArgTypes) {
    long[] funSorts = Longs.toArray(pArgTypes);
    long sort;
    String newUfName = name;
    if (pArgTypes.isEmpty()) {
      sort = pReturnType;
    } else {
      sort = BtorJNI.boolector_fun_sort(btor, funSorts, funSorts.length, pReturnType);
    }
    if (cache.isNameUsed(name)) {
      Long maybeFormula = cache.getExistingFormula(name, sort);
      if (cache.getExistingFormula(name, sort) != null) {
        return maybeFormula;
      } else {
        newUfName = cache.getNewVarName(name);
      }
    }
    Long uf = BtorJNI.boolector_uf(btor, sort, newUfName);
    cache.enterNewFormula(newUfName, name, uf);
    return uf;
  }

  @Override
  public Object convertValue(Long key, Long term) {
    // TODO: UF / ARRAY
    String value = null;
    if (BtorJNI.boolector_is_array(btor, term)) {
      value = BtorJNI.boolector_bv_assignment(btor, term);
    } else if (BtorJNI.boolector_is_const(btor, term)) {
      value = BtorJNI.boolector_get_bits(btor, term);
    } else if (BtorJNI.boolector_is_bitvec_sort(btor, BtorJNI.boolector_get_sort(btor, term))) {
      value = BtorJNI.boolector_bv_assignment(btor, term);
    } else {
      value = BtorJNI.boolector_bv_assignment(btor, term);
    }
    // To get the correct type, we check the width of the term (== 1 means bool).
    int width = BtorJNI.boolector_get_width(btor, term);
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
          charArray[i] = arbitrary_value;
        } else if (charArray[i] != '0' && charArray[i] != '1') {
          throw new IllegalArgumentException(
              "Boolector gave back an assignment that is not parseable.");
        }
      }
      assignment = charArray.toString();
    }
    return new BigInteger(assignment, 2);
  }


  /**
   * Transforms String bitvec into Long
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
      bitVec = charArray.toString();
    }
    BigInteger bigInt = new BigInteger(bitVec, 2);
    return bigInt.longValue();
  }

  String getName(long pKey) {
    return cache.getJavaSMTVarName(BtorJNI.boolector_get_symbol(btor, pKey));
  }

  @Override
  public Object convertValue(Long pF) {
    throw new UnsupportedOperationException(
        "Please use the other method.");
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Long pTFormulaInfo) {
    // declaration of constant or fun
    if (BtorJNI.boolector_is_const(btor, pTFormulaInfo)) {
      return parseBitvector(BtorJNI.boolector_get_bits(btor, pTFormulaInfo));
    } else if (BtorJNI.boolector_is_var(btor, pTFormulaInfo)) {
      return parseBitvector(BtorJNI.boolector_bv_assignment(btor, pTFormulaInfo));
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
  protected BoolectorVariablesCache getCache() {
    return cache;
  }

  @Override
  protected <TI extends Formula, TE extends Formula> FormulaType<TE>
      getArrayFormulaElementType(ArrayFormula<TI, TE> pArray) {
    return ((BoolectorArrayFormula<TI, TE>) pArray).getElementType();
  }

  @Override
  protected <TI extends Formula, TE extends Formula> FormulaType<TI>
      getArrayFormulaIndexType(ArrayFormula<TI, TE> pArray) {
    return ((BoolectorArrayFormula<TI, TE>) pArray).getIndexType();
  }

}
