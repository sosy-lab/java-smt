// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ABS;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_AND;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_APP_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_GE_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_SUM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BIT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BOOL_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_ARRAY;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_ASHR;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_DIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_GE_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_LSHR;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_MUL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_REM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SDIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SGE_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SHL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SMOD;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SREM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SUM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_CEIL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_DISTINCT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_DIVIDES_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_EQ_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_FLOOR;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_FORALL_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_IDIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_IMOD;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_IS_INT_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ITE_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_NOT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_OR_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_POWER_PRODUCT;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_RDIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_SELECT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_UNINTERPRETED_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_VARIABLE;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_XOR_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_abs;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_and;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_application;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_geq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bitextract;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvarray;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvashr;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvconst_from_array;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvdiv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvge_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvlshr;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvmul;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvpower;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvproduct;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvrem;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsdiv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsge_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvshl;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsmod;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsrem;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsum;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsum_component;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvtype_size;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_ceil;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_distinct;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_divides_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_division;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_eq;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_floor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_function_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_term_by_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_idiv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_imod;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int32;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_is_int_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_ite;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_mul;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_uninterpreted_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_variable;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_not;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_or;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_rational;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_power;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_product;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_product_component;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_proj_arg;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_proj_index;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_rational_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_real_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_set_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sum;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sum_component;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_bitsize;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_child;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_constructor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_bitvector;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_bool;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_int;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_real;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_num_children;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_true;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_is_bitvector;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_of_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_xor;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Table;
import com.google.common.primitives.Ints;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2BitvectorFormula;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2BooleanFormula;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2IntegerFormula;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2RationalFormula;

public class Yices2FormulaCreator extends FormulaCreator<Integer, Integer, Long, Integer> {

  private static final ImmutableSet<Integer> CONSTANT_AND_VARIABLE_CONSTRUCTORS =
      ImmutableSet.of(
          YICES_BOOL_CONST,
          YICES_ARITH_CONST,
          YICES_BV_CONST,
          YICES_VARIABLE,
          YICES_UNINTERPRETED_TERM);

  /**
   * Maps a name and a free variable or function type to a concrete formula node. We allow only 1
   * type per var name, meaning there is only 1 column per row!
   */
  private final Table<String, Integer, Integer> formulaCache = HashBasedTable.create();

  protected Yices2FormulaCreator() {
    super(null, yices_bool_type(), yices_int_type(), yices_real_type(), null, null);
  }

  @Override
  public Integer getBitvectorType(int pBitwidth) {
    return yices_bv_type(pBitwidth);
  }

  @Override
  public Integer getFloatingPointType(FloatingPointType pType) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Integer getArrayType(Integer pIndexType, Integer pElementType) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Integer makeVariable(Integer pType, String pVarName) {
    return createNamedVariable(pType, pVarName);
  }

  public Integer makeVariable(Integer pTerm) {
    return makeVariable(yices_type_of_term(pTerm), yices_get_term_name(pTerm));
  }

  @Override
  public Integer extractInfo(Formula pT) {
    return Yices2FormulaManager.getYicesTerm(pT);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Integer pTerm) {
    // INTEGER is basic type and also used for function applications like EXTRACT/EXPAND.
    // RATIONAL can be used to model INTEGERS. Otherwise, the type should match exactly.
    assert FormulaType.IntegerType.equals(pType)
            || (FormulaType.RationalType.equals(pType)
                && FormulaType.IntegerType.equals(getFormulaType(pTerm)))
            || pType.equals(getFormulaType(pTerm))
        : String.format(
            "Trying to encapsulate formula %s of type %s as %s",
            yices_term_to_string(pTerm), getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new Yices2BooleanFormula(pTerm);
    } else if (pType.isIntegerType()) {
      return (T) new Yices2IntegerFormula(pTerm);
    } else if (pType.isRationalType()) {
      return (T) new Yices2RationalFormula(pTerm);
    } else if (pType.isBitvectorType()) {
      return (T) new Yices2BitvectorFormula(pTerm);
    }
    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in Yices");
  }

  @Override
  public BooleanFormula encapsulateBoolean(Integer pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new Yices2BooleanFormula(pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Integer pTerm) {
    assert getFormulaType(pTerm).isBitvectorType();
    return new Yices2BitvectorFormula(pTerm);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    if (pFormula instanceof BitvectorFormula) {
      int type = yices_type_of_term(extractInfo(pFormula));
      return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize(yices_bvtype_size(type));
    } else {
      return super.getFormulaType(pFormula);
    }
  }

  @Override
  public FormulaType<?> getFormulaType(Integer pFormula) {
    if (yices_term_is_bool(pFormula)) {
      return FormulaType.BooleanType;
    } else if (yices_term_is_int(pFormula)) {
      return FormulaType.IntegerType;
    } else if (yices_term_is_real(pFormula)) {
      return FormulaType.RationalType;
    } else if (yices_term_is_bitvector(pFormula)) {
      return FormulaType.getBitvectorTypeWithSize(yices_term_bitsize(pFormula));
    }
    throw new IllegalArgumentException(
        String.format(
            "Unknown formula type '%s' for formula '%s'",
            yices_type_to_string(yices_type_of_term(pFormula)), yices_term_to_string(pFormula)));
  }

  /** Creates a named, free variable. Might retrieve it from the cache if created prior. */
  protected int createNamedVariable(int type, String name) {
    Integer maybeFormula = formulaCache.get(name, type);
    if (maybeFormula != null) {
      return maybeFormula;
    }
    if (formulaCache.containsRow(name)) {
      throw new IllegalArgumentException(
          "Symbol " + name + " already used for a variable of type " + formulaCache.row(name));
    }
    int var = yices_new_uninterpreted_term(type);
    // Names in Yices2 behave like a stack. The last variable named is retrieved when asking for
    // a term with a specific name. Since we substitute free vars with bound for quantifiers,
    // this sometimes mixes them up, hence we track them ourselves.
    yices_set_term_name(var, name);
    formulaCache.put(name, type, var);
    return var;
  }

  protected int createBoundVariableFromFreeVariable(int unboundVar) {
    int type = yices_type_of_term(unboundVar);
    String name = yices_get_term_name(unboundVar);

    int termFromName = yices_get_term_by_name(name);
    if (termFromName != -1) {
      int termFromNameType = yices_type_of_term(termFromName);
      if (type == termFromNameType) {
        int constructor = yices_term_constructor(termFromName);
        if (constructor == YICES_VARIABLE) {
          // Already a bound var
          return termFromName;
        }
      } else {
        throw new IllegalArgumentException(
            String.format(
                "Can't create variable with name '%s' and type '%s' "
                    + "as it would omit a variable with type '%s'",
                name, yices_type_to_string(type), yices_type_to_string(termFromNameType)));
      }
    }
    // reset term name binding
    // TODO: add yices_remove_term_name();
    int bound = yices_new_variable(type);
    // Names in Yices2 behave like a stack. The last variable named is retrieved when asking for
    // a term with a specific name. Since we substitute free vars with bound for quantifiers,
    // this sometimes mixes them up, hence we track them ourselves.
    // This overrides the naming, but the old is cached.
    // Meaning that if we remove the new name, the old term gets its name back.
    // Since we just want to retrieve the same var for the quantifier we are currently building,
    // this is fine.
    yices_set_term_name(bound, name);
    return bound;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> pVisitor, Formula pFormula, Integer pF) throws IOException {
    int constructor = yices_term_constructor(pF);
    switch (constructor) {
      case YICES_BOOL_CONST:
        return pVisitor.visitConstant(pFormula, yices_bool_const_value(pF));
      case YICES_ARITH_CONST:
        return pVisitor.visitConstant(pFormula, convertValue(pF, pF));
      case YICES_BV_CONST:
        return pVisitor.visitConstant(pFormula, convertValue(pF, pF));
      case YICES_UNINTERPRETED_TERM:
        return pVisitor.visitFreeVariable(pFormula, yices_get_term_name(pF));
      case YICES_VARIABLE:
        return pVisitor.visitBoundVariable(pFormula, 0);
      case YICES_FORALL_TERM:
        int children = yices_term_num_children(pF);
        ImmutableList.Builder<Formula> boundVars = ImmutableList.builder();
        for (int i = 0; i < children - 1; i++) {
          int boundVar = yices_term_child(pF, i);
          boundVars.add(encapsulateWithTypeOf(boundVar));
        }
        BooleanFormula body = encapsulateBoolean(yices_term_child(pF, children - 1));
        Quantifier quant = Quantifier.EXISTS;
        if (yices_term_to_string(pF).startsWith("(forall")) {
          // TODO: this is stupid, but i could not find a way of discerning between the quantifiers
          quant = Quantifier.FORALL;
        }
        return pVisitor.visitQuantifier((BooleanFormula) pFormula, quant, boundVars.build(), body);
      default:
        return visitFunctionApplication(pVisitor, pFormula, pF, constructor);
    }
  }

  private <R> R visitFunctionApplication(
      FormulaVisitor<R> pVisitor, Formula pFormula, int pF, final int constructor) {

    // Map built-in constructors in negative int to avoid collision with UFs.
    int functionDeclaration = -constructor;

    assert !CONSTANT_AND_VARIABLE_CONSTRUCTORS.contains(constructor)
        : String.format(
            "Term %s with constructor %d should be handled somewhere else",
            yices_term_to_string(pF), constructor);

    // filled later, except for some special function applications
    String functionName = null;
    List<Integer> functionArgs = null;

    // filled directly when handling the function application
    final FunctionDeclarationKind functionKind;

    switch (constructor) {
      case YICES_ITE_TERM:
        functionKind = FunctionDeclarationKind.ITE;
        break;
      case YICES_APP_TERM:
        functionKind = FunctionDeclarationKind.UF;
        functionArgs = getArgs(pF);
        functionName = yices_term_to_string(functionArgs.get(0));
        functionDeclaration = functionArgs.get(0);
        functionArgs.remove(0);
        break;
      case YICES_EQ_TERM:
        functionKind = FunctionDeclarationKind.EQ; // Covers all equivalences
        break;
      case YICES_NOT_TERM:
        if (isNestedConjunction(pF)) {
          functionKind = FunctionDeclarationKind.AND;
          functionArgs = getNestedConjunctionArgs(pF);
          functionDeclaration = -YICES_AND;
        } else {
          functionKind = FunctionDeclarationKind.NOT;
        }
        break;
      case YICES_OR_TERM:
        functionKind = FunctionDeclarationKind.OR;
        break;
      case YICES_XOR_TERM:
        functionKind = FunctionDeclarationKind.XOR;
        break;
      case YICES_BV_DIV:
        functionKind = FunctionDeclarationKind.BV_UDIV;
        break;
      case YICES_BV_REM:
        functionKind = FunctionDeclarationKind.BV_UREM;
        break;
      case YICES_BV_SDIV:
        functionKind = FunctionDeclarationKind.BV_SDIV;
        break;
      case YICES_BV_SREM:
        functionKind = FunctionDeclarationKind.BV_SREM;
        break;
      case YICES_BV_SMOD:
        functionKind = FunctionDeclarationKind.BV_SMOD;
        break;
      case YICES_BV_SHL:
        functionKind = FunctionDeclarationKind.BV_SHL;
        break;
      case YICES_BV_LSHR:
        functionKind = FunctionDeclarationKind.BV_LSHR;
        break;
      case YICES_BV_ASHR:
        functionKind = FunctionDeclarationKind.BV_ASHR;
        break;
      case YICES_BV_GE_ATOM:
        functionKind = FunctionDeclarationKind.BV_UGE;
        break;
      case YICES_BV_SGE_ATOM:
        functionKind = FunctionDeclarationKind.BV_SGE;
        break;
      case YICES_ARITH_GE_ATOM:
        functionKind = FunctionDeclarationKind.GTE;
        break;
      case YICES_FLOOR:
        functionKind = FunctionDeclarationKind.FLOOR;
        break;
      case YICES_RDIV:
        functionKind = FunctionDeclarationKind.DIV;
        break;
      case YICES_IDIV:
        functionKind = FunctionDeclarationKind.DIV;
        break;
      case YICES_SELECT_TERM:
        functionKind = FunctionDeclarationKind.SELECT;
        break;
      case YICES_BV_SUM:
        if (yices_term_num_children(pF) == 1) {
          functionKind = FunctionDeclarationKind.BV_MUL;
          functionArgs = getMultiplyBvSumArgsFromSum(pF);
          functionDeclaration = -YICES_BV_MUL;
        } else {
          functionKind = FunctionDeclarationKind.BV_ADD;
          functionArgs = getBvSumArgs(pF);
        }
        break;
      case YICES_ARITH_SUM:
        if (yices_term_num_children(pF) == 1) {
          functionKind = FunctionDeclarationKind.MUL;
          functionArgs = getMultiplySumArgsFromSum(pF);
          functionDeclaration = -YICES_POWER_PRODUCT;
        } else {
          functionKind = FunctionDeclarationKind.ADD;
          functionArgs = getSumArgs(pF);
        }
        break;
      case YICES_POWER_PRODUCT:
        if (yices_type_is_bitvector(yices_type_of_term(pF))) {
          functionKind = FunctionDeclarationKind.BV_MUL;
          functionArgs = getMultiplyArgs(pF, true);
          functionDeclaration = -YICES_BV_MUL;
          // TODO Product of more then 2 bitvectors ?
        } else {
          functionKind = FunctionDeclarationKind.MUL;
          functionArgs = getMultiplyArgs(pF, false);
        }
        break;
      case YICES_BIT_TERM:
        functionKind = FunctionDeclarationKind.BV_EXTRACT;
        functionArgs = getBitArgs(pF);
        break;
      case YICES_BV_ARRAY:
        functionKind = FunctionDeclarationKind.BV_CONCAT;
        break;
      default:
        functionKind = FunctionDeclarationKind.OTHER;
    }

    if (functionName == null) {
      functionName = functionKind.toString();
    }
    if (functionArgs == null) {
      functionArgs = getArgs(pF);
    }

    final ImmutableList<FormulaType<?>> argTypes = ImmutableList.copyOf(toType(functionArgs));

    Preconditions.checkState(
        functionArgs.size() == argTypes.size(),
        "different size of args (%s) and their types (%s) in term %s",
        functionArgs,
        argTypes,
        pFormula);

    final ImmutableList.Builder<Formula> argsBuilder = ImmutableList.builder();
    for (int i = 0; i < functionArgs.size(); i++) {
      argsBuilder.add(encapsulate(argTypes.get(i), functionArgs.get(i)));
    }
    final ImmutableList<Formula> args = argsBuilder.build();

    return pVisitor.visitFunction(
        pFormula,
        args,
        FunctionDeclarationImpl.of(
            functionName, functionKind, argTypes, getFormulaType(pF), functionDeclaration));
  }

  private List<FormulaType<?>> toType(final List<Integer> args) {
    return Lists.transform(args, this::getFormulaType);
  }

  /** Yices transforms <code>AND(x,...)</code> into <code>NOT(OR(NOT(X),NOT(...))</code>. */
  private static boolean isNestedConjunction(int outerTerm) {
    if (yices_term_constructor(outerTerm) != YICES_NOT_TERM) {
      return false;
    }

    int middleTerm = yices_term_child(outerTerm, 0);
    if (yices_term_constructor(middleTerm) != YICES_OR_TERM) {
      return false;
    }

    // code commented out --> ignore nested NOTs and just negate all resulting child-terms.
    // for (int child : getArgs(middleTerm)) {
    //   if (yices_term_constructor(child) != YICES_NOT_TERM) {
    //     return false;
    //   }
    // }

    return true;
  }

  /**
   * Yices transforms <code>AND(x,...)</code> into <code>NOT(OR(NOT(X),NOT(...))</code>.
   *
   * <p>Only call this method for terms that are nested conjunctions!
   */
  private static List<Integer> getNestedConjunctionArgs(int outerTerm) {
    Preconditions.checkArgument(yices_term_constructor(outerTerm) == YICES_NOT_TERM);
    int middleTerm = yices_term_child(outerTerm, 0);
    Preconditions.checkArgument(yices_term_constructor(middleTerm) == YICES_OR_TERM);
    List<Integer> result = new ArrayList<>();
    for (int child : getArgs(middleTerm)) {
      result.add(yices_not(child));
    }
    return result;
  }

  private static List<Integer> getArgs(int parent) {
    try {
      return getArgs0(parent);
    } catch (IllegalArgumentException e) {
      throw new IllegalArgumentException("problematic term: " + yices_term_to_string(parent), e);
    }
  }

  private static List<Integer> getArgs0(int parent) {
    List<Integer> children = new ArrayList<>();
    for (int i = 0; i < yices_term_num_children(parent); i++) {
      children.add(yices_term_child(parent, i));
    }
    return children;
  }

  private static List<Integer> getSumArgs(int parent) {
    List<Integer> children = new ArrayList<>();
    for (int i = 0; i < yices_term_num_children(parent); i++) {
      String[] child = yices_sum_component(parent, i);
      String coeff = child[0];
      int term = Integer.parseInt(child[1]);
      if (term == -1) { // No term just a number
        children.add(yices_parse_rational(coeff));
      } else {
        int coeffTerm = yices_parse_rational(coeff);
        children.add(yices_mul(coeffTerm, term));
      }
    }
    return children;
  }

  /** extract all entries of a BV sum like "3*x + 2*y + 1". */
  private static List<Integer> getBvSumArgs(int parent) {
    List<Integer> children = new ArrayList<>();
    int bitsize = yices_term_bitsize(parent);
    for (int i = 0; i < yices_term_num_children(parent); i++) {
      int[] component = yices_bvsum_component(parent, i, bitsize);
      assert component.length == bitsize + 1;
      // the components consist of coefficient (as bits) and variable (if missing: -1)
      int coeff = yices_bvconst_from_array(bitsize, Arrays.copyOfRange(component, 0, bitsize));
      int term = component[component.length - 1];
      if (term == -1) { // No term
        children.add(coeff);
      } else {
        children.add(yices_bvmul(coeff, term));
      }
    }
    return children;
  }

  /** extract -1 and X from the sum of one element [-1*x]. */
  private static List<Integer> getMultiplyBvSumArgsFromSum(int parent) {
    Preconditions.checkArgument(yices_term_num_children(parent) == 1);
    int bitsize = yices_term_bitsize(parent);
    int[] component = yices_bvsum_component(parent, 0, bitsize);
    int coeff = yices_bvconst_from_array(bitsize, Arrays.copyOfRange(component, 0, bitsize));
    int term = component[component.length - 1];
    Preconditions.checkArgument(term != -1, "unexpected constant coeff without variable");
    return ImmutableList.of(coeff, term);
  }

  /** extract -1 and X from the sum of one element [-1*x]. */
  private static List<Integer> getMultiplySumArgsFromSum(int parent) {
    Preconditions.checkArgument(yices_term_num_children(parent) == 1);
    String[] child = yices_sum_component(parent, 0);
    int term = Integer.parseInt(child[1]);
    Preconditions.checkArgument(term != -1, "unexpected constant coeff without variable");
    int coeffTerm = yices_parse_rational(child[0]);
    return ImmutableList.of(coeffTerm, term);
  }

  private static List<Integer> getMultiplyArgs(int parent, boolean isBV) {
    // TODO Add exponent?
    List<Integer> result = new ArrayList<>();
    for (int i = 0; i < yices_term_num_children(parent); i++) {
      int[] component = yices_product_component(parent, i);
      if (isBV) {
        result.add(yices_bvpower(component[0], component[1]));
      } else {
        result.add(yices_power(component[0], component[1])); // add term, ignore exponent
      }
    }
    return result;
  }

  /** get "index" and "b" from "(bit index b)". */
  private static List<Integer> getBitArgs(int parent) {
    return ImmutableList.of(yices_proj_arg(parent), yices_int32(yices_proj_index(parent)));
  }

  @Override
  public Integer callFunctionImpl(Integer pDeclaration, List<Integer> pArgs) {
    if (pDeclaration < 0) { // is constant function application from API
      switch (-pDeclaration) {
        case YICES_ITE_TERM:
          checkArgsLength("YICES_ITE_TERM", pArgs, 3);
          return yices_ite(pArgs.get(0), pArgs.get(1), pArgs.get(2));
        case YICES_EQ_TERM:
          checkArgsLength("YICES_EQ_TERM", pArgs, 2);
          return yices_eq(pArgs.get(0), pArgs.get(1));
        case YICES_DISTINCT_TERM:
          return yices_distinct(pArgs.size(), Ints.toArray(pArgs));
        case YICES_NOT_TERM:
          checkArgsLength("YICES_NOT_TERM", pArgs, 1);
          return yices_not(pArgs.get(0));
        case YICES_OR_TERM:
          return yices_or(pArgs.size(), Ints.toArray(pArgs));
        case YICES_XOR_TERM:
          return yices_xor(pArgs.size(), Ints.toArray(pArgs));
        case YICES_BV_DIV:
          checkArgsLength("YICES_BV_DIV", pArgs, 2);
          return yices_bvdiv(pArgs.get(0), pArgs.get(1));
        case YICES_BV_REM:
          checkArgsLength("YICES_BV_REM", pArgs, 2);
          return yices_bvrem(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SDIV:
          checkArgsLength("YICES_BV_SDIV", pArgs, 2);
          return yices_bvsdiv(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SREM:
          checkArgsLength("YICES_BV_SREM", pArgs, 2);
          return yices_bvsrem(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SMOD:
          checkArgsLength("YICES_BV_SMOD", pArgs, 2);
          return yices_bvsmod(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SHL:
          checkArgsLength("YICES_BV_SHL", pArgs, 2);
          return yices_bvshl(pArgs.get(0), pArgs.get(1));
        case YICES_BV_LSHR:
          checkArgsLength("YICES_BV_LSHR", pArgs, 2);
          return yices_bvlshr(pArgs.get(0), pArgs.get(1));
        case YICES_BV_ASHR:
          checkArgsLength("YICES_BV_ASHR", pArgs, 2);
          return yices_bvashr(pArgs.get(0), pArgs.get(1));
        case YICES_BV_GE_ATOM:
          checkArgsLength("YICES_BV_GE_ATOM", pArgs, 2);
          return yices_bvge_atom(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SGE_ATOM:
          checkArgsLength("YICES_BV_SGE_ATOM", pArgs, 2);
          return yices_bvsge_atom(pArgs.get(0), pArgs.get(1));
        case YICES_ARITH_GE_ATOM:
          checkArgsLength("YICES_ARITH_GE_ATOM", pArgs, 2);
          return yices_arith_geq_atom(pArgs.get(0), pArgs.get(1));
        case YICES_ABS:
          checkArgsLength("YICES_ABS", pArgs, 1);
          return yices_abs(pArgs.get(0));
        case YICES_CEIL:
          checkArgsLength("YICES_CEIL", pArgs, 1);
          return yices_ceil(pArgs.get(0));
        case YICES_FLOOR:
          checkArgsLength("YICES_FLOOR", pArgs, 1);
          return yices_floor(pArgs.get(0));
        case YICES_RDIV:
          checkArgsLength("YICES_RDIV", pArgs, 2);
          return yices_division(pArgs.get(0), pArgs.get(1));
        case YICES_IDIV:
          checkArgsLength("YICES_IDIV", pArgs, 2);
          return yices_idiv(pArgs.get(0), pArgs.get(1));
        case YICES_IMOD:
          checkArgsLength("YICES_IMOD", pArgs, 2);
          return yices_imod(pArgs.get(0), pArgs.get(1));
        case YICES_IS_INT_ATOM:
          checkArgsLength("YICES_IS_INT_ATOM", pArgs, 1);
          return yices_is_int_atom(pArgs.get(0));
        case YICES_DIVIDES_ATOM:
          checkArgsLength("YICES_DIVIDES_ATOM", pArgs, 2);
          return yices_divides_atom(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SUM:
          return yices_bvsum(pArgs.size(), Ints.toArray(pArgs));
        case YICES_ARITH_SUM:
          return yices_sum(pArgs.size(), Ints.toArray(pArgs));
        case YICES_POWER_PRODUCT:
          return yices_product(pArgs.size(), Ints.toArray(pArgs));
        case YICES_BIT_TERM:
          checkArgsLength("YICES_BIT_TERM", pArgs, 2);
          return yices_bitextract(pArgs.get(0), toInt(pArgs.get(1)));
        case YICES_BV_ARRAY:
          return yices_bvarray(pArgs.size(), Ints.toArray(pArgs));
        case YICES_BV_MUL:
          return yices_bvproduct(pArgs.size(), Ints.toArray(pArgs));
        case YICES_AND:
          return yices_and(pArgs.size(), Ints.toArray(pArgs));
        default:
          // TODO add more cases
          // if something bad happens here,
          // in most cases the solution is a fix in the method visitFunctionApplication
          throw new IllegalArgumentException(
              String.format(
                  "Unknown function declaration with constructor %d and arguments %s (%s)",
                  -pDeclaration,
                  pArgs,
                  Lists.transform(pArgs, Yices2NativeApi::yices_term_to_string)));
      }
    } else { // is UF Application
      if (pArgs.isEmpty()) {
        return pDeclaration;
      } else {
        int[] argArray = Ints.toArray(pArgs);
        int app = yices_application(pDeclaration, argArray.length, argArray);
        return app;
      }
    }
  }

  private int toInt(int termId) {
    assert yices_term_is_int(termId);
    return Integer.parseInt(yices_rational_const_value(termId));
  }

  private void checkArgsLength(String kind, List<Integer> pArgs, final int expectedLength) {
    Preconditions.checkArgument(
        pArgs.size() == expectedLength,
        "%s with %s expected arguments was called with unexpected arguments: %s",
        kind,
        expectedLength,
        Collections2.transform(pArgs, Yices2NativeApi::yices_term_to_string));
  }

  @Override
  public Integer declareUFImpl(String pName, Integer pReturnType, List<Integer> pArgTypes) {
    int size = pArgTypes.size();
    int[] argTypeArray = Ints.toArray(pArgTypes);
    final int yicesFuncType;
    if (pArgTypes.isEmpty()) {
      // a nullary function is a plain symbol (variable)
      yicesFuncType = pReturnType;
    } else {
      yicesFuncType = yices_function_type(size, argTypeArray, pReturnType);
    }
    int uf = createNamedVariable(yicesFuncType, pName);
    return uf;
  }

  @Override
  protected Integer getBooleanVarDeclarationImpl(Integer pTFormulaInfo) {
    return yices_term_constructor(pTFormulaInfo);
  }

  private Object parseNumeralValue(Integer pF, FormulaType<?> type) {
    if (yices_term_constructor(pF) == YICES_ARITH_CONST) {
      String value = yices_rational_const_value(pF);
      if (type.isRationalType()) {
        Rational ratValue = Rational.of(value);
        return ratValue.isIntegral() ? ratValue.getNum() : ratValue;
      } else if (type.isIntegerType()) {
        return new BigInteger(value);
      } else {
        throw new IllegalArgumentException("Unexpected type: " + type);
      }
    } else {
      throw new IllegalArgumentException(
          String.format(
              "Term: '%s' with type '%s' is not an arithmetic constant",
              yices_term_to_string(pF), yices_type_to_string(yices_type_of_term(pF))));
    }
  }

  private BigInteger parseBitvector(int pF) {
    if (yices_term_constructor(pF) == YICES_BV_CONST) {
      int[] littleEndianBV = yices_bv_const_value(pF, yices_term_bitsize(pF));
      Preconditions.checkArgument(littleEndianBV.length != 0, "BV was empty");
      String bigEndianBV = Joiner.on("").join(Lists.reverse(Ints.asList(littleEndianBV)));
      return new BigInteger(bigEndianBV, 2);
    } else {
      throw new IllegalArgumentException(
          String.format("Term: '%s' is not a bitvector constant", yices_term_to_string(pF)));
    }
  }

  @Override
  public Object convertValue(Integer typeKey, Integer pF) {
    FormulaType<?> type = getFormulaType(typeKey);
    if (type.isBooleanType()) {
      return pF.equals(yices_true());
    } else if (type.isRationalType() || type.isIntegerType()) {
      return parseNumeralValue(pF, type);
    } else if (type.isBitvectorType()) {
      return parseBitvector(pF);
    } else {
      throw new IllegalArgumentException(
          "Unexpected type: " + yices_type_to_string(yices_type_of_term(pF)));
    }
  }
}
