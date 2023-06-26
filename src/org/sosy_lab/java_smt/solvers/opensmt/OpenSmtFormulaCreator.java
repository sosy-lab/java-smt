// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import opensmt.ArithLogic;
import opensmt.Logic;
import opensmt.OpenSmt;
import opensmt.PTRef;
import opensmt.SRef;
import opensmt.SymRef;
import opensmt.VectorPTRef;
import opensmt.VectorSRef;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtFormula.OpenSmtArrayFormula;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtFormula.OpenSmtBooleanFormula;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtFormula.OpenSmtIntegerFormula;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtFormula.OpenSmtRationalFormula;

public class OpenSmtFormulaCreator extends FormulaCreator<PTRef, SRef, OpenSmt, SymRef> {

  protected final Logic osmtLogic;

  OpenSmtFormulaCreator(OpenSmt solver) {
    // FIXME: We need srefs that are independant of the logic. Map to sref_undef if the sort is not
    // supported?
    super(
        solver,
        solver.getLogic().getSort_bool(),
        solver.getLRALogic().getSort_int(),
        solver.getLRALogic().getSort_real(),
        null,
        null);
    osmtLogic = solver.getLogic();
  }

  @Override
  public PTRef extractInfo(Formula pT) {
    OpenSmtFormula osmtFormula = (OpenSmtFormula) pT;
    return osmtFormula.getOsmtTerm();
  }

  @Override
  public PTRef callFunctionImpl(SymRef declaration, List<PTRef> args) {
    return getEnv().getLogic().insertTerm(declaration, new VectorPTRef(args));
  }

  @Override
  public SymRef declareUFImpl(String pName, SRef pReturnType, List<SRef> pArgTypes) {
    return getEnv().getLogic().declareFun(pName, pReturnType, new VectorSRef(pArgTypes));
  }

  // FIXME: This is a bit of a hack. OpenSmt has no way of accessing the element and index types
  // of an array. We just store them here for now. Maybe there's a better way?
  private Map<SRef, SRef> arrayIndexTypes = new HashMap<SRef, SRef>();
  private Map<SRef, SRef> arrayElementTypes = new HashMap<SRef, SRef>();

  @Override
  public SRef getArrayType(SRef indexType, SRef elementType) {
    SRef array = getEnv().getLogic().getArraySort(indexType, elementType);
    arrayIndexTypes.put(array, indexType);
    arrayElementTypes.put(array, elementType);
    return array;
  }

  @Override
  public SRef getBitvectorType(int bitwidth) {
    throw new UnsupportedOperationException("OpenSMT does not support bitvectors.");
  }

  @Override
  public SymRef getBooleanVarDeclarationImpl(PTRef pPTRef) {
    return getEnv().getLogic().getSymRef(pPTRef);
  }

  @Override
  public SRef getFloatingPointType(FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException("OpenSMT does not support floating point operations.");
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> FormulaType<TD> getArrayFormulaIndexType(
      ArrayFormula<TD, TR> pArray) {
    OpenSmtArrayFormula<TD, TR> array = (OpenSmtArrayFormula<TD, TR>) pArray;
    return array.getIndexType();
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> FormulaType<TR> getArrayFormulaElementType(
      ArrayFormula<TD, TR> pArray) {
    OpenSmtArrayFormula<TD, TR> array = (OpenSmtArrayFormula<TD, TR>) pArray;
    return array.getElementType();
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    if (pFormula instanceof ArrayFormula<?, ?>) {
      FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
      FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public FormulaType<?> getFormulaType(PTRef pFormula) {
    SRef sort = getEnv().getLogic().getSortRef(pFormula);
    return getFormulaTypeFromTermType(sort);
  }

  private FormulaType<?> getFormulaTypeFromTermType(SRef sort) {
    Logic logic = getEnv().getLogic();
    if (logic.isSortBool(sort)) {
      return FormulaType.BooleanType;
    }
    if (logic.isArraySort(sort)) {
      FormulaType<?> indexType = getFormulaTypeFromTermType(arrayIndexTypes.get(sort));
      FormulaType<?> elementType = getFormulaTypeFromTermType(arrayElementTypes.get(sort));
      return FormulaType.getArrayType(indexType, elementType);
    }
    ArithLogic alogic = getEnv().getLRALogic();
    if (alogic.isSortInt(sort)) {
      return FormulaType.IntegerType;
    }
    if (alogic.isSortReal(sort)) {
      return FormulaType.RationalType;
    }
    throw new AssertionError(String.format("Encountered unhandled Type '%s'.", sort));
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, PTRef pTerm) {
    assert pType.equals(getFormulaType(pTerm))
            || (pType.equals(FormulaType.RationalType)
                && getFormulaType(pTerm).equals(FormulaType.IntegerType))
        : String.format(
            "Cannot encapsulate formula %s of Type %s as %s", pTerm, getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new OpenSmtBooleanFormula(osmtLogic, pTerm);
    }
    if (pType.isIntegerType()) {
      return (T) new OpenSmtIntegerFormula(osmtLogic, pTerm);
    }
    if (pType.isRationalType()) {
      return (T) new OpenSmtRationalFormula(osmtLogic, pTerm);
    }
    if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T)
          new OpenSmtArrayFormula<>(osmtLogic, pTerm, arrFt.getIndexType(), arrFt.getElementType());
    }
    throw new IllegalArgumentException("Cannot create formulas of Type " + pType + " in OpenSMT");
  }

  public Formula encapsulate(PTRef pTerm) {
    return encapsulate(getFormulaType(pTerm), pTerm);
  }

  @Override
  public BooleanFormula encapsulateBoolean(PTRef pTerm) {
    assert getFormulaType(pTerm).isBooleanType()
        : String.format(
            "%s is not boolean, but %s (%s)",
            pTerm, osmtLogic.getSortRef(pTerm), getFormulaType(pTerm));
    return new OpenSmtBooleanFormula(osmtLogic, pTerm);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      PTRef pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType))
        : String.format(
            "%s is no array, but %s (%s)",
            pTerm, osmtLogic.getSortRef(pTerm), getFormulaType(pTerm));
    return new OpenSmtArrayFormula<>(osmtLogic, pTerm, pIndexType, pElementType);
  }

  @Override
  public PTRef makeVariable(SRef type, String varName) {
    return getEnv().getLogic().mkVar(type, varName);
  }

  @SuppressWarnings("unused")
  private FunctionDeclarationKind getDeclarationKind(PTRef f) {
    Logic logic = getEnv().getLogic();
    /*
    AND
    IFF        If and only if.
    IMPLIES    Implication between two boolean formulas.
    ITE        If-then-else operator.
    NOT
    OR
    SELECT
    STORE 	Store and select on arrays.
    UF 	        Uninterpreted function.
    XOR 	Exclusive OR over two formulas.
    */

    if (logic.isAnd(f)) {
      return FunctionDeclarationKind.AND;
    }
    if (logic.isIff(f)) {
      return FunctionDeclarationKind.IFF;
    }
    if (logic.isImplies(f)) {
      return FunctionDeclarationKind.IMPLIES;
    }
    if (logic.isIte(f)) {
      return FunctionDeclarationKind.ITE;
    }
    if (logic.isNot(f)) {
      return FunctionDeclarationKind.NOT;
    }
    if (logic.isOr(f)) {
      return FunctionDeclarationKind.OR;
    }
    if (logic.isArraySelect(f)) {
      return FunctionDeclarationKind.SELECT;
    }
    if (logic.isArrayStore(f)) {
      return FunctionDeclarationKind.STORE;
    }
    if (logic.isUF(f)) {
      return FunctionDeclarationKind.UF;
    }
    if (logic.isXor(f)) {
      return FunctionDeclarationKind.XOR;
    }

    ArithLogic alogic = getEnv().getLRALogic();
    /*
    ADD        Addition over integers and rationals.
    DISTINCT   Distinct operator for a set of numeric formulas.
    DIV        Division over rationals and integer division over integers.
    EQ         Equality over integers and rationals.
    GT         Greater-than over integers and rationals.
    GTE        Greater-than-or-equal over integers and rationals.
    LT 	       Less-than over integers and rationals.
    LTE        Less-than-or-equal over integers and rationals.
    MODULO     Modulo operator over integers.
    MUL        Multiplication over integers and rationals.
    SUB        Subtraction over integers and rationals.
    UMINUS     Unary minus.
    */

    if (alogic.isPlus(f)) {
      return FunctionDeclarationKind.ADD;
    }
    if (alogic.isDisequality(f)) {
      return FunctionDeclarationKind.DISTINCT;
    }
    if (alogic.isDiv(f)) {
      return FunctionDeclarationKind.DIV;
    }
    if (alogic.isEquality(f)) {
      return FunctionDeclarationKind.EQ;
    }
    if (alogic.isGeq(f)) {
      return FunctionDeclarationKind.GT;
    }
    if (alogic.isGt(f)) {
      return FunctionDeclarationKind.GTE;
    }
    if (alogic.isLeq(f)) {
      return FunctionDeclarationKind.LT;
    }
    if (alogic.isLt(f)) {
      return FunctionDeclarationKind.LTE;
    }
    if (alogic.isMod(f)) {
      return FunctionDeclarationKind.MODULO;
    }
    if (alogic.isTimes(f)) {
      return FunctionDeclarationKind.MUL;
    }
    if (alogic.isMinus(f)) {
      return FunctionDeclarationKind.SUB;
    }
    if (alogic.isNeg(f)) {
      return FunctionDeclarationKind.UMINUS;
    }

    throw new UnsupportedOperationException("Encountered unsupported declaration kind");
  }

  @Override
  public Object convertValue(PTRef value) {
    Logic logic = getEnv().getLogic();
    if (logic.isTrue(value)) {
      return Boolean.TRUE;
    }
    if (logic.isFalse(value)) {
      return Boolean.FALSE;
    }

    ArithLogic alogic = getEnv().getLRALogic();
    if (alogic.isIntConst(value)) {
      return new BigInteger(alogic.getNumConst(value));
    }
    if (alogic.isRealConst(value)) {
      Rational ratValue = Rational.ofString(alogic.getNumConst(value));
      return ratValue.isIntegral() ? ratValue.getNum() : ratValue;
    }

    throw new UnsupportedOperationException("Term `" + logic.pp(value) + "` is not a value");
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, PTRef f) {
    Logic logic = getEnv().getLogic();

    if (logic.isConstant(f)) {
      return visitor.visitConstant(formula, convertValue(f));
    }
    if (logic.isVar(f)) {
      return visitor.visitFreeVariable(formula, dequote(logic.getSymName(f)));
    }

    // FIXME: Handle abstract values for arrays?

    VectorPTRef subterms = logic.getSubterms(f);

    ImmutableList.Builder<Formula> argTerms = ImmutableList.builder();
    ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();

    for (PTRef sub : subterms) {
      argTerms.add(encapsulate(sub));
      argTypes.add(getFormulaType(sub));
    }

    return visitor.visitFunction(
        formula,
        argTerms.build(),
        FunctionDeclarationImpl.of(
            logic.getSymName(f),
            getDeclarationKind(f),
            argTypes.build(),
            getFormulaType(f),
            logic.getSymRef(f)));
  }
}
