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

package org.sosy_lab.java_smt.solvers.dreal4;
import static java.lang.Double.parseDouble;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.dreal4.DReal4Formula.DReal4BooleanFormula;
import org.sosy_lab.java_smt.solvers.dreal4.DReal4Formula.DReal4IntegerFormula;
import org.sosy_lab.java_smt.solvers.dreal4.DReal4Formula.DReal4RationalFormula;

import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionDoubleMap;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionExpressionMap;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaSet;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;


public class DReal4FormulaCreator extends FormulaCreator<DRealTerm, Type, Context,
    DRealTerm> {

  public DReal4FormulaCreator(Context context) {
    super(context, Type.BOOLEAN, Type.INTEGER, Type.CONTINUOUS, null, null);
  }

  @Override
  public Type getBitvectorType(int bitwidth) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Type getFloatingPointType(FloatingPointType type) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Type getArrayType(Type indexType, Type elementType) {
    throw new UnsupportedOperationException();
  }

  @Override
  public DRealTerm makeVariable(Type pType, String varName) {
    return new DRealTerm(new Variable(varName, pType), null, null, pType);
  }

  @Override
  public FormulaType<?> getFormulaType(DRealTerm formula) {
    if (formula.getType() == Type.BOOLEAN) {
      return FormulaType.BooleanType;
    } else if (formula.getType() == Type.INTEGER) {
      return FormulaType.IntegerType;
    } else
      return FormulaType.RationalType;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, DRealTerm pTerm) {
    assert FormulaType.IntegerType.equals(pType)
        || (FormulaType.RationalType.equals(pType)
        && FormulaType.IntegerType.equals(getFormulaType(pTerm)))
        || pType.equals(getFormulaType(pTerm))
        : String.format(
        "Trying to encapsulate formula %s of type %s as %s",
        pTerm.to_string(), getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new DReal4BooleanFormula(pTerm);
    } else if (pType.isIntegerType()) {
      return (T) new DReal4IntegerFormula(pTerm);
    } else if (pType.isRationalType()) {
      return (T) new DReal4RationalFormula(pTerm);
    }
    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in dReal.");
  }
  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, DRealTerm f) {

    FunctionDeclarationKind functionKind = null;
    List<DRealTerm> functionArgs = null;

    if (f.isVar()) {
      return visitor.visitFreeVariable(formula, f.getVariable().to_string());
    } else if (f.isExp()) {
      ExpressionKind kind = f.getExpressionKind();
      if (kind == ExpressionKind.Constant) {
        // not possible to create an Expression from a boolean Variable
        if (f.getType() == Type.INTEGER) {
          return visitor.visitConstant(formula, new BigInteger(f.getExpression().to_string()));
        } else {
          // ich habe nur double?
          //return visitor.visitConstant(formula, new );
        }
      } else if (kind == ExpressionKind.Var) {
        return visitor.visitFreeVariable(formula, f.getExpression().to_string());
      } else if (kind == ExpressionKind.IfThenElse) {
        functionKind = FunctionDeclarationKind.ITE;
        functionArgs = getExpressionFromITE(f);
      } else if (kind == ExpressionKind.Pow) {
        // this should be changed if pow is supported in JavaSMT
        functionKind = FunctionDeclarationKind.MUL;
      } else if (kind == ExpressionKind.Add){
        functionKind = FunctionDeclarationKind.ADD;
        functionArgs = getExpressionFromAdd(f);
      } else if (kind == ExpressionKind.Mul) {
        // hier muss noch was passieren
        functionKind = FunctionDeclarationKind.MUL;
        functionArgs = getExpressionFromMul(f);
      } else {
        functionKind = FunctionDeclarationKind.DIV;
        functionArgs = getExpressionsFromDiv(f);
      }
      // hier weiter geben der Expression
    } else {
      FormulaKind kind = f.getFormulaKind();
      if (kind == FormulaKind.Forall) {
        // Problem dass man an die boundVariablen nicht ran kommt -> SWIG Wrapper funktion schreiben
        throw new UnsupportedOperationException("Not supported.");
      } else if (kind == FormulaKind.And) {
        functionKind = FunctionDeclarationKind.AND;
        functionArgs = getFormulaArgs(f);
      } else if (kind == FormulaKind.Or) {
        functionKind = FunctionDeclarationKind.OR;
        functionArgs = getFormulaArgs(f);
      } else if (kind == FormulaKind.Not) {
        functionKind = FunctionDeclarationKind.NOT;
        functionArgs = getFormulaFromNot(f);
      } else if (kind == FormulaKind.Eq) {
        functionKind = FunctionDeclarationKind.EQ;
      } else if (kind == FormulaKind.Geq) {
        functionKind = FunctionDeclarationKind.GTE;
      } else if (kind == FormulaKind.Gt) {
        functionKind = FunctionDeclarationKind.GT;
      } else if (kind == FormulaKind.Leq) {
        functionKind = FunctionDeclarationKind.LT;
      } else if (kind == FormulaKind.Lt) {
        functionKind = FunctionDeclarationKind.LTE;
      } else if (kind == FormulaKind.Neq) {
        // lhs ≠ rhs -> (lhs > rhs) ∨ (lhs < rhs)
        Expression lhs = dreal.get_lhs_expression(f.getFormula());
        Expression rhs = dreal.get_rhs_expression(f.getFormula());
        DRealTerm neqTerm = new DRealTerm(null, null,
            new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(dreal.Or(dreal.Grater(lhs,
                rhs), dreal.Less(lhs, rhs))), Type.BOOLEAN);
        functionKind = FunctionDeclarationKind.OR;
        functionArgs = getFormulaArgs(neqTerm);
      } else if (kind == FormulaKind.Var) {
        return visitor.visitConstant(formula, false);
      } else if (kind == FormulaKind.True) {
        return visitor.visitConstant(formula, true);
      } else {
        return visitor.visitFreeVariable(formula, f.getFormula().to_string());
      }
    }

    String functionName = functionKind.toString();
    if (functionArgs == null) {
      functionArgs = getExpressionArgs(f);
    }

    final ImmutableList<FormulaType<?>> argTypes = ImmutableList.copyOf(toType(functionArgs));

    final ImmutableList.Builder<Formula> argsBuilder = ImmutableList.builder();
    for (int i = 0; i < functionArgs.size(); i++) {
      argsBuilder.add(encapsulate(argTypes.get(i), functionArgs.get(i)));
    }
    final ImmutableList<Formula> args = argsBuilder.build();

    return visitor.visitFunction(formula, args, FunctionDeclarationImpl.of(functionName,
        functionKind, argTypes, f.getType(), ));

  }

  private List<FormulaType<?>> toType(final List<DRealTerm> args) {
    return Lists.transform(args, this::getFormulaType);
  }

  private static List<DRealTerm> getFormulaArgs(DRealTerm pTerm) {
    List<DRealTerm> formulas = new ArrayList<>();

    if (pTerm.isFormula()) {
      FormulaSet set = dreal.get_operands(pTerm.getFormula());
      Iterator<org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula> iter = set.iterator();
      for (int i = 0; i < set.size(); i++) {
        formulas.add(new DRealTerm(null, null, iter.next(), pTerm.getType()));
      }
      return formulas;
    } else {
      throw new IllegalArgumentException("Term is not a Formula.");
    }
  }

  private static List<DRealTerm> getExpressionArgs(DRealTerm parent) {
    List<DRealTerm> children = new ArrayList<>();
    if (parent.isExp()) {
      throw new IllegalArgumentException("Term is Expression.");
    } else if (parent.isFormula()) {
      children.add(new DRealTerm(null, dreal.get_lhs_expression(parent.getFormula()), null,
          parent.getType()));
      children.add(new DRealTerm(null, dreal.get_rhs_expression(parent.getFormula()), null,
          parent.getType()));
      return children;
    } else {
      throw new IllegalArgumentException("Term is Variable.");
    }
  }

  private static List<DRealTerm> getFormulaFromNot(DRealTerm pTerm) {
    List<DRealTerm> formula = new ArrayList<>();
    if (pTerm.isVar() || pTerm.isExp()) {
      throw new IllegalArgumentException("Term is Expression or Variable.");
    } else {
      formula.add(new DRealTerm(null, null, dreal.get_operand(pTerm.getFormula()), Type.BOOLEAN));
      return formula;
    }
  }

  private static List<DRealTerm> getExpressionsFromDiv(DRealTerm pTerm) {
    List<DRealTerm> children = new ArrayList<>();
    if (pTerm.isVar() || pTerm.isExp()) {
      throw new IllegalArgumentException("Term is Variable or Expression");
    } else {
        children.add(new DRealTerm(null, dreal.get_first_argument(pTerm.getExpression()), null, pTerm.getType()));
        children.add(new DRealTerm(null, dreal.get_second_argument(pTerm.getExpression()), null,
            pTerm.getType()));
        return children;
      }
  }

  private static List<DRealTerm> getExpressionFromITE(DRealTerm pTerm) {
    List<DRealTerm> children = new ArrayList<>();
    if (pTerm.isFormula() || pTerm.isVar()) {
      throw new IllegalArgumentException("Term is Variable or Formula");
    } else {
      children.add(new DRealTerm(null, null, dreal.get_conditional_formula(pTerm.getExpression()),
          pTerm.getType()));
      children.add(new DRealTerm(null, dreal.get_then_expression(pTerm.getExpression()), null,
          pTerm.getType()));
      children.add(new DRealTerm(null, dreal.get_else_expression(pTerm.getExpression()), null,
          pTerm.getType()));
      return children;
    }
  }

  private static List<DRealTerm> getExpressionFromAdd(DRealTerm pTerm) {
    List<DRealTerm> terms = new ArrayList<>();
    if (pTerm.isVar() || pTerm.isFormula()) {
      throw new IllegalArgumentException("Term is Variable or Formula.");
    } else {
      terms.add(new DRealTerm(null, new Expression(dreal.get_constant_in_addition(pTerm.getExpression())), null,
          pTerm.getType()));
      ExpressionDoubleMap map = dreal.get_expr_to_coeff_map_in_addition(pTerm.getExpression());
      Set<Entry<Expression, Double>> set = map.entrySet();
      Iterator<Entry<Expression, Double>> iterator = set.iterator();
      Entry<Expression, Double> entry;
      for (int i = 0; i < map.size(); i++) {
        entry = iterator.next();
        terms.add(new DRealTerm(null, dreal.Multiply(entry.getKey(),
            new Expression(entry.getValue())), null, pTerm.getType()));
      }
      return terms;
    }
  }

  private static List<DRealTerm> getExpressionFromMul(DRealTerm pTerm) {
    List<DRealTerm> terms = new ArrayList<>();
    if (pTerm.isFormula() || pTerm.isVar()) {
      throw new IllegalArgumentException("Term is Variable or Formula");
    } else {
      terms.add(new DRealTerm(null,
          new Expression(dreal.get_constant_in_multiplication(pTerm.getExpression())), null,
          pTerm.getType()));
      ExpressionExpressionMap map =
          dreal.get_base_to_exponent_map_in_multiplication(pTerm.getExpression());
      Set<Entry<Expression, Expression>> set = map.entrySet();
      Iterator<Entry<Expression, Expression>> iterator = set.iterator();
      Entry<Expression, Expression> entry;
      for (int i = 0; i < map.size(); i++) {
        entry = iterator.next();
        // it is possible to create an Expression like (x*x*x), therefore pow will always have an
        // int as exponent -> convert back multiplication
        // this should be changed if pow is supported in JavaSMT
        for (double j = 0; j < parseDouble(entry.getValue().to_string()); j++) {
          terms.add(new DRealTerm(null, new Expression(entry.getKey()), null, pTerm.getType()));
        }
      }
      return terms;
    }
  }


  @Override
  public DRealTerm callFunctionImpl(DRealTerm declaration, List<DRealTerm> args) {
    return null;
  }

  @Override
  public DRealTerm declareUFImpl(String pName, Type pReturnType, List<Type> pArgTypes) {
    return null;
  }

  @Override
  protected DRealTerm getBooleanVarDeclarationImpl(DRealTerm pDRealTerm) {
    return null;
  }
}
