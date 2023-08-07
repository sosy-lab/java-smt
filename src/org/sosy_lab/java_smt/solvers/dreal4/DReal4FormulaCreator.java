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
import static java.lang.String.valueOf;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier.FORALL;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.math.BigDecimal;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
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
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.VariableSet;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variables;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;
public class DReal4FormulaCreator extends FormulaCreator<DRealTerm<?, ?>, Type, Context,
    DRealTerm<?, ?>> {

  private final Map<String, DRealTerm<Variable, Type>> variablesCache = new HashMap<>();
  private final Map<String, DRealTerm<?, ?>> functionCache = new HashMap<>();

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
  public DRealTerm<Variable, Type> makeVariable(Type pType, String varName) {
    if (variablesCache.get(varName) == null) {
      DRealTerm<Variable, Type> var =
          new DRealTerm<>(new Variable(varName, pType), pType, pType);
      variablesCache.put(varName, var);
      return var;
    } else {
      DRealTerm<Variable, Type> var = variablesCache.get(varName);
      if (var.getVariable().get_type() == pType) {
        return var;
      } else {
        throw new IllegalArgumentException("Symbol name already in use for different type "
            + var.getType());
      }
    }
  }

  @Override
  public DRealTerm<?, ?> extractInfo(Formula pT) {
    return DReal4FormulaManager.getDReal4Formula(pT);
  }

  @Override
  public FormulaType<?> getFormulaType(DRealTerm<? ,?> formula) {
    if (formula.getType() == Type.BOOLEAN) {
      return FormulaType.BooleanType;
    } else if (formula.getType() == Type.INTEGER) {
      return FormulaType.IntegerType;
    } else
      return FormulaType.RationalType;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, DRealTerm<?, ?> pTerm) {
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
  public BooleanFormula encapsulateBoolean(DRealTerm<?, ?> pTerm) {
    assert getFormulaType(pTerm).isBooleanType()
        : String.format(
        "%s is not boolean, but %s (%s)", pTerm.to_string(), pTerm.getType(), getFormulaType(pTerm));
    return new DReal4BooleanFormula(pTerm);
  }
  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, DRealTerm<?, ?> f) {

    final FunctionDeclarationKind functionKind;
    List<DRealTerm<?, ?>> functionArgs = null;

    if (f.isVar()) {
      return visitor.visitFreeVariable(formula, f.getVariable().to_string());
    } else if (f.isExp()) {
      ExpressionKind kind = f.getExpressionKind();
      if (kind == ExpressionKind.Constant) {
        // not possible to create an Expression from a boolean Variable
        if (f.getType() == Type.INTEGER) {
          return visitor.visitConstant(formula, new BigInteger(f.getExpression().to_string()));
        } else {
          return visitor.visitConstant(formula,
             BigDecimal.valueOf(parseDouble(f.getExpression().to_string())));
        }
      } else if (kind == ExpressionKind.Var) {
        return visitor.visitFreeVariable(formula, f.getExpression().to_string());
      } else if (kind == ExpressionKind.IfThenElse) {
        functionKind = FunctionDeclarationKind.ITE;
        functionArgs = getExpressionFromITE(f);
      } else if (kind == ExpressionKind.Pow) {
        // the exponent should only be an int i >= 2, because the only way to get an
        // expression with an exponent is to create an expression like (x*x*x), because pow is
        // not supported in JavaSMT or if a variable gets negated, so pow(x,-1)
        DRealTerm<Expression, ExpressionKind> pow;
        Expression lhs = dreal.get_first_argument(f.getExpression());
        Expression rhs = dreal.get_second_argument(f.getExpression());
        double exponent = parseDouble(rhs.to_string());
        if (exponent < 0) {
          functionKind = FunctionDeclarationKind.DIV;
          pow = new DRealTerm<>(dreal.Divide(Expression.One(), lhs),
              dreal.get_variable(lhs).get_type(), ExpressionKind.Div);
        } else {
          functionKind = FunctionDeclarationKind.MUL;
          Expression exp = dreal.Multiply(lhs, lhs);
          for (int i = 2; i < exponent; i++) {
            exp = dreal.Multiply(exp, lhs);
          }
          pow = new DRealTerm<>(exp, dreal.get_variable(lhs).get_type(), ExpressionKind.Mul);
        }
        functionArgs = getExpressionFromMul(pow);
      } else if (kind == ExpressionKind.Add) {
        functionKind = FunctionDeclarationKind.ADD;
        functionArgs = getExpressionFromAdd(f);
      } else if (kind == ExpressionKind.Mul) {
        functionKind = FunctionDeclarationKind.MUL;
        functionArgs = getExpressionFromMul(f);
      } else {
        functionKind = FunctionDeclarationKind.DIV;
        functionArgs = getExpressionsFromDiv(f);
      }
    } else {
      FormulaKind kind = f.getFormulaKind();
      if (kind == FormulaKind.Forall) {
        VariableSet set = f.getFormula().getQuantifiedVariables();
        List<Formula> boundVariables = new ArrayList<>();
        DRealTerm<?, ?> var;
        Iterator<Variable> iter = set.iterator();
        Variable next;
        for (int i = 0; i < set.size(); i++) {
          next = iter.next();
          var = new DRealTerm<>(next, next.get_type(), next.get_type());
          boundVariables.add(encapsulate(getFormulaType(var), var));
        }
        DRealTerm<org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula, FormulaKind> quantifiedFormula =
            new DRealTerm<>(dreal.get_quantified_formula(f.getFormula()),
            Type.BOOLEAN, dreal.get_quantified_formula(f.getFormula()).get_kind());
        return visitor.visitQuantifier((BooleanFormula) formula, FORALL, boundVariables,
            encapsulateBoolean(quantifiedFormula));
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
        DRealTerm<org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula, FormulaKind> neqTerm =
            new DRealTerm<>(
                new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(dreal.Or(dreal.Grater(lhs,
                    rhs), dreal.Less(lhs, rhs))), Type.BOOLEAN, FormulaKind.Or);
        functionKind = FunctionDeclarationKind.OR;
        functionArgs = getFormulaArgs(neqTerm);
      } else if (kind == FormulaKind.Var) {
        return visitor.visitFreeVariable(formula, f.getFormula().to_string());
      } else if (kind == FormulaKind.True) {
        return visitor.visitConstant(formula, true);
      } else if (kind == FormulaKind.False) {
        return visitor.visitConstant(formula, false);
      } else {
        return visitor.visitFreeVariable(formula, f.getFormula().to_string());
      }
    }

    String functionName = functionKind.toString();
    if (functionArgs == null) {
      functionArgs = getExpressionArgs(f);
    }

    DRealTerm<?, ?> pDeclaration;

    // Variable should be handled above, just to be sure
    Preconditions.checkState(f.isExp() || f.isFormula());
    if (f.isExp()) {
      pDeclaration = new DRealTerm<>(new Expression(), f.getType(),f.getExpressionKind());
    } else {
      pDeclaration = new DRealTerm<>(new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(),
          f.getType(), f.getFormulaKind());
    }


    final ImmutableList<FormulaType<?>> argTypes = ImmutableList.copyOf(toType(functionArgs));

    final ImmutableList.Builder<Formula> argsBuilder = ImmutableList.builder();
    for (int i = 0; i < functionArgs.size(); i++) {
      argsBuilder.add(encapsulate(argTypes.get(i), functionArgs.get(i)));
    }
    final ImmutableList<Formula> args = argsBuilder.build();

    return visitor.visitFunction(formula, args, FunctionDeclarationImpl.of(functionName,
        functionKind, argTypes, getFormulaType(f), pDeclaration));

  }
  private List<FormulaType<?>> toType(final List<DRealTerm<?, ?>> args) {
    return Lists.transform(args, this::getFormulaType);
  }

  private static List<DRealTerm<?, ?>> getFormulaArgs(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> formulas = new ArrayList<>();
    org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula formula;

    if (pTerm.isFormula()) {
      FormulaSet set = dreal.get_operands(pTerm.getFormula());
      Iterator<org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula> iter = set.iterator();
      for (int i = 0; i < set.size(); i++) {
        formula = iter.next();
        formulas.add(new DRealTerm<>(formula, pTerm.getType(), formula.get_kind()));
      }
      return formulas;
    } else {
      throw new IllegalArgumentException("Term is not a Formula.");
    }
  }

  private static List<DRealTerm<?, ?>> getExpressionArgs(DRealTerm<?, ?> parent) {
    List<DRealTerm<?, ?>> children = new ArrayList<>();
    if (parent.isExp()) {
      throw new IllegalArgumentException("Term is Expression.");
    } else if (parent.isFormula()) {
      Type type = getTypeForExpressions(dreal.get_lhs_expression(parent.getFormula()));
      if (type == null) {
        type = getTypeForExpressions(dreal.get_rhs_expression(parent.getFormula()));
      }
      children.add(new DRealTerm<>(dreal.get_lhs_expression(parent.getFormula()), type,
          dreal.get_lhs_expression(parent.getFormula()).get_kind()));
      children.add(new DRealTerm<>(dreal.get_rhs_expression(parent.getFormula()), type,
          dreal.get_rhs_expression(parent.getFormula()).get_kind()));
      return children;
    } else {
      throw new IllegalArgumentException("Term is Variable.");
    }
  }

  private static List<DRealTerm<?, ?>> getFormulaFromNot(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> formula = new ArrayList<>();
    if (pTerm.isVar() || pTerm.isExp()) {
      throw new IllegalArgumentException("Term is Expression or Variable.");
    } else {
      org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula term = dreal.get_operand(pTerm.getFormula());
      formula.add(new DRealTerm<>(term, Type.BOOLEAN, term.get_kind()));
      return formula;
    }
  }

  private static List<DRealTerm<?, ?>> getExpressionsFromDiv(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> children = new ArrayList<>();
    if (pTerm.isVar() || pTerm.isExp()) {
      throw new IllegalArgumentException("Term is Variable or Expression");
    } else {
      children.add(new DRealTerm<>(dreal.get_first_argument(pTerm.getExpression()),
          pTerm.getType(), dreal.get_first_argument(pTerm.getExpression()).get_kind()));
      children.add(new DRealTerm<>(dreal.get_second_argument(pTerm.getExpression()),
          pTerm.getType(), dreal.get_second_argument(pTerm.getExpression()).get_kind()));
      return children;
    }
  }

  private static List<DRealTerm<?, ?>> getExpressionFromITE(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> children = new ArrayList<>();
    if (pTerm.isFormula() || pTerm.isVar()) {
      throw new IllegalArgumentException("Term is Variable or Formula");
    } else {
      children.add(new DRealTerm<>(dreal.get_conditional_formula(pTerm.getExpression()),
          pTerm.getType(), dreal.get_conditional_formula(pTerm.getExpression()).get_kind()));
      children.add(new DRealTerm<>(dreal.get_then_expression(pTerm.getExpression()),
          pTerm.getType(), dreal.get_then_expression(pTerm.getExpression()).get_kind()));
      children.add(new DRealTerm<>(dreal.get_else_expression(pTerm.getExpression()),
          pTerm.getType(), dreal.get_else_expression(pTerm.getExpression()).get_kind()));
      return children;
    }
  }

  private static List<DRealTerm<?, ?>> getExpressionFromAdd(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> terms = new ArrayList<>();
    if (pTerm.isVar() || pTerm.isFormula()) {
      throw new IllegalArgumentException("Term is Variable or Formula.");
    } else {
      terms.add(new DRealTerm<>(new Expression(dreal.get_constant_in_addition(pTerm.getExpression())),
          pTerm.getType(), ExpressionKind.Constant));
      ExpressionDoubleMap map = dreal.get_expr_to_coeff_map_in_addition(pTerm.getExpression());
      Set<Entry<Expression, Double>> set = map.entrySet();
      Iterator<Entry<Expression, Double>> iterator = set.iterator();
      Entry<Expression, Double> entry;
      for (int i = 0; i < map.size(); i++) {
        entry = iterator.next();
        terms.add(new DRealTerm<>(dreal.Multiply(entry.getKey(),
            new Expression(entry.getValue())), pTerm.getType(), ExpressionKind.Mul));
      }
      return terms;
    }
  }

  private static List<DRealTerm<?, ?>> getExpressionFromMul(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> terms = new ArrayList<>();
    if (pTerm.isFormula() || pTerm.isVar()) {
      throw new IllegalArgumentException("Term is Variable or Formula");
    } else {
      terms.add(new DRealTerm<>(
          new Expression(dreal.get_constant_in_multiplication(pTerm.getExpression())),
          pTerm.getType(), ExpressionKind.Constant));
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
          terms.add(new DRealTerm<>(new Expression(entry.getKey()),
              pTerm.getType(), ExpressionKind.Var));
        }
      }
      return terms;
    }
  }

  /*
  Needed if we split a formula. For example, we have x + 2 < 10. In visit we will
  extract the first and second expression and need the type for the Expression. Because we
  have only the parent to get the type from, it will always return Boolean Type, but the
  expression should be some kind of NumeralFormula Type
  */
  private static Type getTypeForExpressions(Expression pExpression) {
    // If the Expression is Constant we return null, because from constant we cannot get the
    // type, but this function is always called from a formula, so this is called two times, and
    // one of them has a Variable, else this Formula would have been a True or False formula
    if (pExpression.get_kind() == ExpressionKind.Constant) {
      return null;
    } else if (pExpression.get_kind() == ExpressionKind.Var) {
      return dreal.get_variable(pExpression).get_type();
    } else if (pExpression.get_kind() == ExpressionKind.Div) {
      Expression lhs = dreal.get_first_argument(pExpression);
      Expression rhs = dreal.get_second_argument(pExpression);
      // Division has at least one Variable, else it would be a constant;
      if (lhs.get_kind() == ExpressionKind.Var) {
        return dreal.get_variable(lhs).get_type();
      } else {
        return dreal.get_variable(rhs).get_type();
      }
    } else if (pExpression.get_kind() == ExpressionKind.Mul) {
      // we will always get a Variable, else it would be a constant 3*3 -> 9
      ExpressionExpressionMap map =
          dreal.get_base_to_exponent_map_in_multiplication(pExpression);
      Set<Entry<Expression, Expression>> set = map.entrySet();
      Iterator<Entry<Expression, Expression>> iterator = set.iterator();
      // we only need one, because the type is the same from all of them
      Entry<Expression, Expression> entry = iterator.next();
      return dreal.get_variable(entry.getKey()).get_type();
    } else if (pExpression.get_kind() == ExpressionKind.Add) {
      ExpressionDoubleMap map = dreal.get_expr_to_coeff_map_in_addition(pExpression);
      Set<Entry<Expression, Double>> set = map.entrySet();
      Iterator<Entry<Expression, Double>> iterator = set.iterator();
      // we only need one, because the type is the same from all of them
      Entry<Expression, Double> entry = iterator.next();
      return dreal.get_variable(entry.getKey()).get_type();
    } else if (pExpression.get_kind() == ExpressionKind.Pow) {
      // pow(x,int) first argument should always be a variable
      Expression lhs = dreal.get_first_argument(pExpression);
      return dreal.get_variable(lhs).get_type();
    } else if (pExpression.get_kind() == ExpressionKind.IfThenElse) {
      //TODO:!
      return null;
    }
    else {
      throw new AssertionError("Kind not known, this should not be possible.");
    }
  }

  //TODO: nicht richtig so -> antwort von dReal?
  @Override
  public DRealTerm<?, ?> callFunctionImpl(DRealTerm<?, ?> declaration, List<DRealTerm<?, ?>> args) {
    if (args.isEmpty()) {
      // Variable erstellen
      throw new IllegalArgumentException("dReal does not support UFs without arguments.");
    } else {
      Expression expression;
      org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula formula;
      if (declaration.isExp()) {
        ExpressionKind expressionKind = declaration.getExpressionKind();
        if (expressionKind.equals(ExpressionKind.IfThenElse)) {
          return new DRealTerm<>(
              dreal.if_then_else(args.get(0).getFormula(), args.get(1).getExpression(),
                  args.get(2).getExpression()), args.get(2).getType(), ExpressionKind.IfThenElse);
        } else if (expressionKind.equals(ExpressionKind.Div)) {
          return new DRealTerm<>(dreal.Divide(args.get(0).getExpression(),
              args.get(1).getExpression()), args.get(0).getType(), ExpressionKind.Div);
        } else if (expressionKind.equals(ExpressionKind.Mul)) {
          expression = dreal.Multiply(args.get(0).getExpression(), args.get(1).getExpression());
          if (args.size() > 2) {
            for (int i = 2; i < args.size(); i++) {
              expression = (dreal.Multiply(expression, args.get(i).getExpression()));
            }
          }
          return new DRealTerm<>(expression, args.get(0).getType(), ExpressionKind.Mul);
        } else if (expressionKind.equals(ExpressionKind.Add)) {
          expression = dreal.Add(args.get(0).getExpression(), args.get(1).getExpression());
          if (args.size() > 2) {
            for (int i = 2; i < args.size(); i++) {
              expression = (dreal.Add(expression, args.get(i).getExpression()));
            }
          }
          return new DRealTerm<>(expression, args.get(0).getType(), ExpressionKind.Add);
        } else if (expressionKind.equals(ExpressionKind.UninterpretedFunction)) {
          //TODO: Was soll passieren?
          return new DRealTerm<>(args.get(0).getExpression(), args.get(0).getType(),
              args.get(0).getExpressionKind());
        }
      } else if (declaration.isFormula()) {
        FormulaKind formulaKind = declaration.getFormulaKind();
        if (formulaKind.equals(FormulaKind.Not)) {
          return new DRealTerm<>(dreal.Not(args.get(0).getFormula()), args.get(0).getType(),
              FormulaKind.Not);
        } else if (formulaKind.equals(FormulaKind.Eq)) {
          return new DRealTerm<>(dreal.Equal(args.get(0).getExpression(),
              args.get(1).getExpression()), args.get(0).getType(), FormulaKind.Eq);
        } else if (formulaKind.equals(FormulaKind.Gt)) {
          return new DRealTerm<>(dreal.Grater(args.get(0).getExpression(),
              args.get(1).getExpression()), args.get(0).getType(), FormulaKind.Gt);
        } else if (formulaKind.equals(FormulaKind.Geq)) {
          return new DRealTerm<>(dreal.GraterEqual(args.get(0).getExpression(),
              args.get(1).getExpression()), args.get(0).getType(), FormulaKind.Geq);
        } else if (formulaKind.equals(FormulaKind.Lt)) {
          return new DRealTerm<>(dreal.Less(args.get(0).getExpression(),
              args.get(1).getExpression()), args.get(0).getType(), FormulaKind.Lt);
        } else if (formulaKind.equals(FormulaKind.Leq)) {
          return new DRealTerm<>(dreal.LessEqual(args.get(0).getExpression(),
              args.get(1).getExpression()), args.get(0).getType(), FormulaKind.Leq);
        } else if (formulaKind.equals(FormulaKind.And)) {
          formula = dreal.And(args.get(0).getFormula(), args.get(1).getFormula());
          if (args.size() > 2) {
            for (int i = 2; i < args.size(); i++) {
              formula = dreal.And(formula, args.get(i).getFormula());
            }
          }
          return new DRealTerm<>(formula, Type.BOOLEAN, FormulaKind.And);
        } else if (formulaKind.equals(FormulaKind.Or)) {
          formula = dreal.Or(args.get(0).getFormula(), args.get(1).getFormula());
          if (args.size() > 2) {
            for (int i = 2; i < args.size(); i++) {
              formula = dreal.Or(formula, args.get(i).getFormula());
            }
          }
          return new DRealTerm<>(formula, Type.BOOLEAN, FormulaKind.Or);
        }
      } else {
        // Variable?
        return null;
      }
      throw new IllegalArgumentException("Unknown function declaration.");
    }
  }

  //TODO: nicht richtig so -> antwort von dReal?
  @Override
  public DRealTerm<?, ?> declareUFImpl(String pName, Type pReturnType, List<Type> pArgTypes) {
    DRealTerm<?, ?> term = functionCache.get(pName);
    if (term == null) {
      if (pArgTypes.isEmpty()) {
        // einfach Variable zurückgeben?
        return new DRealTerm<>(new Variable(pName, pReturnType), pReturnType,
            pReturnType);
      } else {
        Variables vars = new Variables();
        for (int i = 0; i < pArgTypes.size(); i++) {
          vars.insert(new Variable(valueOf(i), pArgTypes.get(i)));
        }
        return new DRealTerm<>(dreal.uninterpreted_function(pName, vars), pReturnType,
            ExpressionKind.UninterpretedFunction);
      }
    } else if (term.getType() == pReturnType) {
      return term;
    } else {
      throw new IllegalArgumentException("symbol already exist for UF with different type.");
    }
  }

  @Override
  protected DRealTerm<?, ?> getBooleanVarDeclarationImpl(DRealTerm<?, ?> pDRealTerm) {
    // create DRealTerm with dummy Variable, Expression, Formula, only to save declaration in
    // DRealTerm
    if (pDRealTerm.isVar()) {
      return new DRealTerm<>(new Variable(), pDRealTerm.getType(), pDRealTerm.getType());
    } else if (pDRealTerm.isExp()) {
      return new DRealTerm<>(new Expression(), pDRealTerm.getType(), pDRealTerm.getExpressionKind());
    } else {
      return new DRealTerm<>(new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(),
          pDRealTerm.getType(), pDRealTerm.getFormulaKind());
    }
  }

  @Override
  public Object convertValue(DRealTerm<?, ?> pTerm) {
    Preconditions.checkState(pTerm.isExp() || pTerm.isFormula());
    if (pTerm.isExp()) {
      // This should be a constant, Integer or Rational
      Preconditions.checkState(pTerm.getExpression().get_kind() == ExpressionKind.Constant);
      if (pTerm.getType() == Type.INTEGER) {
        return new BigInteger(pTerm.getExpression().to_string());
      } else {
        return Rational.ofString(pTerm.getExpression().to_string());
      }
    } else {
      if (pTerm.getFormulaKind() == FormulaKind.True || pTerm.getFormulaKind() == FormulaKind.False) {
        return dreal.is_true(pTerm.getFormula());
      } else {
        throw new UnsupportedOperationException("Can not convert Formula to Value.");
      }

    }
  }

}
