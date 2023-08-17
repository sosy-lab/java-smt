// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import static java.lang.Double.parseDouble;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier.FORALL;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
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
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionDoubleMap;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionExpressionMap;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaSet;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.VariableSet;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Dreal;

public class DReal4FormulaCreator
    extends FormulaCreator<DRealTerm<?, ?>, Variable.Type, Config, DRealTerm<?, ?>> {

  private final Map<String, DRealTerm<Variable, Variable.Type>> variablesCache = new HashMap<>();

  public DReal4FormulaCreator(Config config) {
    super(
        config, Variable.Type.BOOLEAN, Variable.Type.INTEGER, Variable.Type.CONTINUOUS, null, null);
  }

  @Override
  public Variable.Type getBitvectorType(int bitwidth) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Variable.Type getFloatingPointType(FloatingPointType type) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Variable.Type getArrayType(Variable.Type indexType, Variable.Type elementType) {
    throw new UnsupportedOperationException();
  }

  @Override
  public DRealTerm<Variable, Variable.Type> makeVariable(Variable.Type pType, String varName) {
    if (variablesCache.get(varName) == null) {
      DRealTerm<Variable, Variable.Type> var =
          new DRealTerm<>(new Variable(varName, pType), pType, pType);
      variablesCache.put(varName, var);
      return var;
    } else {
      DRealTerm<Variable, Variable.Type> var = variablesCache.get(varName);
      if (var.getVariable().getType() == pType) {
        return var;
      } else {
        throw new IllegalArgumentException(
            "Symbol name already in use for different type " + var.getType());
      }
    }
  }

  @Override
  public DRealTerm<?, ?> extractInfo(Formula pT) {
    return DReal4FormulaManager.getDReal4Formula(pT);
  }

  @Override
  public FormulaType<?> getFormulaType(DRealTerm<?, ?> formula) {
    if (formula.getType() == Variable.Type.BOOLEAN) {
      return FormulaType.BooleanType;
    } else if (formula.getType() == Variable.Type.INTEGER) {
      return FormulaType.IntegerType;
    } else return FormulaType.RationalType;
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
            pTerm, getFormulaType(pTerm), pType);
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
            "%s is not boolean, but %s (%s)", pTerm, pTerm.getType(), getFormulaType(pTerm));
    return new DReal4BooleanFormula(pTerm);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, DRealTerm<?, ?> f) {

    final FunctionDeclarationKind functionKind;
    FormulaKind formulaKind = null;
    ExpressionKind expressionKind = null;
    List<DRealTerm<?, ?>> functionArgs = null;

    if (f.isVar()) {
      return visitor.visitFreeVariable(formula, f.getVariable().toString());
    } else if (f.isExp()) {
      ExpressionKind kind = f.getExpressionKind();
      if (kind == ExpressionKind.Constant) {
        String s = f.toString();
        int idx = s.indexOf(".");
        if (idx == -1) {
          return visitor.visitConstant(formula, new BigInteger(s));
        } else {
          return visitor.visitConstant(
              formula, Rational.ofBigDecimal(BigDecimal.valueOf(parseDouble(s))));
        }
      } else if (kind == ExpressionKind.Var) {
        return visitor.visitFreeVariable(formula, f.getExpression().toString());
      } else if (kind == ExpressionKind.IfThenElse) {
        functionKind = FunctionDeclarationKind.ITE;
        expressionKind = ExpressionKind.IfThenElse;
        functionArgs = getExpressionFromITE(f);
      } else if (kind == ExpressionKind.Pow) {
        // the exponent should only be an int i >= 2, because the only way to get an
        // expression with an exponent is to create an expression like (x*x*x), because pow is
        // not supported in JavaSMT or if a variable gets negated, so pow(x,-1)
        DRealTerm<Expression, ExpressionKind> pow;
        Expression lhs = Dreal.getFirstArgument(f.getExpression());
        Expression rhs = Dreal.getSecondArgument(f.getExpression());
        double exponent = parseDouble(rhs.toString());
        if (exponent < 0) {
          functionKind = FunctionDeclarationKind.DIV;
          expressionKind = ExpressionKind.Div;
          pow =
              new DRealTerm<>(
                  Dreal.divide(Expression.one(), lhs),
                  Dreal.getVariable(lhs).getType(),
                  ExpressionKind.Div);
        } else {
          functionKind = FunctionDeclarationKind.MUL;
          expressionKind = ExpressionKind.Mul;
          Expression exp = Dreal.multiply(lhs, lhs);
          for (int i = 2; i < exponent; i++) {
            exp = Dreal.multiply(exp, lhs);
          }
          pow = new DRealTerm<>(exp, Dreal.getVariable(lhs).getType(), ExpressionKind.Mul);
        }
        functionArgs = getExpressionFromMul(pow);
      } else if (kind == ExpressionKind.Add) {
        functionKind = FunctionDeclarationKind.ADD;
        expressionKind = ExpressionKind.Add;
        functionArgs = getExpressionFromAdd(f);
      } else if (kind == ExpressionKind.Mul) {
        functionKind = FunctionDeclarationKind.MUL;
        expressionKind = ExpressionKind.Mul;
        functionArgs = getExpressionFromMul(f);
      } else {
        functionKind = FunctionDeclarationKind.DIV;
        expressionKind = ExpressionKind.Div;
        functionArgs = getExpressionsFromDiv(f);
      }
    } else {
      FormulaKind kind = f.getFormulaKind();
      if (kind == FormulaKind.Forall) {
        VariableSet set = f.getFormula().getQuantifiedVariables();
        List<Formula> boundVariables = new ArrayList<>();
        DRealTerm<Variable, Variable.Type> var;
        Iterator<Variable> iter = set.iterator();
        Variable next;
        for (int i = 0; i < set.size(); i++) {
          next = iter.next();
          var = new DRealTerm<>(next, next.getType(), next.getType());
          boundVariables.add(encapsulate(getFormulaType(var), var));
        }
        DRealTerm<org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula, FormulaKind>
            quantifiedFormula =
                new DRealTerm<>(
                    Dreal.getQuantifiedFormula(f.getFormula()),
                    Variable.Type.BOOLEAN,
                    f.getFormula().getKind());
        return visitor.visitQuantifier(
            (BooleanFormula) formula,
            FORALL,
            boundVariables,
            encapsulateBoolean(quantifiedFormula));
      } else if (kind == FormulaKind.And) {
        functionKind = FunctionDeclarationKind.AND;
        formulaKind = FormulaKind.And;
        functionArgs = getFormulaArgs(f);
      } else if (kind == FormulaKind.Or) {
        functionKind = FunctionDeclarationKind.OR;
        formulaKind = FormulaKind.Or;
        functionArgs = getFormulaArgs(f);
      } else if (kind == FormulaKind.Not) {
        functionKind = FunctionDeclarationKind.NOT;
        formulaKind = FormulaKind.Not;
        functionArgs = getFormulaFromNot(f);
      } else if (kind == FormulaKind.Eq) {
        functionKind = FunctionDeclarationKind.EQ;
        formulaKind = FormulaKind.Eq;
      } else if (kind == FormulaKind.Geq) {
        functionKind = FunctionDeclarationKind.GTE;
        formulaKind = FormulaKind.Geq;
      } else if (kind == FormulaKind.Gt) {
        functionKind = FunctionDeclarationKind.GT;
        formulaKind = FormulaKind.Gt;
      } else if (kind == FormulaKind.Leq) {
        functionKind = FunctionDeclarationKind.LT;
        formulaKind = FormulaKind.Lt;
      } else if (kind == FormulaKind.Lt) {
        functionKind = FunctionDeclarationKind.LTE;
        formulaKind = FormulaKind.Leq;
      } else if (kind == FormulaKind.Neq) {
        // lhs ≠ rhs -> (lhs > rhs) ∨ (lhs < rhs)
        Expression lhs = Dreal.getLhsExpression(f.getFormula());
        Expression rhs = Dreal.getRhsExpression(f.getFormula());
        DRealTerm<org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula, FormulaKind> neqTerm =
            new DRealTerm<>(
                new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(
                    Dreal.or(Dreal.grater(lhs, rhs), Dreal.less(lhs, rhs))),
                Variable.Type.BOOLEAN,
                FormulaKind.Or);
        functionKind = FunctionDeclarationKind.OR;
        formulaKind = FormulaKind.Or;
        functionArgs = getFormulaArgs(neqTerm);
      } else if (kind == FormulaKind.Var) {
        return visitor.visitFreeVariable(formula, f.getFormula().toString());
      } else if (kind == FormulaKind.True) {
        return visitor.visitConstant(formula, true);
      } else if (kind == FormulaKind.False) {
        return visitor.visitConstant(formula, false);
      } else {
        return visitor.visitFreeVariable(formula, f.getFormula().toString());
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
      pDeclaration = new DRealTerm<>(new Expression(), f.getType(), expressionKind);
    } else {
      pDeclaration =
          new DRealTerm<>(
              new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(),
              f.getType(),
              formulaKind);
    }

    final ImmutableList<FormulaType<?>> argTypes = ImmutableList.copyOf(toType(functionArgs));

    final ImmutableList.Builder<Formula> argsBuilder = ImmutableList.builder();
    for (int i = 0; i < functionArgs.size(); i++) {
      argsBuilder.add(encapsulate(argTypes.get(i), functionArgs.get(i)));
    }
    final ImmutableList<Formula> args = argsBuilder.build();

    return visitor.visitFunction(
        formula,
        args,
        FunctionDeclarationImpl.of(
            functionName, functionKind, argTypes, getFormulaType(f), pDeclaration));
  }

  private List<FormulaType<?>> toType(final List<DRealTerm<?, ?>> args) {
    return Lists.transform(args, this::getFormulaType);
  }

  private static List<DRealTerm<?, ?>> getFormulaArgs(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> formulas = new ArrayList<>();
    org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula formula;
    // pTerm should be a Formula, not Expression or Variable
    Preconditions.checkState(pTerm.isFormula());
    FormulaSet set = Dreal.getOperands(pTerm.getFormula());
    Iterator<org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula> iter = set.iterator();
    for (int i = 0; i < set.size(); i++) {
      formula = iter.next();
      formulas.add(new DRealTerm<>(formula, pTerm.getType(), formula.getKind()));
    }
    return formulas;
  }

  private static List<DRealTerm<?, ?>> getExpressionArgs(DRealTerm<?, ?> parent) {
    List<DRealTerm<?, ?>> children = new ArrayList<>();
    // pTerm should be a Formula, so that the expressions or variable can be extracted
    Preconditions.checkState(parent.isFormula());
    Variable.Type type = getTypeForExpressions(Dreal.getLhsExpression(parent.getFormula()));
    if (type == null) {
      type = getTypeForExpressions(Dreal.getRhsExpression(parent.getFormula()));
    }
    Expression left = Dreal.getLhsExpression(parent.getFormula());
    Expression right = Dreal.getRhsExpression(parent.getFormula());
    children.add(new DRealTerm<>(left, type, left.getKind()));
    children.add(new DRealTerm<>(right, type, right.getKind()));
    return children;
  }

  private static List<DRealTerm<?, ?>> getFormulaFromNot(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> formula = new ArrayList<>();
    // pTerm should be Formula, because we try to get the formula inside the Not-Formula
    Preconditions.checkState(pTerm.isFormula());
    org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula term =
        Dreal.getOperand(pTerm.getFormula());
    formula.add(new DRealTerm<>(term, Variable.Type.BOOLEAN, term.getKind()));
    return formula;
  }

  private static List<DRealTerm<?, ?>> getExpressionsFromDiv(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> children = new ArrayList<>();
    // pTerm is Division-Expression
    Preconditions.checkState(pTerm.isExp());
    Expression first = Dreal.getFirstArgument(pTerm.getExpression());
    Expression second = Dreal.getSecondArgument(pTerm.getExpression());
    children.add(new DRealTerm<>(first, pTerm.getType(), first.getKind()));
    children.add(new DRealTerm<>(second, pTerm.getType(), second.getKind()));
    return children;
  }

  private static List<DRealTerm<?, ?>> getExpressionFromITE(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> children = new ArrayList<>();
    // pTerm ist if_then_else Expression
    Preconditions.checkState(pTerm.isExp());
    org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula cond =
        Dreal.getConditionalFormula(pTerm.getExpression());
    Expression expThen = Dreal.getThenExpression(pTerm.getExpression());
    Expression expElse = Dreal.getElseExpression(pTerm.getExpression());
    children.add(new DRealTerm<>(cond, pTerm.getType(), cond.getKind()));
    children.add(new DRealTerm<>(expThen, pTerm.getType(), expThen.getKind()));
    children.add(new DRealTerm<>(expElse, pTerm.getType(), expElse.getKind()));
    return children;
  }

  private static List<DRealTerm<?, ?>> getExpressionFromAdd(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> terms = new ArrayList<>();
    // pTerm is addition expression
    Preconditions.checkState(pTerm.isExp());
    terms.add(
        new DRealTerm<>(
            new Expression(Dreal.getConstantInAddition(pTerm.getExpression())),
            pTerm.getType(),
            ExpressionKind.Constant));
    ExpressionDoubleMap map = Dreal.getExprToCoeffMapInAddition(pTerm.getExpression());
    for (Map.Entry<Expression, Double> entry : map.entrySet()) {
      terms.add(
          new DRealTerm<>(
              new Expression(Dreal.multiply(entry.getKey(), new Expression(entry.getValue()))),
              pTerm.getType(),
              ExpressionKind.Mul));
    }
    return terms;
  }

  private static List<DRealTerm<?, ?>> getExpressionFromMul(DRealTerm<?, ?> pTerm) {
    List<DRealTerm<?, ?>> terms = new ArrayList<>();
    // pTerm is multiplication expression
    Preconditions.checkState(pTerm.isExp());
    terms.add(
        new DRealTerm<>(
            new Expression(Dreal.getConstantInMultiplication(pTerm.getExpression())),
            pTerm.getType(),
            ExpressionKind.Constant));
    ExpressionExpressionMap map =
        Dreal.getBaseToExponentMapInMultiplication(pTerm.getExpression());
    // Map of Variable and exponent, exponent can be -1 or grater than 0, we will return pow
    // (var, exp), visit will handle pow
    for (Map.Entry<Expression, Expression> entry : map.entrySet()) {
      terms.add(
          new DRealTerm<>(
              Dreal.pow(entry.getKey(), entry.getValue()), pTerm.getType(), ExpressionKind.Pow));
    }
    return terms;
  }

  /*
  Needed if we split a formula. For example, we have x + 2 < 10. In visit we will
  extract the first and second expression and need the type for the Expression. Because we
  have only the parent to get the type from, it will always return Boolean Type, but the
  expression should be some kind of NumeralFormula Type
  */
  protected static Variable.Type getTypeForExpressions(Expression pExpression) {
    // If the Expression is Constant we return null, because from constant we cannot get the
    // type, but this function is always called from a formula, so this is called two times, and
    // one of them has a Variable, else this Formula would have been a True or False formula
    if (pExpression.getKind() == ExpressionKind.Constant) {
      return null;
    } else if (pExpression.getKind() == ExpressionKind.Var) {
      return Dreal.getVariable(pExpression).getType();
    } else {
      // There is at least one Variable in the Expression, else it would be a constant
      VariableSet varSet = pExpression.getVariables();
      Preconditions.checkState(!varSet.isEmpty());
      Iterator<Variable> iter = varSet.iterator();
      Variable var = iter.next();
      return var.getType();
    }
  }

  // Not possible to throw an unsupported exception, because in AbstractFormulaManager
  // declareUFImpl is called.
  @Override
  public DRealTerm<?, ?> declareUFImpl(
      String pName, Variable.Type pReturnType, List<Variable.Type> pArgTypes) {
    return null;
  }

  // TODO: Funtkion schreiben, um nicht immer wieder die Fälle durchzugehen sondern das auslagern
  //  wenn möglich
  @Override
  public DRealTerm<?, ?> callFunctionImpl(DRealTerm<?, ?> declaration, List<DRealTerm<?, ?>> args) {
    Preconditions.checkArgument(
        !args.isEmpty(), "dReal does not support callFunctionImpl without arguments.");
    if (declaration.isExp()) {
      ExpressionKind expressionKind = (ExpressionKind) declaration.getDeclaration();
      if (expressionKind.equals(ExpressionKind.IfThenElse)) {
        // ITE cond has to be a formula
        Preconditions.checkState(args.get(0).isFormula());
        DRealTerm<?, ?> args1 = args.get(1);
        DRealTerm<?, ?> args2 = args.get(2);
        // Expression ite;
        // ITE else and then must be expression or variable
        Preconditions.checkState(
            (args1.isExp() || args1.isVar()) && (args2.isExp() || args2.isVar()));
        Expression[] expArgs = getExpressionArgs(args1, args2);
        return new DRealTerm<>(
            Dreal.ifThenElse(args.get(0).getFormula(), expArgs[0], expArgs[1]),
            args2.getType(),
            ExpressionKind.IfThenElse);
      }
      DRealTerm<?, ?> args1 = args.get(0);
      DRealTerm<?, ?> args2 = args.get(1);
      // declaration is an Expression, it is only possible to create an expression from variables
      // or expressions
      Preconditions.checkState(
          (args1.isExp() || args1.isVar()) && (args2.isExp() || args2.isVar()));
      Expression[] expArgs = getExpressionArgs(args1, args2);
      if (expressionKind.equals(ExpressionKind.Div)) {
        return new DRealTerm<>(
            Dreal.divide(expArgs[0], expArgs[1]), args1.getType(), ExpressionKind.Div);
      } else if (expressionKind.equals(ExpressionKind.Mul)) {
        Expression mult = Dreal.multiply(expArgs[0], expArgs[1]);
        if (args.size() > 2) {
          for (int i = 2; i < args.size(); i++) {
            if (args.get(i).isExp()) {
              mult = Dreal.multiply(mult, args.get(i).getExpression());
            } else {
              mult = Dreal.multiply(mult, new Expression(args.get(i).getVariable()));
            }
          }
        }
        return new DRealTerm<>(mult, args.get(0).getType(), ExpressionKind.Mul);
      } else if (expressionKind.equals(ExpressionKind.Add)) {
        Expression add = Dreal.Add(expArgs[0], expArgs[1]);
        if (args.size() > 2) {
          for (int i = 2; i < args.size(); i++) {
            if (args.get(i).isExp()) {
              add = Dreal.Add(add, args.get(i).getExpression());
            } else {
              add = Dreal.Add(add, new Expression(args.get(i).getVariable()));
            }
          }
        }
        return new DRealTerm<>(add, args.get(0).getType(), ExpressionKind.Add);
      } else {
        throw new UnsupportedOperationException(
            "No known declarationkind and UF's are not supported.");
      }
    } else if (declaration.isFormula()) {
      FormulaKind formulaKind = (FormulaKind) declaration.getDeclaration();
      if (formulaKind == FormulaKind.Gt
          || formulaKind == FormulaKind.Geq
          || formulaKind == FormulaKind.Leq
          || formulaKind == FormulaKind.Lt) {
        // declaration is Formula and will be created to be Gt, Geq, Leq or Lt. This can only be
        // created with Expression
        Preconditions.checkState(
            (args.get(0).isExp() || args.get(0).isVar())
                && (args.get(1).isExp() || args.get(1).isVar()));
        Expression[] expArgs = getExpressionArgs(args.get(0), args.get(1));
        if (formulaKind == FormulaKind.Gt) {
          return new DRealTerm<>(
              Dreal.grater(expArgs[0], expArgs[1]), args.get(0).getType(), FormulaKind.Gt);
        } else if (formulaKind == FormulaKind.Geq) {
          return new DRealTerm<>(
              Dreal.graterEqual(expArgs[0], expArgs[1]), args.get(0).getType(), FormulaKind.Geq);
        } else if (formulaKind == FormulaKind.Leq) {
          return new DRealTerm<>(
              Dreal.lessEqual(expArgs[0], expArgs[1]), args.get(0).getType(), FormulaKind.Leq);
        } else {
          return new DRealTerm<>(
              Dreal.less(expArgs[0], expArgs[1]), args.get(0).getType(), FormulaKind.Lt);
        }
      }
      if (formulaKind == FormulaKind.And || formulaKind == FormulaKind.Or) {
        org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula[] formulaArgs =
            getFormulaArgs(args.get(0), args.get(1));
        if (formulaKind == FormulaKind.And) {
          org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula and =
              Dreal.and(formulaArgs[0], formulaArgs[1]);
          if (args.size() > 2) {
            for (int i = 2; i < args.size(); i++) {
              if (args.get(i).isVar() && args.get(i).getType() == Variable.Type.BOOLEAN) {
                and =
                    Dreal.and(
                        and,
                        new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(
                            args.get(i).getVariable()));
              } else if (args.get(i).isFormula()) {
                and = Dreal.and(and, args.get(i).getFormula());
              } else {
                throw new UnsupportedOperationException(
                    "And-Formula from Expression or Variable "
                        + "of not boolean type is not supported.");
              }
            }
          }
          return new DRealTerm<>(and, Variable.Type.BOOLEAN, FormulaKind.And);
        } else {
          org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula or =
              Dreal.or(formulaArgs[0], formulaArgs[1]);
          if (args.size() > 2) {
            for (int i = 2; i < args.size(); i++) {
              if (args.get(i).isVar() && args.get(i).getType() == Variable.Type.BOOLEAN) {
                or =
                    Dreal.or(
                        or,
                        new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(
                            args.get(i).getVariable()));
              } else if (args.get(i).isFormula()) {
                or = Dreal.or(or, args.get(i).getFormula());
              } else {
                throw new UnsupportedOperationException(
                    "or-Formula from Expression or Variable "
                        + "of not boolean type is not supported.");
              }
            }
          }
          return new DRealTerm<>(or, Variable.Type.BOOLEAN, FormulaKind.Or);
        }
      }
      if (formulaKind.equals(FormulaKind.Not)) {
        DRealTerm<?, ?> args1 = args.get(0);
        org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula not;
        // Argument must be formula or variable
        Preconditions.checkState(args1.isFormula() || args1.isVar());
        if (args1.isVar() && args1.getType() == Variable.Type.BOOLEAN) {
          not = Dreal.not(new Variable(args1.getVariable()));
        } else if (args1.isFormula()) {
          not = Dreal.not(args1.getFormula());
        } else {
          throw new IllegalArgumentException(
              "Variable is not of boolean type and therefore a formula can not be created.");
        }
        return new DRealTerm<>(not, Variable.Type.BOOLEAN, FormulaKind.Not);
      } else if (formulaKind.equals(FormulaKind.Eq)) {
        DRealTerm<?, ?> args1 = args.get(0);
        DRealTerm<?, ?> args2 = args.get(1);
        org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula eq;
        if (args1.isVar() && args2.isVar()) {
          eq = Dreal.equal(args1.getVariable(), args2.getVariable());
        } else if (args1.isVar() && args2.isExp()) {
          eq = Dreal.equal(new Expression(args1.getVariable()), args2.getExpression());
        } else if (args1.isVar() && args2.isFormula()) {
          eq = Dreal.equal(args1.getVariable(), args2.getFormula());
        } else if (args1.isExp() && args2.isVar()) {
          eq = Dreal.equal(args1.getExpression(), new Expression(args2.getVariable()));
        } else if (args1.isExp() && args2.isExp()) {
          eq = Dreal.equal(args1.getExpression(), args2.getExpression());
        } else if (args1.isFormula() && args2.isVar()) {
          eq = Dreal.equal(args1.getFormula(), args2.getVariable());
        } else if (args1.isFormula() && args2.isFormula()) {
          eq = Dreal.equal(args1.getFormula(), args2.getFormula());
        } else {
          throw new UnsupportedOperationException(
              "Can not create an equal formula from Expression and Formula.");
        }
        return new DRealTerm<>(eq, Variable.Type.BOOLEAN, FormulaKind.Eq);
      } else {
        throw new UnsupportedOperationException(
            "No known declarationkind and UF's are not " + "supported.");
      }
    }
    throw new IllegalArgumentException("Unknown function declaration.");
  }

  private Expression[] getExpressionArgs(DRealTerm<?, ?> args1, DRealTerm<?, ?> args2) {
    Expression[] args = new Expression[2];
    if (args1.isVar() && args2.isVar()) {
      args[0] = new Expression(args1.getVariable());
      args[1] = new Expression(args2.getVariable());
    } else if (args1.isVar() && args2.isExp()) {
      args[0] = new Expression(args1.getExpression());
      args[1] = args2.getExpression();
    } else if (args1.isExp() && args2.isVar()) {
      args[0] = args1.getExpression();
      args[1] = new Expression(args2.getVariable());
    } else {
      args[0] = args1.getExpression();
      args[1] = args2.getExpression();
    }
    return args;
  }

  private org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula[] getFormulaArgs(
      DRealTerm<?, ?> args1, DRealTerm<?, ?> args2) {
    org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula[] args =
        new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula[2];
    if (args1.isVar()
        && args1.getType() == Variable.Type.BOOLEAN
        && args2.isVar()
        && args2.getType() == Variable.Type.BOOLEAN) {
      args[0] = new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(args1.getVariable());
      args[1] = new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(args2.getVariable());
    } else if (args1.isVar() && args1.getType() == Variable.Type.BOOLEAN && args2.isFormula()) {
      args[0] = new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(args1.getVariable());
      args[1] = args2.getFormula();
    } else if (args1.isFormula() && args2.isVar() && args2.getType() == Variable.Type.BOOLEAN) {
      args[0] = args1.getFormula();
      args[1] = new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(args2.getVariable());
    } else {
      args[0] = args1.getFormula();
      args[1] = args2.getFormula();
    }
    return args;
  }

  @Override
  protected DRealTerm<?, ?> getBooleanVarDeclarationImpl(DRealTerm<?, ?> pDRealTerm) {
    if (pDRealTerm.isVar()) {
      return new DRealTerm<>(new Variable(), pDRealTerm.getType(), pDRealTerm.getType());
    } else if (pDRealTerm.isExp()) {
      return new DRealTerm<>(
          new Expression(), pDRealTerm.getType(), (ExpressionKind) pDRealTerm.getDeclaration());
    } else {
      return new DRealTerm<>(
          new org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula(),
          pDRealTerm.getType(),
          (FormulaKind) pDRealTerm.getDeclaration());
    }
  }

  @Override
  public Object convertValue(DRealTerm<?, ?> pTerm) {
    Preconditions.checkState(pTerm.isExp() || pTerm.isFormula());
    if (pTerm.isExp()) {
      // This should be a constant
      Preconditions.checkState(pTerm.getExpression().getKind() == ExpressionKind.Constant);
      String s = pTerm.toString();
      if (pTerm.getType() == Variable.Type.CONTINUOUS) {
        double res = Double.parseDouble(s);
        // check if double is int
        if ((res == Math.floor(res)) && !Double.isInfinite(res)) {
          BigDecimal b = BigDecimal.valueOf(parseDouble(s));
          return b.toBigInteger();
        }
        return Rational.ofBigDecimal(BigDecimal.valueOf(parseDouble(s)));
      } else {
        return new BigInteger(s);
      }
    } else {
      if (pTerm.getFormulaKind() == FormulaKind.True
          || pTerm.getFormulaKind() == FormulaKind.False) {
        return Dreal.isTrue(pTerm.getFormula());
      } else {
        throw new UnsupportedOperationException("Can not convert Formula to a value.");
      }
    }
  }
}
