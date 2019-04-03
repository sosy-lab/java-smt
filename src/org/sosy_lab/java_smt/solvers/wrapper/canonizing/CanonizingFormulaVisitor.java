/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.wrapper.canonizing;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategy;

public class CanonizingFormulaVisitor implements FormulaVisitor<CanonizingFormula> {

  private final CanonizingFormulaStore store;
  private final FormulaManager mgr;

  public CanonizingFormulaVisitor(FormulaManager pMgr, List<CanonizingStrategy> pStrategies) {
    mgr = pMgr;
    store = new CanonizingFormulaStore(mgr, pStrategies);
  }

  public CanonizingFormula translate(Formula pFormula) {
    return mgr.visit(pFormula, this);
  }

  public CanonizingFormulaStore getStorage() {
    return store.copy();
  }

  @Override
  public CanonizingFormula visitFreeVariable(Formula pF, String pName) {
    FormulaType<?> type = store.popType();
    if (type == null) {
      type = mgr.getFormulaType(pF);
    }
    return store.remember(CanonizingVariable.getInstance(mgr, pName, type));
  }

  @Override
  public CanonizingFormula visitBoundVariable(Formula pF, int pDeBruijnIdx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public CanonizingFormula visitConstant(Formula pF, Object pValue) {
    FormulaType<?> type = store.popType();
    if (type == null) {
      // XXX: that situation should only occur in case a solver decides to simplify a whole formula
      // to either 'true' or 'false' before we get a hold of it
      type = FormulaType.BooleanType;
    }
    return store.remember(CanonizingConstant.getInstance(mgr, pValue, type));
  }

  // TODO: PRINCESS -> BV_SLT and probably others
  @Override
  public CanonizingFormula visitFunction(
      Formula pF, List<Formula> pArgs, FunctionDeclaration<?> pFunctionDeclaration) {
    CanonizingFormula function = null;
    FormulaType<?> returnType = pFunctionDeclaration.getType();
    FunctionDeclarationKind kind = pFunctionDeclaration.getKind();

    if (kind == FunctionDeclarationKind.OTHER) {
      // FIXME: That's really bad...
      if (pFunctionDeclaration.toString().contains("bvsext")) {
        kind = FunctionDeclarationKind.BV_SIGN_EXTENSION;
      } else if (pFunctionDeclaration.toString().contains("bvzext")) {
        kind = FunctionDeclarationKind.BV_ZERO_EXTENSION;
      } else if (pFunctionDeclaration.toString().contains("fpfromubv")) {
        kind = FunctionDeclarationKind.BV_UCASTTO_FP;
      } else if (pFunctionDeclaration.toString().contains("fpcast")) {
        kind = FunctionDeclarationKind.FP_CASTTO_FP;
      } else if (pFunctionDeclaration.toString().contains("fpisnan")) {
        kind = FunctionDeclarationKind.FP_IS_NAN;
      } else if (pFunctionDeclaration.toString().contains("fpisinf")) {
        kind = FunctionDeclarationKind.FP_IS_INF;
      } else if (pFunctionDeclaration.toString().contains("fpiszero")) {
        kind = FunctionDeclarationKind.FP_IS_ZERO;
      } else if (pFunctionDeclaration.toString().contains("fpissubnormal")) {
        kind = FunctionDeclarationKind.FP_IS_SUBNORMAL;
      } else if (pFunctionDeclaration.toString().contains("fpfromsbv")) {
        kind = FunctionDeclarationKind.BV_SCASTTO_FP;
      } else if (pFunctionDeclaration.toString().contains("fptobv")) {
        kind = FunctionDeclarationKind.FP_CASTTO_BV;
      } else if (pFunctionDeclaration.toString().contains("fpasbv")) {
        kind = FunctionDeclarationKind.FP_AS_BV;
      } else if (pFunctionDeclaration.toString().contains("fpfromieeebv")) {
        kind = FunctionDeclarationKind.FP_FROM_BV;
      }
    }

    List<CanonizingFormula> args = new ArrayList<>();
    if (kind == FunctionDeclarationKind.UF) {
      for (int i = 0; i < pArgs.size(); i++) {
        store.storeType(pFunctionDeclaration.getArgumentTypes().get(i));
        args.add(mgr.visit(pArgs.get(i), this));
      }

      function =
          CanonizingPrefixOperator.getInstance(
              mgr, kind, args, pFunctionDeclaration.getType(), pFunctionDeclaration.getName());
    } else {
      switch (pArgs.size()) {
        case 0:
          function = CanonizingPrefixOperator.getInstance(mgr, kind, new ArrayList<>(), returnType);
          break;
        case 1:
        case 3:
        case 4: // PRINCESS: extract
          for (int i = 0; i < pArgs.size(); i++) {
            store.storeType(pFunctionDeclaration.getArgumentTypes().get(i));
            args.add(mgr.visit(pArgs.get(i), this));
          }

          // FIXME: MathSAT and Z3 simplify bvextract with 3 parameters to a function with only 1
          // parameter, so at the moment we have to use this ugly and error-prone hack to determine
          // the ranges of the extract
          //
          // Princess also needs a special handling, since it creates some 4-argument function with
          // reordering in the arguments
          if (kind == FunctionDeclarationKind.BV_EXTRACT
              || kind == FunctionDeclarationKind.BV_SIGN_EXTENSION
              || kind == FunctionDeclarationKind.BV_ZERO_EXTENSION) {
            if (mgr.getClass().getName().contains("Mathsat")
                || mgr.getClass().getName().contains("Z3")) {
              String rawFunction = pF.toString();
              Matcher matcher =
                  Pattern.compile(".*?([0-9]{1,4}).*?([0-9]{1,4}).*").matcher(rawFunction);
              if (matcher.matches()) {
                String argument1 = matcher.group(1);
                String argument2 = matcher.group(2);
                args.add(
                    store.remember(
                        CanonizingConstant.getInstance(
                            mgr, Integer.parseInt(argument1), FormulaType.IntegerType)));
                args.add(
                    store.remember(
                        CanonizingConstant.getInstance(
                            mgr, Integer.parseInt(argument2), FormulaType.IntegerType)));
              }
            }
            if (mgr.getClass().getName().contains("Princess")) {
              args.clear();
              store.storeType(pFunctionDeclaration.getArgumentTypes().get(3));
              args.add(mgr.visit(pArgs.get(3), this));

              store.storeType(pFunctionDeclaration.getArgumentTypes().get(1));
              CanonizingConstant arg1inter = (CanonizingConstant) mgr.visit(pArgs.get(1), this);
              store.storeType(pFunctionDeclaration.getArgumentTypes().get(2));
              CanonizingConstant arg2 = (CanonizingConstant) mgr.visit(pArgs.get(2), this);

              Integer arg1Calculated =
                  ((BigInteger) arg1inter.getValue()).add(((BigInteger) arg2.getValue())).intValue()
                      - 1;

              CanonizingFormula arg1 =
                  store.remember(
                      CanonizingConstant.getInstance(mgr, arg1Calculated, FormulaType.IntegerType));
              arg2 =
                  (CanonizingConstant)
                      store.remember(
                          CanonizingConstant.getInstance(
                              mgr,
                              ((BigInteger) arg2.getValue()).intValue(),
                              FormulaType.IntegerType));

              args.add(arg1);
              args.add(arg2);
            }
          }

          function = CanonizingPrefixOperator.getInstance(mgr, kind, args, returnType);
          break;
        case 2:
          // FIXME: PRRINCESS-Multiply can have one argument of type Integer and one argument of
          // type bitvector at this point - how to handle something like that?
          store.storeType(pFunctionDeclaration.getArgumentTypes().get(0));
          CanonizingFormula left = mgr.visit(pArgs.get(0), this);
          store.storeType(pFunctionDeclaration.getArgumentTypes().get(1));
          CanonizingFormula right = mgr.visit(pArgs.get(1), this);

          if (kind == FunctionDeclarationKind.SELECT
              || kind == FunctionDeclarationKind.BV_UCASTTO_FP) {
            List<CanonizingFormula> operands = new ArrayList<>();
            operands.add(left);
            operands.add(right);
            function = CanonizingPrefixOperator.getInstance(mgr, kind, operands, returnType);
          } else {
            function = CanonizingInfixOperator.getInstance(mgr, kind, left, right, returnType);
          }
          break;
        default:
          // FIXME: SMTINTERPOL seems to construct AND and maybe OR and other operators as well with
          // arbitrary argument-lists
          throw new IllegalStateException(
              "No handling for function "
                  + pFunctionDeclaration.getName()
                  + " with "
                  + pArgs.size()
                  + " Parameters known.");
      }
    }

    function = store.remember(function);
    store.storeOperator(function);
    store.closeOperand(function);

    return function;
  }

  @Override
  public CanonizingFormula visitQuantifier(
      BooleanFormula pF,
      Quantifier pQuantifier,
      List<Formula> pBoundVariables,
      BooleanFormula pBody) {
    // TODO Auto-generated method stub
    return null;
  }

  public void push() {
    store.push();
  }

  public void pop() {
    store.pop();
  }
}
