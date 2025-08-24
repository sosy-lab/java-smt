/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class TraceFormulaManager implements FormulaManager {
  private final FormulaManager delegate;
  private TraceLogger logger;

  TraceFormulaManager(FormulaManager pDelegate) {
    delegate = pDelegate;
  }

  void setLogger(TraceLogger pLogger) {
    logger = pLogger;
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    return new TraceIntegerFormulaManager(delegate.getIntegerFormulaManager(), logger);
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormulaManager getBooleanFormulaManager() {
    return new TraceBooleanFormulaManager(delegate.getBooleanFormulaManager(), logger);
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    return new TraceArrayFormulaManager(delegate.getArrayFormulaManager(), logger);
  }

  @Override
  public BitvectorFormulaManager getBitvectorFormulaManager() {
    return new TraceBitvectorFormulaManager(delegate.getBitvectorFormulaManager(), logger);
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    return new TraceFloatingPointFormulaManager(delegate.getFloatingPointFormulaManager(), logger);
  }

  @Override
  public UFManager getUFManager() {
    return new TraceUFManager(delegate.getUFManager(), this, logger);
  }

  @Override
  public SLFormulaManager getSLFormulaManager() {
    throw new UnsupportedOperationException();
  }

  @Override
  public QuantifiedFormulaManager getQuantifiedFormulaManager() {
    throw new UnsupportedOperationException();
  }

  @Override
  public StringFormulaManager getStringFormulaManager() {
    throw new UnsupportedOperationException();
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    throw new UnsupportedOperationException();
  }

  private class Rebuilder extends FormulaTransformationVisitor {
    protected Rebuilder(FormulaManager fmgr) {
      super(fmgr);
    }

    @Override
    public Formula visitFreeVariable(Formula f, String name) {
      if (!logger.isTracked(f)) {
        var g =
            logger.logDef(
                "mgr",
                String.format(
                    "makeVariable(%s, %s)",
                    logger.printFormulaType(delegate.getFormulaType(f)), name),
                () -> delegate.makeVariable(delegate.getFormulaType(f), name));
        Preconditions.checkArgument(g.equals(f));
      }
      return f;
    }

    @Override
    public Formula visitConstant(Formula f, Object value) {
      if (!logger.isTracked(f)) {
        if (f instanceof BooleanFormula && value instanceof Boolean) {
          var g =
              logger.logDef(
                  "mgr.getBooleanFormulaManager()",
                  String.format("makeBoolean(%s)", value),
                  () -> delegate.getBooleanFormulaManager().makeBoolean((Boolean) value));
          Preconditions.checkArgument(g.equals(f));
        } else if (f instanceof BitvectorFormula && value instanceof BigInteger) {
          var bvSize = delegate.getBitvectorFormulaManager().getLength((BitvectorFormula) f);
          var g =
              logger.logDef(
                  "mgr.getBitvectorFormulaManager()",
                  String.format("makeBitvector(%s, %s)", bvSize, value),
                  () ->
                      delegate
                          .getBitvectorFormulaManager()
                          .makeBitvector(bvSize, (BigInteger) value));
          Preconditions.checkArgument(g.equals(f));
        } else if (f instanceof IntegerFormula && value instanceof BigInteger) {
          var g =
              logger.logDef(
                  "mgr.getIntegerFormulaManager()",
                  String.format("makeNumber(%s)", value),
                  () -> delegate.getIntegerFormulaManager().makeNumber((BigInteger) value));
          Preconditions.checkArgument(g.equals(f));
        } else {
          throw new IllegalArgumentException(
              String.format(
                  "Unsupported value: Formula=%s, Value=%s",
                  delegate.getFormulaType(f), value.getClass().getName()));
        }
      }
      return f;
    }

    @Override
    public Formula visitFunction(
        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
      if (!logger.isTracked(f)) {
        Formula g = makeApplication(functionDeclaration, args);
        // FIXME Remove the assertion? Argument order can change, f.ex (and a b) becomes (and b a)
        // Preconditions.checkArgument(g.equals(f));
      }
      return f;
    }

    @Override
    public BooleanFormula visitQuantifier(
        BooleanFormula f,
        Quantifier quantifier,
        List<Formula> boundVariables,
        BooleanFormula body) {
      throw new UnsupportedOperationException();
    }
  }

  public <T extends Formula> T rebuild(T f) {
    return delegate.transformRecursively(f, new TraceFormulaManager.Rebuilder(this));
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    String var = logger.newVariable();
    logger.appendDef(
        var,
        String.format("mgr.makeVariable(%s, \"%s\")", logger.printFormulaType(formulaType), name));
    T f = delegate.makeVariable(formulaType, name);
    if (logger.isTracked(f)) {
      logger.undoLast();
    }
    return f;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args) {
    if (declaration.getKind().equals(FunctionDeclarationKind.UF)) {
      var uf =
          getUFManager()
              .declareUF(
                  declaration.getName(), declaration.getType(), declaration.getArgumentTypes());
      return getUFManager().callUF(uf, args);
    } else {
      // TODO Check that the number of arguments matches the arity of the operation
      // TODO Figure out how to handle rounding mode for floats
      switch (declaration.getKind()) {
        case AND:
          return (T)
              getBooleanFormulaManager()
                  .and((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
        case NOT:
          return (T) getBooleanFormulaManager().not((BooleanFormula) args.get(0));
        case OR:
          return (T)
              getBooleanFormulaManager()
                  .or((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
        case IFF:
          return (T)
              getBooleanFormulaManager()
                  .equivalence((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
        case ITE:
          return getBooleanFormulaManager()
              .ifThenElse((BooleanFormula) args.get(0), (T) args.get(1), (T) args.get(2));
        case XOR:
          return (T)
              getBooleanFormulaManager()
                  .xor((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
        case IMPLIES:
          return (T)
              getBooleanFormulaManager()
                  .implication((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
        case DISTINCT:
          // TODO We only have 'distinct' for some theories
          break;
        case STORE:
          return (T)
              getArrayFormulaManager().store((ArrayFormula) args.get(0), args.get(1), args.get(2));
        case SELECT:
          return (T) getArrayFormulaManager().select((ArrayFormula) args.get(0), args.get(1));
        case CONST:
          return (T)
              getArrayFormulaManager()
                  .makeArray((ArrayFormulaType) declaration.getType(), args.get(0));
        case UMINUS:
          // FIXME Handle rational formulas
          return (T) getIntegerFormulaManager().negate((IntegerFormula) args.get(0));
        case SUB:
          return (T)
              getIntegerFormulaManager()
                  .subtract((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
        case ADD:
          return (T)
              getIntegerFormulaManager()
                  .add((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
        case DIV:
          return (T)
              getIntegerFormulaManager()
                  .divide((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
        case MUL:
          return (T)
              getIntegerFormulaManager()
                  .multiply((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
        case MODULO:
          return (T)
              getIntegerFormulaManager()
                  .modulo((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
        case LT:
          return (T)
              getIntegerFormulaManager()
                  .lessThan((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
        case LTE:
          return (T)
              getIntegerFormulaManager()
                  .lessOrEquals((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
        case GT:
          return (T)
              getIntegerFormulaManager()
                  .greaterThan((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
        case GTE:
          return (T)
              getIntegerFormulaManager()
                  .greaterOrEquals((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
        case EQ:
          {
            if (declaration.getArgumentTypes().get(0).isBooleanType()) {
              return (T)
                  getBooleanFormulaManager()
                      .equivalence((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
            } else if (declaration.getArgumentTypes().get(1).isIntegerType()) {
              return (T)
                  getIntegerFormulaManager()
                      .equal((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
            } else if (declaration.getArgumentTypes().get(1).isBitvectorType()) {
              return (T)
                  getBitvectorFormulaManager()
                      .equal((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
            } else if (declaration.getArgumentTypes().get(1).isArrayType()) {
              return (T)
                  getArrayFormulaManager()
                      .equivalence((ArrayFormula) args.get(0), (ArrayFormula) args.get(1));
            } else {
              throw new UnsupportedOperationException(
                  String.format(
                      "EQ not supported for theory " + "%s",
                      declaration.getArgumentTypes().get(0)));
            }
          }
        /*
        case EQ_ZERO:
          break;
        case GTE_ZERO:
          break;
        case FLOOR:
          break;
        case TO_REAL:
          break;
        */
        case BV_EXTRACT:
          {
            String[] tokens = declaration.getName().split("_");
            return (T)
                getBitvectorFormulaManager()
                    .extract(
                        (BitvectorFormula) args.get(0),
                        Integer.parseInt(tokens[1]),
                        Integer.parseInt(tokens[2]));
          }
        case BV_CONCAT:
          return (T)
              getBitvectorFormulaManager()
                  .concat((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_SIGN_EXTENSION:
          // TODO
          break;
        case BV_ZERO_EXTENSION:
          // TODO
          break;
        case BV_NOT:
          return (T) getBitvectorFormulaManager().not((BitvectorFormula) args.get(0));
        case BV_NEG:
          return (T) getBitvectorFormulaManager().negate((BitvectorFormula) args.get(0));
        case BV_OR:
          return (T)
              getBitvectorFormulaManager()
                  .or((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_AND:
          return (T)
              getBitvectorFormulaManager()
                  .and((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_XOR:
          return (T)
              getBitvectorFormulaManager()
                  .xor((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_SUB:
          return (T)
              getBitvectorFormulaManager()
                  .subtract((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_ADD:
          return (T)
              getBitvectorFormulaManager()
                  .add((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_SDIV:
          return (T)
              getBitvectorFormulaManager()
                  .divide((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_UDIV:
          return (T)
              getBitvectorFormulaManager()
                  .divide((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SREM:
          return (T)
              getBitvectorFormulaManager()
                  .remainder((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_UREM:
          return (T)
              getBitvectorFormulaManager()
                  .remainder((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SMOD:
          return (T)
              getBitvectorFormulaManager()
                  .smodulo((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_MUL:
          return (T)
              getBitvectorFormulaManager()
                  .multiply((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_ULT:
          return (T)
              getBitvectorFormulaManager()
                  .lessThan((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SLT:
          return (T)
              getBitvectorFormulaManager()
                  .lessThan((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_ULE:
          return (T)
              getBitvectorFormulaManager()
                  .lessOrEquals(
                      (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SLE:
          return (T)
              getBitvectorFormulaManager()
                  .lessOrEquals(
                      (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_UGT:
          return (T)
              getBitvectorFormulaManager()
                  .greaterThan(
                      (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SGT:
          return (T)
              getBitvectorFormulaManager()
                  .greaterThan(
                      (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_UGE:
          return (T)
              getBitvectorFormulaManager()
                  .greaterOrEquals(
                      (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SGE:
          return (T)
              getBitvectorFormulaManager()
                  .greaterOrEquals(
                      (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_EQ: // FIXME Why is this a separate symbol?
          return (T)
              getBitvectorFormulaManager()
                  .equal((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_SHL:
          return (T)
              getBitvectorFormulaManager()
                  .shiftLeft((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_LSHR:
          return (T)
              getBitvectorFormulaManager()
                  .shiftRight(
                      (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_ASHR:
          return (T)
              getBitvectorFormulaManager()
                  .shiftRight((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_ROTATE_LEFT:
          return (T)
              getBitvectorFormulaManager()
                  .rotateLeft((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_ROTATE_RIGHT:
          return (T)
              getBitvectorFormulaManager()
                  .rotateRight((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_ROTATE_LEFT_BY_INT:
          // TODO
          break;
        case BV_ROTATE_RIGHT_BY_INT:
          // TODO
          break;
        case BV_UCASTTO_FP:
          return (T)
              getFloatingPointFormulaManager()
                  .castFrom(args.get(0), false, (FloatingPointType) declaration.getType());
        case BV_SCASTTO_FP:
          return (T)
              getFloatingPointFormulaManager()
                  .castFrom(args.get(0), true, (FloatingPointType) declaration.getType());
        case FP_NEG:
          return (T) getFloatingPointFormulaManager().negate((FloatingPointFormula) args.get(0));
        case FP_ABS:
          return (T) getFloatingPointFormulaManager().abs((FloatingPointFormula) args.get(0));
        case FP_MAX:
          return (T)
              getFloatingPointFormulaManager()
                  .max((FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_MIN:
          return (T)
              getFloatingPointFormulaManager()
                  .min((FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_SQRT:
          return (T) getFloatingPointFormulaManager().sqrt((FloatingPointFormula) args.get(0));
        case FP_SUB:
          return (T)
              getFloatingPointFormulaManager()
                  .subtract((FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_ADD:
          return (T)
              getFloatingPointFormulaManager()
                  .add((FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_DIV:
          return (T)
              getFloatingPointFormulaManager()
                  .divide((FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_REM:
          return (T)
              getFloatingPointFormulaManager()
                  .remainder(
                      (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_MUL:
          return (T)
              getFloatingPointFormulaManager()
                  .multiply((FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_LT:
          return (T)
              getFloatingPointFormulaManager()
                  .lessThan((FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_LE:
          return (T)
              getFloatingPointFormulaManager()
                  .lessOrEquals(
                      (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_GE:
          return (T)
              getFloatingPointFormulaManager()
                  .greaterOrEquals(
                      (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_GT:
          return (T)
              getFloatingPointFormulaManager()
                  .greaterThan(
                      (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_EQ:
          return (T)
              getFloatingPointFormulaManager()
                  .equalWithFPSemantics(
                      (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_ROUND_EVEN:
          break;
        case FP_ROUND_AWAY:
          break;
        case FP_ROUND_POSITIVE:
          break;
        case FP_ROUND_NEGATIVE:
          break;
        case FP_ROUND_ZERO:
          break;
        case FP_ROUND_TO_INTEGRAL:
          {
            var rm = (FloatingPointRoundingModeFormula) args.get(1);
            System.out.println("Rounding Mode: " + rm);
            return (T)
                getFloatingPointFormulaManager()
                    .round(
                        (FloatingPointFormula) args.get(0),
                        FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
          }
        case FP_IS_NAN:
          return (T) getFloatingPointFormulaManager().isNaN((FloatingPointFormula) args.get(0));
        case FP_IS_INF:
          return (T)
              getFloatingPointFormulaManager().isInfinity((FloatingPointFormula) args.get(0));
        case FP_IS_ZERO:
          return (T) getFloatingPointFormulaManager().isZero((FloatingPointFormula) args.get(0));
        case FP_IS_NEGATIVE:
          return (T)
              getFloatingPointFormulaManager().isNegative((FloatingPointFormula) args.get(0));
        case FP_IS_SUBNORMAL:
          return (T)
              getFloatingPointFormulaManager().isSubnormal((FloatingPointFormula) args.get(0));
        case FP_IS_NORMAL:
          return (T) getFloatingPointFormulaManager().isNormal((FloatingPointFormula) args.get(0));
        case FP_CASTTO_FP:
          return getFloatingPointFormulaManager()
              .castTo((FloatingPointFormula) args.get(0), true, declaration.getType());
        case FP_CASTTO_SBV:
          return getFloatingPointFormulaManager()
              .castTo((FloatingPointFormula) args.get(0), true, declaration.getType());
        case FP_CASTTO_UBV:
          return getFloatingPointFormulaManager()
              .castTo((FloatingPointFormula) args.get(0), false, declaration.getType());
        case FP_AS_IEEEBV:
          return (T)
              getFloatingPointFormulaManager().toIeeeBitvector((FloatingPointFormula) args.get(0));
        case FP_FROM_IEEEBV:
          return (T)
              getFloatingPointFormulaManager()
                  .fromIeeeBitvector(
                      (BitvectorFormula) args.get(0), (FloatingPointType) declaration.getType());
        /*
        case STR_CONCAT:
          break;
        case STR_PREFIX:
          break;
        case STR_SUFFIX:
          break;
        case STR_CONTAINS:
          break;
        case STR_SUBSTRING:
          break;
        case STR_REPLACE:
          break;
        case STR_REPLACE_ALL:
          break;
        case STR_CHAR_AT:
          break;
        case STR_LENGTH:
          break;
        case STR_INDEX_OF:
          break;
        case STR_TO_RE:
          break;
        case STR_IN_RE:
          break;
        case STR_TO_INT:
          break;
        case INT_TO_STR:
          break;
        case STR_FROM_CODE:
          break;
        case STR_TO_CODE:
          break;
        case STR_LT:
          break;
        case STR_LE:
          break;
        case RE_PLUS:
          break;
        case RE_STAR:
          break;
        case RE_OPTIONAL:
          break;
        case RE_CONCAT:
          break;
        case RE_UNION:
          break;
        case RE_RANGE:
          break;
        case RE_INTERSECT:
          break;
        case RE_COMPLEMENT:
          break;
        case RE_DIFFERENCE:
          break;
        case OTHER:
          break;
          */
        default:
          throw new UnsupportedOperationException(
              String.format(
                  "Operation not supported: %s, (%s)",
                  declaration.getKind(), declaration.getName()));
      }
    }
    throw new UnsupportedOperationException();
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, Formula... args) {
    return makeApplication(declaration, ImmutableList.copyOf(args));
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    return logger.logDefDiscard(
        "mgr",
        String.format("getFormulaType(%s)", logger.toVariable(formula)),
        () -> delegate.getFormulaType(formula));
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    logger.appendStmt(String.format("mgr.parse(\"%s\")", s));
    BooleanFormula f = delegate.parse(s);
    logger.undoLast();
    return rebuild(f);
  }

  @Override
  public Appender dumpFormula(BooleanFormula pT) {
    logger.appendStmt(String.format("mgr.dumpFormula(%s)", logger.toVariable(pT)));
    Appender str = delegate.dumpFormula(pT);
    logger.undoLast();
    return str;
  }

  @Override
  public BooleanFormula applyTactic(BooleanFormula input, Tactic tactic)
      throws InterruptedException, SolverException {
    return logger.logDef(
        "mgr",
        String.format("applyTactic(%s, %s)", logger.toVariable(input), "Tactic" + tactic.name()),
        () -> delegate.applyTactic(input, tactic));
  }

  @Override
  public <T extends Formula> T simplify(T input) throws InterruptedException {
    return logger.logDef(
        "mgr",
        String.format("simplify(%s)", logger.toVariable(input)),
        () -> delegate.simplify(input));
  }

  @Override
  public <R> R visit(Formula f, FormulaVisitor<R> rFormulaVisitor) {
    return logger.logDefDiscard(
        "mgr",
        String.format(
            "visit(%s, new DefaultFormulaVisitor<>() {"
                + "protected Formula visitDefault(Formula f) {"
                + "return f;"
                + "}})",
            logger.toVariable(f)),
        () -> delegate.visit(f, rFormulaVisitor));
  }

  @Override
  public void visitRecursively(Formula f, FormulaVisitor<TraversalProcess> rFormulaVisitor) {
    logger.logStmtDiscard(
        "mgr",
        String.format(
            "visitRecursively(%s, new DefaultFormulaVisitor<>() {"
                + "protected TraversalProcess visitDefault(Formula f) {"
                + "return TraversalProcess.CONTINUE;"
                + "}})",
            logger.toVariable(f)),
        () -> delegate.visitRecursively(f, rFormulaVisitor));
  }

  @Override
  public <T extends Formula> T transformRecursively(
      T f, FormulaTransformationVisitor pFormulaVisitor) {
    return logger.logDefDiscard(
        "mgr",
        String.format(
            "transformRecursively(%s, new FormulaTransformationVisitor(%s) {})",
            logger.toVariable(f), "mgr"),
        () -> delegate.transformRecursively(f, pFormulaVisitor));
  }

  @Override
  public ImmutableMap<String, Formula> extractVariables(Formula f) {
    return logger.logDefDiscard(
        "mgr",
        String.format("extractVariables(%s)", logger.toVariable(f)),
        () -> delegate.extractVariables(f));
  }

  @Override
  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f) {
    return logger.logDefDiscard(
        "mgr",
        String.format("extractVariablesAndUFs(%s)", logger.toVariable(f)),
        () -> delegate.extractVariablesAndUFs(f));
  }

  @Override
  public <T extends Formula> T substitute(
      T f, Map<? extends Formula, ? extends Formula> fromToMapping) {
    return logger.logDef(
        "mgr",
        String.format(
            "substitute(%s, ImmutableMap.ofEntries(%s))",
            logger.toVariable(f),
            FluentIterable.from(fromToMapping.entrySet())
                .transform(
                    entry ->
                        String.format(
                            "Map.entry(%s, %s)",
                            logger.toVariable(entry.getKey()), logger.toVariable(entry.getValue())))
                .join(Joiner.on(", "))),
        () -> delegate.substitute(f, fromToMapping));
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    // TODO Write API calls from all contexts into one file to allow us to support this method
    throw new UnsupportedOperationException();
  }

  @Override
  public boolean isValidName(String variableName) {
    return delegate.isValidName(variableName);
  }

  @Override
  public String escape(String variableName) {
    return delegate.escape(variableName);
  }

  @Override
  public String unescape(String variableName) {
    return delegate.unescape(variableName);
  }
}
