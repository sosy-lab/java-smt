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

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableListCopy;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableSetCopy;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
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
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

class TraceFormulaManager implements FormulaManager {
  private final FormulaManager delegate;
  private TraceLogger logger;
  private final LogManager logManager;
  private final boolean failOnError;

  TraceFormulaManager(FormulaManager pDelegate, LogManager pLogManager, boolean pFailOnError) {
    delegate = pDelegate;
    logManager = pLogManager;
    failOnError = pFailOnError;
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
    return new TraceRationalFormulaManager(delegate.getRationalFormulaManager(), logger);
  }

  @Override
  public BooleanFormulaManager getBooleanFormulaManager() {
    return new TraceBooleanFormulaManager(delegate.getBooleanFormulaManager(), this, logger);
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
    return new TraceSLFormulaManager(delegate.getSLFormulaManager(), logger);
  }

  @Override
  public QuantifiedFormulaManager getQuantifiedFormulaManager() {
    return new TraceQuantifiedFormulaManager(delegate.getQuantifiedFormulaManager(), this, logger);
  }

  @Override
  public StringFormulaManager getStringFormulaManager() {
    return new TraceStringFormulaManager(delegate.getStringFormulaManager(), logger);
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    return new TraceEnumerationFormulaManager(delegate.getEnumerationFormulaManager(), logger);
  }

  private class Rebuilder extends FormulaTransformationVisitor {
    Rebuilder(FormulaManager fmgr) {
      super(fmgr);
    }

    @Override
    public Formula visitFreeVariable(Formula f, String name) {
      if (!logger.isTracked(f)) {
        var g = makeVariable(delegate.getFormulaType(f), name);
        if (!g.equals(f)) { // can happen after simplifications, bad for tracing, but happens.
          var msg = "Formula '%s' is not an identity of '%s'.".formatted(g, f);
          if (failOnError) {
            throw new IllegalArgumentException(msg);
          } else {
            logManager.log(Level.WARNING, msg);
          }
          logger.mapVariable(logger.toVariable(g), f);
        }
      }
      return f;
    }

    @Override
    public Formula visitConstant(Formula f, Object value) {
      if (!logger.isTracked(f)) {
        Formula g;
        // FIXME Add a case for enum formulas
        if (f instanceof BooleanFormula && value instanceof Boolean booleanValue) {
          g = getBooleanFormulaManager().makeBoolean(booleanValue);
        } else if (f instanceof BitvectorFormula bvFormula
            && value instanceof BigInteger bigIntValue) {
          var bvSize = delegate.getBitvectorFormulaManager().getLength(bvFormula);
          g = getBitvectorFormulaManager().makeBitvector(bvSize, bigIntValue);
        } else if (f instanceof IntegerFormula && value instanceof BigInteger bigIntValue) {
          g = getIntegerFormulaManager().makeNumber(bigIntValue);
        } else if (f instanceof RationalFormula && value instanceof BigInteger bigIntValue) {
          g = getRationalFormulaManager().makeNumber(bigIntValue);
        } else if (f instanceof RationalFormula && value instanceof Rational rationalValue) {
          g = getRationalFormulaManager().makeNumber(rationalValue);
        } else if (f instanceof FloatingPointFormula
            && value instanceof FloatingPointNumber fpValue) {
          g = getFloatingPointFormulaManager().makeNumber(fpValue);
        } else if (f instanceof FloatingPointRoundingModeFormula
            && value instanceof FloatingPointRoundingMode fpRoundingMode) {
          g = getFloatingPointFormulaManager().makeRoundingMode(fpRoundingMode);
        } else if (f instanceof StringFormula && value instanceof String stringValue) {
          g = getStringFormulaManager().makeString(stringValue);
        } else {
          throw new IllegalArgumentException(
              "Unsupported value: Formula=%s, Value=%s"
                  .formatted(delegate.getFormulaType(f), value.getClass().getName()));
        }
        if (!g.equals(f)) { // can happen after simplifications, bad for tracing, but happens.
          var msg = "Formula '%s' is not an identity of '%s'.".formatted(g, f);
          if (failOnError) {
            throw new IllegalArgumentException(msg);
          } else {
            logManager.log(Level.WARNING, msg);
          }
          logger.mapVariable(logger.toVariable(g), f);
        }
      }
      return f;
    }

    @SuppressWarnings("CheckReturnValue")
    @Override
    public Formula visitFunction(
        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
      if (!logger.isTracked(f)) {
        Formula g = makeApplication(functionDeclaration, args);
        if (!g.equals(f)) { // can happen after simplifications, bad for tracing, but happens.
          var msg = "Formula '%s' is not an identity of '%s'.".formatted(g, f);
          if (failOnError) {
            throw new IllegalArgumentException(msg);
          } else {
            logManager.log(Level.WARNING, msg);
          }
          logger.mapVariable(logger.toVariable(g), f);
        }
      }
      return f;
    }

    @SuppressWarnings("CheckReturnValue")
    @Override
    public BooleanFormula visitQuantifier(
        BooleanFormula f,
        Quantifier quantifier,
        List<Formula> boundVariables,
        BooleanFormula body) {
      if (!logger.isTracked(f)) {
        var bound = rebuildAll(boundVariables);
        final Formula g;
        if (quantifier == Quantifier.EXISTS) {
          g = getQuantifiedFormulaManager().exists(bound, body);
        } else {
          g = getQuantifiedFormulaManager().forall(bound, body);
        }
        if (!g.equals(f)) { // can happen after simplifications, bad for tracing, but happens.
          var msg = "Formula '%s' is not an identity of '%s'.".formatted(g, f);
          if (failOnError) {
            throw new IllegalArgumentException(msg);
          } else {
            logManager.log(Level.WARNING, msg);
          }
          logger.mapVariable(logger.toVariable(g), f);
        }
      }
      return f;
    }
  }

  public <T extends Formula> T rebuild(T f) {
    return delegate.transformRecursively(f, new TraceFormulaManager.Rebuilder(this));
  }

  public <T extends Formula> List<T> rebuildAll(List<T> formulas) {
    return transformedImmutableListCopy(formulas, this::rebuild);
  }

  public <T extends Formula> Set<T> rebuildAll(Set<T> formulas) {
    return transformedImmutableSetCopy(formulas, this::rebuild);
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    return logger.logDef(
        "mgr",
        "makeVariable(%s, %s)"
            .formatted(logger.printFormulaType(formulaType), logger.printString(name)),
        () -> delegate.makeVariable(formulaType, name));
  }

  private <T extends Formula> int getArity(FunctionDeclaration<T> pDeclaration) {
    return FunctionDeclarationKind.getArity(pDeclaration.getKind());
  }

  @SuppressWarnings({"unchecked", "rawtypes"})
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
      Preconditions.checkArgument(
          getArity(declaration) == -1 ? args.size() > 1 : args.size() == getArity(declaration),
          "Term \"%s\" (%s): expecting %s arguments, but found %s",
          declaration.getName(),
          declaration.getKind(),
          getArity(declaration),
          args.size());
      return switch (declaration.getKind()) {
        case AND -> (T) getBooleanFormulaManager().and((List<BooleanFormula>) args);
        case NOT -> (T) getBooleanFormulaManager().not((BooleanFormula) args.get(0));
        case OR -> (T) getBooleanFormulaManager().or((List<BooleanFormula>) args);
        case IFF -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getBooleanFormulaManager()
                  .equivalence((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
        }
        case ITE ->
            getBooleanFormulaManager()
                .ifThenElse((BooleanFormula) args.get(0), (T) args.get(1), (T) args.get(2));
        case XOR -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getBooleanFormulaManager()
                  .xor((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
        }
        case IMPLIES -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getBooleanFormulaManager()
                  .implication((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
        }
        case DISTINCT -> (T) makeDistinct((Iterable<Formula>) args);
        case STORE ->
            (T)
                getArrayFormulaManager()
                    .store((ArrayFormula) args.get(0), args.get(1), args.get(2));
        case SELECT -> (T) getArrayFormulaManager().select((ArrayFormula) args.get(0), args.get(1));
        case CONST ->
            (T)
                getArrayFormulaManager()
                    .makeArray((ArrayFormulaType) declaration.getType(), args.get(0));
        case UMINUS -> {
          if (declaration.getType().isIntegerType()) {
            yield (T) getIntegerFormulaManager().negate((IntegerFormula) args.get(0));
          } else {
            yield (T) getRationalFormulaManager().negate((NumeralFormula) args.get(0));
          }
        }
        case SUB -> {
          Preconditions.checkArgument(args.size() == 2);
          if (declaration.getType().isIntegerType()) {
            yield (T)
                getIntegerFormulaManager()
                    .subtract((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
          } else {
            yield (T)
                getRationalFormulaManager()
                    .subtract((NumeralFormula) args.get(0), (NumeralFormula) args.get(1));
          }
        }
        case ADD -> {
          if (declaration.getType().isIntegerType()) {
            yield (T) getIntegerFormulaManager().sum((List<IntegerFormula>) args);
          } else {
            yield (T) getRationalFormulaManager().sum((List<NumeralFormula>) args);
          }
        }
        case DIV -> {
          Preconditions.checkArgument(args.size() == 2);
          if (declaration.getType().isIntegerType()) {
            yield (T)
                getIntegerFormulaManager()
                    .divide((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
          } else {
            yield (T)
                getRationalFormulaManager()
                    .divide((NumeralFormula) args.get(0), (NumeralFormula) args.get(1));
          }
        }
        case MUL -> {
          Preconditions.checkArgument(args.size() == 2);
          if (declaration.getType().isIntegerType()) {
            yield (T)
                getIntegerFormulaManager()
                    .multiply((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
          } else {
            yield (T)
                getRationalFormulaManager()
                    .multiply((NumeralFormula) args.get(0), (NumeralFormula) args.get(1));
          }
        }
        case MODULO ->
            (T)
                getIntegerFormulaManager()
                    .modulo((IntegerFormula) args.get(0), (IntegerFormula) args.get(1));
        case LT -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getRationalFormulaManager()
                  .lessThan((NumeralFormula) args.get(0), (NumeralFormula) args.get(1));
        }
        case LTE -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getRationalFormulaManager()
                  .lessOrEquals((NumeralFormula) args.get(0), (NumeralFormula) args.get(1));
        }
        case GT -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getRationalFormulaManager()
                  .greaterThan((NumeralFormula) args.get(0), (NumeralFormula) args.get(1));
        }
        case GTE -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getRationalFormulaManager()
                  .greaterOrEquals((NumeralFormula) args.get(0), (NumeralFormula) args.get(1));
        }
        case EQ -> (T) makeEqual((Iterable<Formula>) args);
        case EQ_ZERO -> {
          if (args.get(0) instanceof IntegerFormula) {
            yield (T)
                getIntegerFormulaManager()
                    .equal((IntegerFormula) args.get(0), getIntegerFormulaManager().makeNumber(0));
          } else {
            yield (T)
                getRationalFormulaManager()
                    .equal((NumeralFormula) args.get(0), getRationalFormulaManager().makeNumber(0));
          }
        }
        case GTE_ZERO -> {
          if (args.get(0) instanceof IntegerFormula) {
            yield (T)
                getIntegerFormulaManager()
                    .greaterOrEquals(
                        (IntegerFormula) args.get(0), getIntegerFormulaManager().makeNumber(0));
          } else {
            yield (T)
                getRationalFormulaManager()
                    .greaterOrEquals(
                        (NumeralFormula) args.get(0), getRationalFormulaManager().makeNumber(0));
          }
        }
        case TO_REAL ->
            (T) getRationalFormulaManager().sum(ImmutableList.of((NumeralFormula) args.get(0)));
        case FLOOR -> {
          if (args.get(0) instanceof IntegerFormula) {
            yield (T) getIntegerFormulaManager().floor((IntegerFormula) args.get(0));
          } else {
            yield (T) getRationalFormulaManager().floor((NumeralFormula) args.get(0));
          }
        }
        case INT_TO_BV -> {
          checkArgument(declaration.getIndices().size() == 1);
          yield (T)
              getBitvectorFormulaManager()
                  .makeBitvector(declaration.getIndices().get(0), (IntegerFormula) args.get(0));
        }
        case BV_EXTRACT -> {
          checkArgument(declaration.getIndices().size() == 2);
          yield (T)
              getBitvectorFormulaManager()
                  .extract(
                      (BitvectorFormula) args.get(0),
                      declaration.getIndices().get(0),
                      declaration.getIndices().get(1));
        }
        case BV_CONCAT -> {
          checkArgument(!args.isEmpty(), "Expected at least one argument");
          var concat = (T) args.get(0);
          for (var p = 1; p < args.size(); p++) {
            concat =
                (T)
                    getBitvectorFormulaManager()
                        .concat((BitvectorFormula) concat, (BitvectorFormula) args.get(p));
          }
          yield concat;
        }
        case BV_SIGN_EXTENSION -> {
          checkArgument(declaration.getIndices().size() == 1);
          yield (T)
              getBitvectorFormulaManager()
                  .extend((BitvectorFormula) args.get(0), declaration.getIndices().get(0), true);
        }
        case BV_ZERO_EXTENSION -> {
          checkArgument(declaration.getIndices().size() == 1);
          yield (T)
              getBitvectorFormulaManager()
                  .extend((BitvectorFormula) args.get(0), declaration.getIndices().get(0), false);
        }
        case BV_NOT -> (T) getBitvectorFormulaManager().not((BitvectorFormula) args.get(0));
        case BV_NEG -> (T) getBitvectorFormulaManager().negate((BitvectorFormula) args.get(0));
        case BV_OR -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getBitvectorFormulaManager()
                  .or((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        }
        case BV_AND -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getBitvectorFormulaManager()
                  .and((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        }
        case BV_XOR -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getBitvectorFormulaManager()
                  .xor((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        }
        case BV_SUB -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getBitvectorFormulaManager()
                  .subtract((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        }
        case BV_ADD -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getBitvectorFormulaManager()
                  .add((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        }
        case BV_SDIV ->
            (T)
                getBitvectorFormulaManager()
                    .divide((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_UDIV ->
            (T)
                getBitvectorFormulaManager()
                    .divide((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SREM ->
            (T)
                getBitvectorFormulaManager()
                    .remainder(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_UREM ->
            (T)
                getBitvectorFormulaManager()
                    .remainder(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SMOD ->
            (T)
                getBitvectorFormulaManager()
                    .smodulo((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_MUL -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getBitvectorFormulaManager()
                  .multiply((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        }
        case BV_ULT ->
            (T)
                getBitvectorFormulaManager()
                    .lessThan(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SLT ->
            (T)
                getBitvectorFormulaManager()
                    .lessThan((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_ULE ->
            (T)
                getBitvectorFormulaManager()
                    .lessOrEquals(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SLE ->
            (T)
                getBitvectorFormulaManager()
                    .lessOrEquals(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_UGT ->
            (T)
                getBitvectorFormulaManager()
                    .greaterThan(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SGT ->
            (T)
                getBitvectorFormulaManager()
                    .greaterThan(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_UGE ->
            (T)
                getBitvectorFormulaManager()
                    .greaterOrEquals(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_SGE ->
            (T)
                getBitvectorFormulaManager()
                    .greaterOrEquals(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_EQ -> { // FIXME Why is this a separate symbol?
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getBitvectorFormulaManager()
                  .equal((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        }
        case BV_SHL ->
            (T)
                getBitvectorFormulaManager()
                    .shiftLeft((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_LSHR ->
            (T)
                getBitvectorFormulaManager()
                    .shiftRight(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), false);
        case BV_ASHR ->
            (T)
                getBitvectorFormulaManager()
                    .shiftRight(
                        (BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1), true);
        case BV_ROTATE_LEFT ->
            (T)
                getBitvectorFormulaManager()
                    .rotateLeft((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_ROTATE_RIGHT ->
            (T)
                getBitvectorFormulaManager()
                    .rotateRight((BitvectorFormula) args.get(0), (BitvectorFormula) args.get(1));
        case BV_ROTATE_LEFT_BY_INT -> {
          checkArgument(declaration.getIndices().size() == 1);
          yield (T)
              getBitvectorFormulaManager()
                  .rotateLeft((BitvectorFormula) args.get(0), declaration.getIndices().get(0));
        }
        case BV_ROTATE_RIGHT_BY_INT -> {
          checkArgument(declaration.getIndices().size() == 1);
          yield (T)
              getBitvectorFormulaManager()
                  .rotateRight((BitvectorFormula) args.get(0), declaration.getIndices().get(0));
        }
        case BV_UCASTTO_FP ->
            (T)
                getFloatingPointFormulaManager()
                    .castFrom(args.get(0), false, (FloatingPointType) declaration.getType());
        case BV_SCASTTO_FP ->
            (T)
                getFloatingPointFormulaManager()
                    .castFrom(args.get(0), true, (FloatingPointType) declaration.getType());
        case UBV_TO_INT ->
            (T)
                getBitvectorFormulaManager()
                    .toIntegerFormula((BitvectorFormula) args.get(0), false);
        case SBV_TO_INT ->
            (T) getBitvectorFormulaManager().toIntegerFormula((BitvectorFormula) args.get(0), true);
        case FP_NEG ->
            (T) getFloatingPointFormulaManager().negate((FloatingPointFormula) args.get(0));
        case FP_ABS -> (T) getFloatingPointFormulaManager().abs((FloatingPointFormula) args.get(0));
        case FP_MAX ->
            (T)
                getFloatingPointFormulaManager()
                    .max((FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_MIN ->
            (T)
                getFloatingPointFormulaManager()
                    .min((FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_SQRT ->
            (T)
                getFloatingPointFormulaManager()
                    .sqrt(
                        (FloatingPointFormula) args.get(1),
                        getFloatingPointFormulaManager()
                            .fromRoundingModeFormula(
                                (FloatingPointRoundingModeFormula) args.get(0)));
        case FP_SUB ->
            (T)
                getFloatingPointFormulaManager()
                    .subtract(
                        (FloatingPointFormula) args.get(1),
                        (FloatingPointFormula) args.get(2),
                        getFloatingPointFormulaManager()
                            .fromRoundingModeFormula(
                                (FloatingPointRoundingModeFormula) args.get(0)));
        case FP_ADD ->
            (T)
                getFloatingPointFormulaManager()
                    .add(
                        (FloatingPointFormula) args.get(1),
                        (FloatingPointFormula) args.get(2),
                        getFloatingPointFormulaManager()
                            .fromRoundingModeFormula(
                                (FloatingPointRoundingModeFormula) args.get(0)));
        case FP_DIV ->
            (T)
                getFloatingPointFormulaManager()
                    .divide(
                        (FloatingPointFormula) args.get(1),
                        (FloatingPointFormula) args.get(2),
                        getFloatingPointFormulaManager()
                            .fromRoundingModeFormula(
                                (FloatingPointRoundingModeFormula) args.get(0)));
        case FP_REM ->
            (T)
                getFloatingPointFormulaManager()
                    .remainder(
                        (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_MUL ->
            (T)
                getFloatingPointFormulaManager()
                    .multiply(
                        (FloatingPointFormula) args.get(1),
                        (FloatingPointFormula) args.get(2),
                        getFloatingPointFormulaManager()
                            .fromRoundingModeFormula(
                                (FloatingPointRoundingModeFormula) args.get(0)));
        case FP_LT ->
            (T)
                getFloatingPointFormulaManager()
                    .lessThan(
                        (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_LE ->
            (T)
                getFloatingPointFormulaManager()
                    .lessOrEquals(
                        (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_GE ->
            (T)
                getFloatingPointFormulaManager()
                    .greaterOrEquals(
                        (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_GT ->
            (T)
                getFloatingPointFormulaManager()
                    .greaterThan(
                        (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_EQ ->
            (T)
                getFloatingPointFormulaManager()
                    .equalWithFPSemantics(
                        (FloatingPointFormula) args.get(0), (FloatingPointFormula) args.get(1));
        case FP_ROUND_TO_INTEGRAL ->
            (T)
                getFloatingPointFormulaManager()
                    .round(
                        (FloatingPointFormula) args.get(1),
                        getFloatingPointFormulaManager()
                            .fromRoundingModeFormula(
                                (FloatingPointRoundingModeFormula) args.get(0)));
        case FP_IS_NAN ->
            (T) getFloatingPointFormulaManager().isNaN((FloatingPointFormula) args.get(0));
        case FP_IS_INF ->
            (T) getFloatingPointFormulaManager().isInfinity((FloatingPointFormula) args.get(0));
        case FP_IS_ZERO ->
            (T) getFloatingPointFormulaManager().isZero((FloatingPointFormula) args.get(0));
        case FP_IS_NEGATIVE ->
            (T) getFloatingPointFormulaManager().isNegative((FloatingPointFormula) args.get(0));
        case FP_IS_SUBNORMAL ->
            (T) getFloatingPointFormulaManager().isSubnormal((FloatingPointFormula) args.get(0));
        case FP_IS_NORMAL ->
            (T) getFloatingPointFormulaManager().isNormal((FloatingPointFormula) args.get(0));
        case FP_CASTTO_FP ->
            getFloatingPointFormulaManager()
                .castTo((FloatingPointFormula) args.get(0), true, declaration.getType());
        case FP_CASTTO_SBV ->
            getFloatingPointFormulaManager()
                .castTo((FloatingPointFormula) args.get(0), true, declaration.getType());
        case FP_CASTTO_UBV ->
            getFloatingPointFormulaManager()
                .castTo((FloatingPointFormula) args.get(0), false, declaration.getType());
        case FP_AS_IEEEBV ->
            (T)
                getFloatingPointFormulaManager()
                    .toIeeeBitvector((FloatingPointFormula) args.get(0));
        case FP_FROM_IEEEBV ->
            (T)
                getFloatingPointFormulaManager()
                    .fromIeeeBitvector(
                        (BitvectorFormula) args.get(0), (FloatingPointType) declaration.getType());
        case STR_CONCAT -> {
          Preconditions.checkArgument(args.size() >= 2);
          yield (T) getStringFormulaManager().concat((List<StringFormula>) args);
        }
        case STR_PREFIX -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager()
                  .prefix((StringFormula) args.get(0), (StringFormula) args.get(1));
        }
        case STR_SUFFIX -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager()
                  .suffix((StringFormula) args.get(0), (StringFormula) args.get(1));
        }
        case STR_CONTAINS -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager()
                  .contains((StringFormula) args.get(0), (StringFormula) args.get(1));
        }
        case STR_SUBSTRING -> {
          Preconditions.checkArgument(args.size() == 3);
          yield (T)
              getStringFormulaManager()
                  .substring(
                      (StringFormula) args.get(0),
                      (IntegerFormula) args.get(1),
                      (IntegerFormula) args.get(2));
        }
        case STR_REPLACE -> {
          Preconditions.checkArgument(args.size() == 3);
          yield (T)
              getStringFormulaManager()
                  .replace(
                      (StringFormula) args.get(0),
                      (StringFormula) args.get(1),
                      (StringFormula) args.get(2));
        }
        case STR_REPLACE_ALL -> {
          Preconditions.checkArgument(args.size() == 3);
          yield (T)
              getStringFormulaManager()
                  .replaceAll(
                      (StringFormula) args.get(0),
                      (StringFormula) args.get(1),
                      (StringFormula) args.get(2));
        }
        case STR_CHAR_AT -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager()
                  .charAt((StringFormula) args.get(0), (IntegerFormula) args.get(1));
        }
        case STR_LENGTH -> {
          Preconditions.checkArgument(args.size() == 1);
          yield (T) getStringFormulaManager().length((StringFormula) args.get(0));
        }
        case STR_INDEX_OF -> {
          Preconditions.checkArgument(args.size() == 3);
          yield (T)
              getStringFormulaManager()
                  .indexOf(
                      (StringFormula) args.get(0),
                      (StringFormula) args.get(1),
                      (IntegerFormula) args.get(2));
        }
        case STR_TO_RE -> {
          // String to RE injection
          // We only support this for constant Strings
          Preconditions.checkArgument(args.size() == 1);
          String str =
              delegate.visit(
                  args.get(0),
                  new DefaultFormulaVisitor<>() {
                    @Override
                    protected String visitDefault(Formula f) {
                      throw new IllegalArgumentException(
                          "We only support constant Strings for str.to_re");
                    }

                    @Override
                    public String visitConstant(Formula f, Object value) {
                      return (String) value;
                    }
                  });
          yield (T) getStringFormulaManager().makeRegex(str);
        }
        case STR_IN_RE -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager().in((StringFormula) args.get(0), (RegexFormula) args.get(1));
        }
        case STR_TO_INT -> {
          Preconditions.checkArgument(args.size() == 1);
          yield (T) getStringFormulaManager().toIntegerFormula((StringFormula) args.get(0));
        }
        case INT_TO_STR -> {
          Preconditions.checkArgument(args.size() == 1);
          yield (T) getStringFormulaManager().toStringFormula((IntegerFormula) args.get(0));
        }
        case STR_FROM_CODE -> {
          Preconditions.checkArgument(args.size() == 1);
          yield (T) getStringFormulaManager().fromCodePoint((IntegerFormula) args.get(0));
        }
        case STR_TO_CODE -> {
          Preconditions.checkArgument(args.size() == 1);
          yield (T) getStringFormulaManager().toCodePoint((StringFormula) args.get(0));
        }
        case STR_LT -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager()
                  .lessThan((StringFormula) args.get(0), (StringFormula) args.get(1));
        }
        case STR_LE -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager()
                  .lessOrEquals((StringFormula) args.get(0), (StringFormula) args.get(1));
        }
        case RE_NONE -> {
          Preconditions.checkArgument(args.isEmpty());
          yield (T) getStringFormulaManager().none();
        }
        case RE_PLUS -> {
          Preconditions.checkArgument(args.size() == 1);
          yield (T) getStringFormulaManager().cross((RegexFormula) args.get(0));
        }
        case RE_STAR -> {
          Preconditions.checkArgument(args.size() == 1);
          yield (T) getStringFormulaManager().closure((RegexFormula) args.get(0));
        }
        case RE_OPTIONAL -> {
          Preconditions.checkArgument(args.size() == 1);
          yield (T) getStringFormulaManager().optional((RegexFormula) args.get(0));
        }
        case RE_CONCAT -> {
          Preconditions.checkArgument(args.size() >= 2);
          yield (T) getStringFormulaManager().concatRegex((List<RegexFormula>) args);
        }
        case RE_UNION -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager()
                  .union((RegexFormula) args.get(0), (RegexFormula) args.get(1));
        }
        case RE_RANGE -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager()
                  .range((StringFormula) args.get(0), (StringFormula) args.get(1));
        }
        case RE_INTERSECT -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager()
                  .intersection((RegexFormula) args.get(0), (RegexFormula) args.get(1));
        }
        case RE_COMPLEMENT -> {
          Preconditions.checkArgument(args.size() == 1);
          yield (T) getStringFormulaManager().complement((RegexFormula) args.get(0));
        }
        case RE_DIFFERENCE -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getStringFormulaManager()
                  .difference((RegexFormula) args.get(0), (RegexFormula) args.get(1));
        }
        case SEP_EMP -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getSLFormulaManager()
                  .makeEmptyHeap(
                      (FormulaType<? extends Formula>) args.get(0),
                      (FormulaType<? extends Formula>) args.get(1));
        }
        case SEP_NIL -> {
          Preconditions.checkArgument(args.size() == 1);
          yield (T)
              getSLFormulaManager().makeNilElement((FormulaType<? extends Formula>) args.get(0));
        }
        case SEP_PTO -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getSLFormulaManager().makePointsTo((Formula) args.get(0), (Formula) args.get(1));
        }
        case SEP_STAR -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getSLFormulaManager()
                  .makeStar((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
        }
        case SEP_WAND -> {
          Preconditions.checkArgument(args.size() == 2);
          yield (T)
              getSLFormulaManager()
                  .makeMagicWand((BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
        }
        // TODO
        // case OTHER:
        default ->
            throw new UnsupportedOperationException(
                "Operation not supported: %s, (%s)"
                    .formatted(declaration.getKind(), declaration.getName()));
      };
    }
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, Formula... args) {
    return makeApplication(declaration, ImmutableList.copyOf(args));
  }

  @Override
  public BooleanFormula makeEqual(Iterable<Formula> pArgs) {
    return rebuild(
        logger.logDef(
            "mgr",
            "makeEqual(%s)".formatted(logger.toVariables(pArgs)),
            () -> delegate.makeEqual(pArgs)));
  }

  @Override
  public BooleanFormula makeDistinct(Iterable<Formula> pArgs) {
    return rebuild(
        logger.logDef(
            "mgr",
            "makeDistinct(%s)".formatted(logger.toVariables(pArgs)),
            () -> delegate.makeDistinct(pArgs)));
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    return logger.logDefDiscard(
        "mgr",
        "getFormulaType(%s)".formatted(logger.toVariable(formula)),
        () -> delegate.getFormulaType(formula));
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    return rebuild(
        logger.logDefDiscard(
            "mgr", "parse(%s)".formatted(logger.printString(s)), () -> delegate.parse(s)));
  }

  @Override
  public List<BooleanFormula> parseAll(String s) throws IllegalArgumentException {
    return rebuildAll(
        logger.logDefDiscard(
            "mgr", "parseAll(%s)".formatted(logger.printString(s)), () -> delegate.parseAll(s)));
  }

  @Override
  public Appender dumpFormula(BooleanFormula pT) {
    return logger.logDefDiscard(
        "mgr", "dumpFormula(%s)".formatted(logger.toVariable(pT)), () -> delegate.dumpFormula(pT));
  }

  @Override
  public BooleanFormula applyTactic(BooleanFormula input, Tactic tactic)
      throws InterruptedException, SolverException {
    return rebuild(
        logger.logDefDiscard(
            "mgr",
            "applyTactic(%s, %s)".formatted(logger.toVariable(input), "Tactic." + tactic.name()),
            () -> delegate.applyTactic(input, tactic)));
  }

  @Override
  public <T extends Formula> T simplify(T input) throws InterruptedException {
    return rebuild(
        logger.logDefDiscard(
            "mgr",
            "simplify(%s)".formatted(logger.toVariable(input)),
            () -> delegate.simplify(input)));
  }

  @Override
  public <R> R visit(Formula f, FormulaVisitor<R> rFormulaVisitor) {
    return logger.logDefDiscard(
        "mgr",
        String.format(
            "visit(%s, new DefaultFormulaVisitor<>() {"
                + "  protected Formula visitDefault(Formula f) {"
                + "  return f;"
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
                + "  protected TraversalProcess visitDefault(Formula f) {"
                + "  return TraversalProcess.CONTINUE;"
                + "}})",
            logger.toVariable(f)),
        () -> delegate.visitRecursively(f, rFormulaVisitor));
  }

  @Override
  public <T extends Formula> T transformRecursively(
      T f, FormulaTransformationVisitor pFormulaVisitor) {
    return logger.logDefDiscard(
        "mgr",
        "transformRecursively(%s, new FormulaTransformationVisitor(%s) {})"
            .formatted(logger.toVariable(f), "mgr"),
        () -> delegate.transformRecursively(f, pFormulaVisitor));
  }

  @Override
  public ImmutableMap<String, Formula> extractVariables(Formula f) {
    return logger.logDefDiscard(
        "mgr",
        "extractVariables(%s)".formatted(logger.toVariable(f)),
        () -> delegate.extractVariables(f));
  }

  @Override
  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f) {
    return logger.logDefDiscard(
        "mgr",
        "extractVariablesAndUFs(%s)".formatted(logger.toVariable(f)),
        () -> delegate.extractVariablesAndUFs(f));
  }

  @Override
  public <T extends Formula> T substitute(
      T f, Map<? extends Formula, ? extends Formula> fromToMapping) {
    return rebuild(
        logger.logDefDiscard(
            "mgr",
            "substitute(%s, ImmutableMap.ofEntries(%s))"
                .formatted(
                    logger.toVariable(f),
                    FluentIterable.from(fromToMapping.entrySet())
                        .transform(
                            entry ->
                                "Map.entry(%s, %s)"
                                    .formatted(
                                        logger.toVariable(entry.getKey()),
                                        logger.toVariable(entry.getValue())))
                        .join(Joiner.on(", "))),
            () -> delegate.substitute(f, fromToMapping)));
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    return rebuild(delegate.translateFrom(formula, otherManager));
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
