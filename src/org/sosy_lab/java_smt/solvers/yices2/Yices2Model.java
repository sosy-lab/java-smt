// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import com.google.common.base.Preconditions;
import com.google.common.base.Verify;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.sri.yices.Model;
import com.sri.yices.Terms;
import com.sri.yices.Types;
import com.sri.yices.VectorValue;
import com.sri.yices.YVal;
import com.sri.yices.YicesException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

class Yices2Model extends AbstractModel<Integer, Integer, Long> {

  private final Model model;
  private final Yices2FormulaCreator formulaCreator;

  Yices2Model(Model model, Yices2AbstractProver<?> prover, Yices2FormulaCreator pCreator) {
    super(prover, pCreator);
    this.model = model;
    this.formulaCreator = Preconditions.checkNotNull(pCreator);
  }

  @Override
  public void close() {
    if (!isClosed()) {
      model.close();
    }
    super.close();
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    Preconditions.checkState(!isProverClosed(), "cannot use model after prover is closed");
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    int[] termsInModel = model.collectDefinedTerms();
    for (int term : termsInModel) {
      YVal yval = model.getValue(term);
      switch (yval.tag) {
        case BOOL, RATIONAL, ALGEBRAIC, BV -> assignments.add(getSimpleAssignment(term));
        case FUNCTION -> { // UFs and Arrays
          if (formulaCreator.isArrayVariable(term)) {
            assignments.addAll(getArrayAssignment(term, yval));
          } else {
            assignments.addAll(getFunctionAssignment(term, yval));
          }
        }
        default -> throw new UnsupportedOperationException("YVAL with unexpected tag: " + yval.tag);
      }
    }

    return assignments.build();
  }

  private ImmutableList<ValueAssignment> getFunctionAssignment(int f, YVal value) {
    int[] types = Types.children(Terms.typeOf(f));
    VectorValue expandFun = model.expandFunction(value);

    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    for (var map : expandFun.vector) {
      var x = model.expandMapping(map);

      ImmutableList.Builder<Object> builderValues = ImmutableList.builder();
      ImmutableList.Builder<Integer> builderTerms = ImmutableList.builder();

      for (int p = 0; p < x.vector.length; p++) {
        var v = x.vector[p];
        var t = types[p];

        var argValue = toValue(v, t);
        var argTerm = constantValue(argValue, t);

        builderValues.add(argValue);
        builderTerms.add(argTerm);
      }

      var funValue = toValue(x.value, types[types.length - 1]);
      var funTerm = constantValue(funValue, types[types.length - 1]);

      var app = Terms.funApplication(f, builderTerms.build());

      assignments.add(
          new ValueAssignment(
              creator.encapsulateWithTypeOf(app),
              creator.encapsulateWithTypeOf(funTerm),
              creator.encapsulateBoolean(Terms.eq(app, funTerm)),
              Terms.getName(f),
              funValue,
              builderValues.build()));
    }
    return assignments.build();
  }

  private List<ValueAssignment> getArrayAssignment0(
      int f, Iterable<Integer> arguments, Iterable<Object> values, int type, YVal value) {
    if (Types.isFunction(type)) {
      var signature = Types.children(type);
      Verify.verify(signature.length == 2);
      var leftType = signature[0];
      var rightType = signature[1];

      ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
      for (var map : model.expandFunction(value).vector) {
        var app = model.expandMapping(map);
        Verify.verify(app.vector.length == 1);

        // Build term for the current index
        var leftValue = toValue(app.vector[0], leftType);
        var leftTerm = constantValue(leftValue, leftType);

        // Add it to the argument list
        var newArguments = FluentIterable.concat(arguments, ImmutableList.of(leftTerm));
        var newValue = FluentIterable.concat(values, ImmutableList.of(leftValue));

        assignments.addAll(getArrayAssignment0(f, newArguments, newValue, rightType, app.value));
      }
      return assignments.build();

    } else {
      // Build term for the left side of the assignment
      var app = f;
      for (var arg : arguments) {
        app = Terms.funApplication(app, arg);
      }

      // Build term for the value
      var rightValue = toValue(value, type);
      var rightTerm = constantValue(rightValue, type);

      return ImmutableList.of(
          new ValueAssignment(
              creator.encapsulateWithTypeOf(app),
              creator.encapsulateWithTypeOf(rightTerm),
              creator.encapsulateBoolean(Terms.eq(app, rightTerm)),
              Terms.getName(f),
              rightValue,
              ImmutableList.copyOf(values)));
    }
  }

  private List<ValueAssignment> getArrayAssignment(int f, YVal value) {
    return getArrayAssignment0(f, ImmutableList.of(), ImmutableList.of(), Terms.typeOf(f), value);
  }

  private ValueAssignment getSimpleAssignment(int t) {
    List<Object> argumentInterpretation = new ArrayList<>();
    int valueTerm = model.valueAsTerm(t);
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(t),
        creator.encapsulateWithTypeOf(valueTerm),
        creator.encapsulateBoolean(Terms.eq(t, valueTerm)),
        Terms.getName(t),
        formulaCreator.convertValue(t, valueTerm),
        argumentInterpretation);
  }

  /** Convert a Yices value to a Java value. */
  private Object toValue(YVal value, int type) {
    return switch (value.tag) {
      case BOOL -> model.boolValue(value);
      case RATIONAL -> {
        if (Types.isInt(type)) {
          yield model.bigIntegerValue(value);
        } else {
          var rational = model.bigRationalValue(value);
          yield Rational.of(rational.getNumerator(), rational.getDenominator());
        }
      }
      case BV -> Yices2FormulaCreator.bitsToInteger(model.bvValue(value));
      default -> throw new IllegalArgumentException("Unexpected value type: " + value.tag);
    };
  }

  /** Create a term for a constant value. */
  private int constantValue(Object value, int type) {
    if (Types.isBool(type)) {
      return Terms.mkBoolConst((Boolean) value);
    } else if (Types.isInt(type)) {
      return Terms.intConst((BigInteger) value);
    } else if (Types.isReal(type)) {
      var rational = (Rational) value;
      return Terms.rationalConst(rational.getNum(), rational.getDen());
    } else if (Types.isBitvector(type)) {
      return Terms.bvConst(
          Yices2FormulaCreator.integerToBits(Types.bvSize(type), (BigInteger) value));
    } else {
      throw new IllegalArgumentException("Unexpected type: " + Types.toString(type));
    }
  }

  @Override
  protected @Nullable Integer evalImpl(Integer pFormula) {
    try {
      return model.valueAsTerm(pFormula);
    } catch (YicesException e) {
      throw new IllegalArgumentException("Could not evaluate term: " + Terms.toString(pFormula));
    }
  }

  @Override
  public String toString() {
    return model.toString();
  }
}
