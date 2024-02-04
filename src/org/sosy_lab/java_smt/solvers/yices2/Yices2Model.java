// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_BOOL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_BV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_FUNCTION;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_MAPPING;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_RATIONAL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_SCALAR;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_TUPLE;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_UNKNOWN;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_application;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvtype_size;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_def_terms;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_eq;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_false;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_model;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_value_as_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_model_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_bvbin;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_float;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_rational;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_true;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_children;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_is_arithmetic;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_is_bitvector;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_is_bool;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_is_int;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_of_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_bitsize;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_expand_function;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_expand_mapping;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_function_arity;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_get_bool;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_get_bv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_get_mpq;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.base.Strings;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.primitives.Ints;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

public class Yices2Model extends AbstractModel<Integer, Integer, Long> {

  private final long model;
  private final Yices2TheoremProver prover;
  private final Yices2FormulaCreator formulaCreator;

  protected Yices2Model(long model, Yices2TheoremProver prover, Yices2FormulaCreator pCreator) {
    super(prover, pCreator);
    this.model = model;
    this.prover = prover;
    this.formulaCreator = Preconditions.checkNotNull(pCreator);
  }

  @Override
  public void close() {
    if (!isClosed()) {
      yices_free_model(model);
    }
    super.close();
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    Preconditions.checkState(!isClosed());
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    List<Integer> complex =
        ImmutableList.of(YVAL_SCALAR, YVAL_FUNCTION, YVAL_MAPPING, YVAL_UNKNOWN, YVAL_TUPLE);
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    int[] termsInModel = yices_def_terms(model);
    for (int term : termsInModel) {
      int[] yvalTag = yices_get_value(model, term);
      if (!complex.contains(yvalTag[1])) { // TODO Switch with other if for less complex check?
        assignments.add(getSimpleAssignment(term));
      } else if (yvalTag[1] == YVAL_FUNCTION) {
        assignments.addAll(getFunctionAssignment(term, yvalTag));
      } else {
        throw new UnsupportedOperationException("YVAL with unexpected tag: " + yvalTag[1]);
      }
    }

    return assignments.build();
  }

  private ImmutableList<ValueAssignment> getFunctionAssignment(int t, int[] yval) {
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    int arity = yices_val_function_arity(model, yval[0], yval[1]);
    int[] types = yices_type_children(yices_type_of_term(t));
    int[] argTerms = new int[arity];
    String name = yices_get_term_name(t);
    int[] expandFun = yices_val_expand_function(model, yval[0], yval[1]);
    for (int i = 2; i < expandFun.length - 1; i += 2) {
      int[] expandMap;
      if (expandFun[i + 1] == YVAL_MAPPING) {
        expandMap = yices_val_expand_mapping(model, expandFun[i], arity, expandFun[i + 1]);
      } else {
        throw new IllegalArgumentException("Unexpected YVAL tag " + yval[1]);
      }
      List<Object> argumentInterpretation = new ArrayList<>();
      for (int j = 0; j < expandMap.length - 2; j += 2) {
        Object argValue = valueFromYval(expandMap[j], expandMap[j + 1], types[j / 2]);
        argumentInterpretation.add(argValue);
        argTerms[j / 2] = valueAsTerm(types[j / 2], argValue);
      }
      Object funValue =
          valueFromYval(
              expandMap[expandMap.length - 2],
              expandMap[expandMap.length - 1],
              types[types.length - 1]);
      int valueTerm = valueAsTerm(types[types.length - 1], funValue);
      int funApp = yices_application(t, arity, argTerms);
      assignments.add(
          new ValueAssignment(
              creator.encapsulateWithTypeOf(funApp),
              creator.encapsulateWithTypeOf(valueTerm),
              creator.encapsulateBoolean(yices_eq(funApp, valueTerm)),
              name,
              funValue,
              argumentInterpretation));
    }
    return assignments.build();
  }

  private ValueAssignment getSimpleAssignment(int t) {
    List<Object> argumentInterpretation = new ArrayList<>();
    int valueTerm = yices_get_value_as_term(model, t);
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(t),
        creator.encapsulateWithTypeOf(valueTerm),
        creator.encapsulateBoolean(yices_eq(t, valueTerm)),
        yices_get_term_name(t),
        formulaCreator.convertValue(t, valueTerm),
        argumentInterpretation);
  }

  private Object valueFromYval(int id, int tag, int type) {
    if (tag == YVAL_BOOL) {
      return yices_val_get_bool(model, id, tag);
    } else if (tag == YVAL_RATIONAL) {
      String value = yices_val_get_mpq(model, id, tag);
      if (yices_type_is_int(type) && !value.contains("/")) {
        return new BigInteger(value);
      } else {
        return Rational.of(value);
      }
    } else if (tag == YVAL_BV) {
      int size = yices_val_bitsize(model, id, tag);
      int[] littleEndianBV = yices_val_get_bv(model, id, size, tag);
      Preconditions.checkArgument(littleEndianBV.length != 0, "BV was empty");
      String bigEndianBV = Joiner.on("").join(Lists.reverse(Ints.asList(littleEndianBV)));
      return new BigInteger(bigEndianBV, 2);
    } else {
      throw new IllegalArgumentException("Unexpected YVAL tag: " + tag);
    }
  }

  private int valueAsTerm(int type, Object value) {
    if (yices_type_is_bool(type)) {
      if ((boolean) value) {
        return yices_true();
      } else {
        return yices_false();
      }
    } else if (yices_type_is_arithmetic(type)) {
      String val = value.toString();
      if (val.contains("/")) {
        return yices_parse_rational(val);
      } else {
        return yices_parse_float(val);
      }
    } else if (yices_type_is_bitvector(type)) {
      BigInteger val = (BigInteger) value;
      int bvSize = yices_bvtype_size(type);
      String bits = val.toString(2);
      assert bits.length() <= bvSize
          : "numeral value " + val + " is out of range for size " + bvSize;
      if (bits.length() < bvSize) {
        bits = Strings.padStart(bits, bvSize, '0');
      }
      Preconditions.checkArgument(bits.length() == bvSize, "Bitvector has unexpected size.");
      return yices_parse_bvbin(bits);
    } else {
      throw new IllegalArgumentException("Unexpected type: " + yices_type_to_string(type));
    }
  }

  @Override
  protected @Nullable Integer evalImpl(Integer pFormula) {
    // TODO Can UF appear here?? // Built in Functions like "add" seem to be OK
    Preconditions.checkState(!isClosed());
    // TODO REENABLE after testing
    // Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    int val = yices_get_value_as_term(model, pFormula);
    if (val == -1) {
      throw new IllegalArgumentException(
          "Could not evaluate Term: " + yices_term_to_string(pFormula));
    }
    return val;
  }

  @Override
  public String toString() {
    return yices_model_to_string(model);
  }
}
