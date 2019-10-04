/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_BOOL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_BV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_FUNCTION;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_MAPPING;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_RATIONAL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_UNKNOWN;
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
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_expand_function;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_expand_mapping;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_function_arity;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_get_bitsize;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_get_bool;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_get_bv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_get_mpq;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;

public class Yices2Model extends CachingAbstractModel<Integer, Integer, Long> {

  private final long model;
  private final Yices2TheoremProver prover;
  private final Yices2FormulaCreator formulaCreator;
  private final boolean DEBUG_MODEL = true;
  private boolean closed = false;

  protected Yices2Model(long model, Yices2TheoremProver prover, Yices2FormulaCreator pCreator) {
    super(pCreator);
    // TODO Auto-generated constructor stub
    this.model = model;
    this.prover = prover;
    this.formulaCreator = pCreator;
    if (DEBUG_MODEL) {
      System.out.println("---MODEL_BEGIN---");
      System.out.println(yices_model_to_string(model, 100, 10, 0));
      System.out.println("---MODEL_END---");
    }
  }

  protected Yices2Model(long model, Yices2FormulaCreator creator) {
    super(creator);
    this.model = model;
    this.prover = null;
    this.formulaCreator = creator;
  }

  @Override
  public void close() {
    // TODO Auto-generated method stub
    if (!closed) {
      yices_free_model(model);
      closed = true;
    }
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    // TODO Auto-generated method stub
    Preconditions.checkState(!closed);
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    List<Integer> complex = ImmutableList.of(YVAL_FUNCTION, YVAL_MAPPING, YVAL_UNKNOWN);
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    int[] termsInModel = yices_def_terms(model);
    for (int i = 0; i < termsInModel.length; i++) {
      int[] yvalTag = yices_get_value(model, termsInModel[i]);
      if (!complex.contains(yvalTag[1])) {
        assignments.add(getSimpleAssignment(termsInModel[i]));
      } else if (yvalTag[1] == YVAL_FUNCTION) {
        assignments.addAll(getFunctionAssignment(termsInModel[i], yvalTag));
      } else {
        throw new UnsupportedOperationException("Not yet implemented");
      }
    }

    return assignments.build();
  }

  // TODO encapsulate Formula ? convert yval to valueTerm and value(Object)
  private ImmutableList<ValueAssignment> getFunctionAssignment(int t, int[] yval) {
    System.out.println("Exploring function...");
    System.out.println(yices_term_to_string(t, 300, 1, 0));
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    int arity = yices_val_function_arity(model, yval[0], yval[1]);
    int[] types = yices_type_children(yices_type_of_term(t));
    String name = yices_get_term_name(t);
    // TOOD solve inconsistent memory problems presumably occurring in expand_mapping()
    int[] expandFun = yices_val_expand_function(model, yval[0], yval[1]);
    System.out.println("Expanded Function:");
    for (int i = 0; i < expandFun.length; i++) {
      System.out.println(expandFun[i]);
    }
    /*
     * TODO Expand function returns multiple yvals with tag YVAL_UNKNOWN Expected behavior: One yval
     * of same type as fun return for the default value, YVAL_MAPPING(s) for actual arguments/value
     */
    int[] defaultValue = {expandFun[0], expandFun[1]};
    if(expandFun.length==2) { //TODO Really required?
      //valueTerm = convert( default Value)
      throw new UnsupportedOperationException("Formula has only default value");
      // assignments.add(new ValueAssignment(keyFormula, valueFormula, formula, name, value,
      // argumentInterpretation))
    }else {
      for (int i = 2; i < expandFun.length - 1; i += 2) {
        System.out.println("Yval_id: " + expandFun[i] + " Yval tag: " + expandFun[i + 1]);
        int[] expandMap;
        if (expandFun[i + 1] == YVAL_MAPPING) {
          expandMap = yices_val_expand_mapping(model, expandFun[i], arity, expandFun[i + 1]);
        } else {
          throw new IllegalArgumentException("Not a mapping!"); // TODO
        }
        List<Object> argumentInterpretation = new ArrayList<>();
       // TODO convertValue of (expandMap[0], expandMap[1])
        for (int j = 0; i<expandMap.length-3; i+=2) {
          argumentInterpretation.add(valueFromYval(expandMap[j], expandMap[j++], types[j/2] ));//TODO
        }
        Object value = valueFromYval(expandMap[expandMap.length-2],expandMap[expandMap.length-1], types[types.length-1]);
        int valueTerm = valueAsTerm(types[types.length-1], value);
        assignments.add(new ValueAssignment(creator.encapsulateWithTypeOf(t),
            creator.encapsulateWithTypeOf(valueTerm),
            creator.encapsulateBoolean(yices_eq(t, valueTerm)),
            name,
            value,
            argumentInterpretation));
      }
    }
    return assignments.build();// new ValueAssignment(keyFormula, valueFormula, formula, name,
                               // value, argumentInterpretation)
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
      return (boolean) yices_val_get_bool(model, id, tag);
    } else if (tag == YVAL_RATIONAL) {
      String value = yices_val_get_mpq(model, id, tag);
      if (yices_type_is_int(type) && !value.contains("/")) {
        return new BigInteger(value);
      } else {
        return Rational.of(value);
      }
    } else if (tag == YVAL_BV) {
      int size = yices_val_get_bitsize(model, id, tag);
      int[] littleEndianBV = yices_val_get_bv(model, id, size, tag);
      String bigEndianBV = "";
      for (int i = littleEndianBV.length - 1; i >= 0; i--) {
        bigEndianBV = bigEndianBV + littleEndianBV[i];
      }
      if (bigEndianBV != "") {
        return new BigInteger(bigEndianBV, 2);
      } else {
        throw new IllegalArgumentException("BV was empty");
      }
    } else {
      throw new IllegalArgumentException("Unexpected yval tag: " + tag);
    }
  }

  private int valueAsTerm(int type, Object value) {
    if (yices_type_is_bool(type)) {
      if ((boolean) value == true) {
        return yices_true();
      } else {
        return yices_false();
      }
    } else if (yices_type_is_arithmetic(type)) {
      String val = (String) value;
      if (val.contains("/")) {
        return yices_parse_rational(val);
      } else {
        return yices_parse_float(val);
      }
    } else if (yices_type_is_bitvector(type)) {
      BigInteger val = (BigInteger) value;
      return yices_parse_bvbin(val.toString(2));
    } else {
      throw new IllegalArgumentException(
          "Unexpected type: " + yices_type_to_string(type, 100, 1, 0));
    }
  }

  @Override
  protected @Nullable Integer evalImpl(Integer pFormula) {
    // TODO Can Functions appear here?? // Convert yval value returns to term instead of
    // get_value_as_term
    System.out
        .println("Query type is: " + yices_type_to_string(yices_type_of_term(pFormula), 100, 1, 0));
    Preconditions.checkState(!closed);
    // TODO REENABLE after testing Preconditions.checkState(!prover.isClosed(), "cannot use model
    // after prover is closed");
    int[] yval = yices_get_value(model, pFormula);
    System.out.println("Yval id is: " + yval[0]);
    System.out.println("Yval tag is: " + yval[1]);
    int val = yices_get_value_as_term(model, pFormula);
    if (val == -1) {
      throw new IllegalArgumentException("Term could not be evaluated!");
    }
    return val;
  }

}

