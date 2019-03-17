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
package org.sosy_lab.java_smt.solvers.princess;

import static scala.collection.JavaConversions.asJavaIterable;
import static scala.collection.JavaConversions.seqAsJavaList;

import ap.SimpleAPI.PartialModel;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.types.Sort;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import scala.Option;
import scala.Tuple2;

class PrincessModel extends CachingAbstractModel<IExpression, Sort, PrincessEnvironment> {
  private static final long serialVersionUID = 1L;
  private final PartialModel model;

  PrincessModel(
      PartialModel partialModel,
      FormulaCreator<IExpression, Sort, PrincessEnvironment, ?> creator) {
    super(creator);
    this.model = partialModel;
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    scala.collection.Map<IExpression, IExpression> interpretation = model.interpretation();

    // first get the addresses of arrays
    Map<IIntLit, ITerm> arrays = getArrayAddresses(interpretation);

    // then iterate over the model and generate the assignments
    ImmutableSet.Builder<ValueAssignment> assignments = ImmutableSet.builder();
    for (Tuple2<IExpression, IExpression> entry : asJavaIterable(interpretation)) {
      ValueAssignment assignment = getAssignment(entry._1, entry._2, arrays);
      if (assignment != null) {
        assignments.add(assignment);
      }
    }

    return assignments.build().asList();
  }

  /**
   * Collect array-models, we need them to replace identifiers later. Princess models arrays as
   * plain numeric "memory-addresses", and the model for an array-access at one of the addresses is
   * the array-content. Example: "arr[5]=123" is modeled as "{arr=0, select(0,5)=123}" or "{arr=0,
   * store(0,5,123)=0}", where "0" is the memory-address. The returned mapping contains the mapping
   * of "0" (=address) to "arr" (=identifier).
   */
  private Map<IIntLit, ITerm> getArrayAddresses(
      scala.collection.Map<IExpression, IExpression> interpretation) {
    Map<IIntLit, ITerm> arrays = new HashMap<>();
    for (Tuple2<IExpression, IExpression> entry : asJavaIterable(interpretation)) {
      if (entry._1 instanceof IConstant) {
        ITerm maybeArray = (IConstant) entry._1;
        if (creator.getEnv().hasArrayType(maybeArray) && entry._2 instanceof IIntLit) {
          arrays.put((IIntLit) entry._2, maybeArray);
        }
      }
    }
    return arrays;
  }

  private @Nullable ValueAssignment getAssignment(
      IExpression key, IExpression value, Map<IIntLit, ITerm> pArrays) {
    IExpression fValue = value;
    final IExpression fKey;
    final String name;
    final IFormula fAssignment;
    Collection<Object> argumentInterpretations = Collections.emptyList();

    if (key instanceof IAtom) {
      fKey = key;
      name = key.toString();
      fAssignment = new IBinFormula(IBinJunctor.Eqv(), (IAtom) key, (IFormula) fValue);

    } else if (key instanceof IConstant) {
      if (creator.getEnv().hasArrayType(key)) {
        // array-access, for explanation see #getArrayAddresses
        return null;
      } else {
        fKey = key;
        name = key.toString();
        fAssignment = ((IConstant) key).$eq$eq$eq((ITerm) fValue);
      }

    } else if (key instanceof IFunApp) {
      IFunApp cKey = (IFunApp) key;

      switch (cKey.fun().name()) {
        case "select":
          // array-access, for explanation see #getArrayAddresses
          ITerm arrayId = cKey.args().apply(0);
          ITerm arrayIndex = cKey.args().apply(1);
          ITerm arrayF = pArrays.get(arrayId);
          if (arrayF == null) {
            // intermediate array store, like a tmp-variable, happens for repeated
            // store-operations
            return null;
          }
          fKey = creator.getEnv().makeSelect(arrayF, arrayIndex);
          name = arrayF.toString();
          argumentInterpretations = Collections.singleton(creator.convertValue(arrayIndex));
          break;
        case "store":
          // array-access, for explanation see #getArrayAddresses
          // IdealInt sourceArray = cKey.args().apply(0);
          ITerm arrayId2 = (ITerm) value;
          ITerm arrayIndex2 = cKey.args().apply(1);
          ITerm arrayContent = cKey.args().apply(2);
          ITerm arrayF2 = pArrays.get(arrayId2);
          if (arrayF2 == null) {
            // intermediate array store, like a tmp-variable, happens for repeated
            // store-operations
            return null;
          }
          fKey = creator.getEnv().makeSelect(arrayF2, arrayIndex2);
          fValue = arrayContent;
          name = arrayF2.toString();
          argumentInterpretations = Collections.singleton(creator.convertValue(arrayIndex2));
          break;
        default:
          // normal variable or UF
          argumentInterpretations = new ArrayList<>();
          for (ITerm arg : seqAsJavaList(cKey.args())) {
            argumentInterpretations.add(creator.convertValue(arg));
          }
          fKey = cKey;
          name = cKey.fun().name();
      }

      fAssignment = ((ITerm) fKey).$eq$eq$eq((ITerm) fValue);

    } else {
      throw new AssertionError(
          String.format("unknown type of key: %s -> %s (%s)", key, value, key.getClass()));
    }

    return new ValueAssignment(
        creator.encapsulateWithTypeOf(fKey),
        creator.encapsulateWithTypeOf(fValue),
        creator.encapsulateBoolean(fAssignment),
        name,
        creator.convertValue(fValue),
        argumentInterpretations);
  }

  @Override
  public String toString() {
    return model.toString();
  }

  @Override
  public void close() {}

  @Override
  protected IExpression evalImpl(IExpression formula) {
    if (formula instanceof ITerm) {
      Option<ITerm> out = model.evalToTerm((ITerm) formula);
      return out.isEmpty() ? null : out.get();
    } else if (formula instanceof IFormula) {
      Option<IExpression> out = model.evalExpression(formula);
      return out.isEmpty() ? null : out.get();
    } else {
      throw new AssertionError("unexpected formula: " + formula);
    }
  }
}
