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

import static scala.collection.JavaConversions.asScalaBuffer;
import static scala.collection.JavaConversions.seqAsJavaList;

import ap.SimpleAPI;
import ap.SimpleAPI.ConstantLoc;
import ap.SimpleAPI.IntFunctionLoc;
import ap.SimpleAPI.IntValue;
import ap.SimpleAPI.ModelLocation;
import ap.SimpleAPI.ModelValue;
import ap.SimpleAPI.PartialModel;
import ap.SimpleAPI.PredicateLoc;
import ap.basetypes.IdealInt;
import ap.parser.IAtom;
import ap.parser.IExpression;
import ap.parser.IFunApp;
import ap.parser.ITerm;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSet.Builder;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import scala.Option;
import scala.Tuple2;
import scala.collection.Iterator;

class PrincessModel
    extends CachingAbstractModel<IExpression, PrincessTermType, PrincessEnvironment> {
  private final PartialModel model;

  PrincessModel(
      PartialModel partialModel,
      FormulaCreator<IExpression, PrincessTermType, PrincessEnvironment, ?> creator) {
    super(creator);
    this.model = partialModel;
  }

  @Nullable
  @Override
  public Object evaluateImpl(IExpression f) {
    Option<ModelValue> out = model.evalExpression(f);
    if (out.isEmpty()) {
      return null;
    }
    ModelValue value = out.get();
    return getValue(value);
  }

  @Override
  protected ImmutableList<ValueAssignment> modelToList() {
    scala.collection.Map<ModelLocation, ModelValue> interpretation = model.interpretation();

    // first get the addresses of arrays
    Map<IdealInt, ITerm> arrays = getArrayAddresses(interpretation);

    // then iterate over the model and generate the assignments
    Builder<ValueAssignment> assignments = ImmutableSet.builder();
    Iterator<Tuple2<ModelLocation, ModelValue>> it2 = interpretation.iterator();
    while (it2.hasNext()) {
      Tuple2<ModelLocation, ModelValue> entry = it2.next();
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
  private Map<IdealInt, ITerm> getArrayAddresses(
      scala.collection.Map<ModelLocation, ModelValue> interpretation) {
    Map<IdealInt, ITerm> arrays = new HashMap<>();
    Iterator<Tuple2<ModelLocation, ModelValue>> it1 = interpretation.iterator();
    while (it1.hasNext()) {
      Tuple2<ModelLocation, ModelValue> entry = it1.next();
      if (entry._1 instanceof ConstantLoc) {
        ITerm maybeArray = IExpression.i(((ConstantLoc) entry._1).c());
        if (creator.getEnv().hasArrayType(maybeArray) && entry._2 instanceof IntValue) {
          arrays.put(((IntValue) entry._2).v(), maybeArray);
        }
      }
    }
    return arrays;
  }

  private @Nullable ValueAssignment getAssignment(
      ModelLocation key, ModelValue value, Map<IdealInt, ITerm> arrays) {
    Object fValue = getValue(value);
    if (key instanceof PredicateLoc) {
      Formula fKey =
          creator.encapsulateWithTypeOf(
              new IAtom(((PredicateLoc) key).p(), asScalaBuffer(Collections.emptyList())));
      return new ValueAssignment(fKey, key.toString(), fValue, Collections.emptyList());

    } else if (key instanceof ConstantLoc) {
      ITerm term = IExpression.i(((ConstantLoc) key).c());
      if (creator.getEnv().hasArrayType(term)) {
        // array-access, for explanation see #getArrayAddresses
        return null;
      } else {
        return new ValueAssignment(
            creator.encapsulateWithTypeOf(term), key.toString(), fValue, Collections.emptyList());
      }

    } else if (key instanceof IntFunctionLoc) {
      IntFunctionLoc cKey = (IntFunctionLoc) key;

      if ("select/2".equals(cKey.f().toString())) {
        // array-access, for explanation see #getArrayAddresses
        IdealInt arrayId = cKey.args().apply(0);
        IdealInt arrayIndex = cKey.args().apply(1);
        ITerm arrayF = arrays.get(arrayId);
        Formula select =
            creator.encapsulateWithTypeOf(
                creator.getEnv().makeSelect(arrayF, IExpression.i(arrayIndex)));
        return new ValueAssignment(
            select, arrayF.toString(), fValue, Collections.singleton(arrayIndex.bigIntValue()));

      } else if ("store/3".equals(cKey.f().toString())) {
        // array-access, for explanation see #getArrayAddresses
        IdealInt arrayId = cKey.args().apply(0);

        // we expect "store(0,5,123)=0" where "0" is the arrayId
        assert arrayId.bigIntValue().equals(fValue);

        IdealInt arrayIndex = cKey.args().apply(1);
        IdealInt arrayContent = cKey.args().apply(2);
        ITerm arrayF = arrays.get(arrayId);
        Formula select =
            creator.encapsulateWithTypeOf(
                creator.getEnv().makeSelect(arrayF, IExpression.i(arrayIndex)));
        return new ValueAssignment(
            select,
            arrayF.toString(),
            arrayContent.bigIntValue(),
            Collections.singleton(arrayIndex.bigIntValue()));

      } else {
        // normal variable or UF
        List<Object> argumentInterpretation = new ArrayList<>();
        List<ITerm> argTerms = new ArrayList<>();
        for (IdealInt arg : seqAsJavaList(cKey.args())) {
          argumentInterpretation.add(arg.bigIntValue());
          argTerms.add(IExpression.i(arg));
        }
        Formula fKey =
            creator.encapsulateWithTypeOf(new IFunApp(cKey.f(), asScalaBuffer(argTerms)));
        return new ValueAssignment(fKey, cKey.f().name(), fValue, argumentInterpretation);
      }

    } else {
      throw new AssertionError(
          String.format("unknown type of key: %s -> %s (%s)", key, value, key.getClass()));
    }
  }

  @Override
  public String toString() {
    return model.toString();
  }

  private Object getValue(SimpleAPI.ModelValue value) {
    if (value instanceof SimpleAPI.BoolValue) {
      return ((SimpleAPI.BoolValue) value).v();

    } else if (value instanceof SimpleAPI.IntValue) {
      return ((SimpleAPI.IntValue) value).v().bigIntValue();

    } else {
      throw new IllegalArgumentException(
          "unhandled model value " + value + " of type " + value.getClass());
    }
  }

  @Override
  public void close() {}
}
