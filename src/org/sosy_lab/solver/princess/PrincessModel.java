/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.princess;

import static scala.collection.JavaConversions.asScalaBuffer;
import static scala.collection.JavaConversions.seqAsJavaList;

import ap.SimpleAPI;
import ap.SimpleAPI.ConstantLoc;
import ap.SimpleAPI.IntFunctionLoc;
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

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractModel.CachingAbstractModel;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import scala.Option;
import scala.Tuple2;
import scala.collection.Iterator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import javax.annotation.Nullable;

class PrincessModel
    extends CachingAbstractModel<IExpression, PrincessTermType, PrincessEnvironment> {
  private final PartialModel model;
  private final ImmutableList<IExpression> assertedTerms;

  PrincessModel(
      PartialModel partialModel,
      FormulaCreator<IExpression, PrincessTermType, PrincessEnvironment, ?> creator,
      Collection<? extends IExpression> assertedTerms) {
    super(creator);
    this.model = partialModel;
    this.assertedTerms = ImmutableList.copyOf(assertedTerms);
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

    Builder<ValueAssignment> assignments = ImmutableSet.builder();

    Iterator<Tuple2<ModelLocation, ModelValue>> it = model.interpretation().iterator();
    while (it.hasNext()) {
      Tuple2<ModelLocation, ModelValue> entry = it.next();
      assignments.add(getAssignment(entry._1, entry._2));
    }

    return assignments.build().asList();
  }

  private @Nullable ValueAssignment getAssignment(ModelLocation key, ModelValue value) {
    Object fValue = getValue(value);
    if (key instanceof PredicateLoc) {
      Formula fKey =
          creator.encapsulateWithTypeOf(
              new IAtom(((PredicateLoc) key).p(), asScalaBuffer(Collections.emptyList())));
      return new ValueAssignment(fKey, key.toString(), fValue, Collections.emptyList());

    } else if (key instanceof ConstantLoc) {
      Formula fKey = creator.encapsulateWithTypeOf(IExpression.i(((ConstantLoc) key).c()));
      return new ValueAssignment(fKey, key.toString(), fValue, Collections.emptyList());

    } else if (key instanceof IntFunctionLoc) {
      IntFunctionLoc cKey = (IntFunctionLoc) key;
      List<Object> argumentInterpretation = new ArrayList<>();
      List<ITerm> argTerms = new ArrayList<>();
      for (IdealInt arg : seqAsJavaList(cKey.args())) {
        argumentInterpretation.add(arg.bigIntValue());
        argTerms.add(ITerm.i(arg));
      }
      Formula fKey = creator.encapsulateWithTypeOf(new IFunApp(cKey.f(), asScalaBuffer(argTerms)));
      return new ValueAssignment(fKey, cKey.f().name(), fValue, argumentInterpretation);

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
