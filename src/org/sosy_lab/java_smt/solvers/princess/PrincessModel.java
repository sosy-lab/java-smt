// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static scala.collection.JavaConverters.asJava;

import ap.SimpleAPI.PartialModel;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.ITerm;
import ap.theories.ExtArray;
import ap.types.Sort;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import scala.Option;

class PrincessModel extends CachingAbstractModel<IExpression, Sort, PrincessEnvironment> {
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
    Map<IFunApp, ITerm> arrays = getArrays(interpretation);

    // then iterate over the model and generate the assignments
    ImmutableSet.Builder<ValueAssignment> assignments = ImmutableSet.builder();
    for (Map.Entry<IExpression, IExpression> entry : asJava(interpretation).entrySet()) {
      ValueAssignment assignment = getAssignment(entry.getKey(), entry.getValue(), arrays);
      if (assignment != null) {
        assignments.add(assignment);
      }
    }

    return assignments.build().asList();
  }

  /**
   * Collect array-models, we need them to replace identifiers later.
   *
   * <p>Princess models arrays as filled, based on a zero-filled array. The model for an
   * array-access (via 'select') uses the filled array instead of the name and is handled later (see
   * #getAssignment). The model gives more information, like the (partially) filled array and all
   * array accesses based on (here comes the weird part:) some intermediate array evaluation.
   *
   * <p>Example: "arr[5]=123" with a following "result_arr[6]=123" (writing into an array in SMT
   * returns a new copy of it!) is modeled as
   *
   * <pre>
   * {
   *     x -> 123,
   *     arr -> store(const(0), 5, 123),
   *     store(store(const(0), 5, 123), 6, 123) -> store(store(const(0), 5, 123), 6, 123),
   *     select(store(const(0), 5, 123), 5) -> 123
   * }
   * </pre>
   *
   * <p>The returned mapping contains the mapping of the complete array value ("store(const(0), 5,
   * 123)") to the identifier ("arr").
   */
  private Map<IFunApp, ITerm> getArrays(
      scala.collection.Map<IExpression, IExpression> interpretation) {
    Map<IFunApp, ITerm> arrays = new HashMap<>();
    for (Map.Entry<IExpression, IExpression> entry : asJava(interpretation).entrySet()) {
      if (entry.getKey() instanceof IConstant) {
        ITerm maybeArray = (IConstant) entry.getKey();
        IExpression value = entry.getValue();
        if (creator.getEnv().hasArrayType(maybeArray)
            && value instanceof IFunApp
            && ExtArray.Store$.MODULE$.unapply(((IFunApp) value).fun()).isDefined()) {
          arrays.put((IFunApp) value, maybeArray);
        }
      }
    }
    return arrays;
  }

  private @Nullable ValueAssignment getAssignment(
      IExpression key, IExpression value, Map<IFunApp, ITerm> pArrays) {
    IExpression fValue = value;
    final IExpression fKey;
    final String name;
    final IFormula fAssignment;
    Collection<Object> argumentInterpretations = ImmutableList.of();

    if (key instanceof IAtom) {
      fKey = key;
      name = key.toString();
      fAssignment = new IBinFormula(IBinJunctor.Eqv(), (IAtom) key, (IFormula) fValue);

    } else if (key instanceof IConstant) {
      if (creator.getEnv().hasArrayType(key)) {
        // array-access, for explanation see #getArrays
        return null;
      } else {
        fKey = key;
        name = key.toString();
        fAssignment = ((IConstant) key).$eq$eq$eq((ITerm) fValue);
      }

    } else if (key instanceof IFunApp) {
      IFunApp cKey = (IFunApp) key;

      if (ExtArray.Select$.MODULE$.unapply(cKey.fun()).isDefined()) {
        // array-access, for explanation see #getArrayAddresses
        ITerm arrayId = cKey.args().apply(Integer.valueOf(0));
        ITerm arrayIndex = cKey.args().apply(Integer.valueOf(1));
        ITerm arrayF = pArrays.get(arrayId);
        if (arrayF == null) {
          // intermediate array store, like a tmp-variable, happens for repeated
          // store-operations
          return null;
        }
        fKey = creator.getEnv().makeSelect(arrayF, arrayIndex);
        name = arrayF.toString();
        argumentInterpretations = ImmutableList.of(creator.convertValue(arrayIndex));

      } else if (ExtArray.Store$.MODULE$.unapply(cKey.fun()).isDefined()) {
        // array-access, for explanation see #getArrayAddresses
        // IdealInt sourceArray = cKey.args().apply(0);
        ITerm arrayIndex2 = cKey.args().apply(Integer.valueOf(1));
        ITerm arrayContent = cKey.args().apply(Integer.valueOf(2));
        ITerm arrayF2 = pArrays.get(value);
        if (arrayF2 == null) {
          // intermediate array store, like a tmp-variable, happens for repeated
          // store-operations
          return null;
        }
        fKey = creator.getEnv().makeSelect(arrayF2, arrayIndex2);
        fValue = arrayContent;
        name = arrayF2.toString();
        argumentInterpretations = ImmutableList.of(creator.convertValue(arrayIndex2));

      } else {
        // normal variable or UF
        argumentInterpretations = new ArrayList<>();
        for (ITerm arg : asJava(cKey.args())) {
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
