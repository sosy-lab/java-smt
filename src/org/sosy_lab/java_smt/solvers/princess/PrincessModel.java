// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableListCopy;
import static scala.collection.JavaConverters.asJava;

import ap.api.PartialModel;
import ap.api.SimpleAPI;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.ITerm;
import ap.terfor.preds.Predicate;
import ap.theories.arrays.ExtArray;
import ap.theories.arrays.ExtArray.Select$;
import ap.theories.arrays.ExtArray.Store$;
import ap.types.Sort;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class PrincessModel extends AbstractModel<IExpression, Sort, PrincessEnvironment> {
  private final PartialModel model;
  private final SimpleAPI api;

  PrincessModel(
      PrincessAbstractProver<?> pProver,
      PartialModel partialModel,
      FormulaCreator<IExpression, Sort, PrincessEnvironment, ?> creator,
      SimpleAPI pApi) {
    super(pProver, creator);
    this.model = partialModel;
    this.api = pApi;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    scala.collection.Map<IExpression, IExpression> interpretation = model.interpretation();

    // get abbreviations, we do not want to export them.
    Set<Predicate> abbrevs = new LinkedHashSet<>();
    for (var entry : asJava(api.ap$api$SimpleAPI$$apiStack().abbrevPredicates()).entrySet()) {
      abbrevs.add(entry.getKey()); // collect the abbreviation.
      abbrevs.add(entry.getValue()._2()); // the definition is also handled as abbreviation here.
    }

    // then iterate over the model and generate the assignments
    ImmutableSet.Builder<ValueAssignment> assignments = ImmutableSet.builder();
    for (Map.Entry<IExpression, IExpression> entry : asJava(interpretation).entrySet()) {
      if (!entry.getKey().toString().equals("Rat_denom") && !isAbbrev(abbrevs, entry.getKey())) {
        assignments.addAll(getAssignments(entry.getKey(), entry.getValue()));
      }
    }
    return assignments.build().asList();
  }

  private boolean isAbbrev(Set<Predicate> abbrevs, IExpression var) {
    return var instanceof IAtom && abbrevs.contains(((IAtom) var).pred());
  }

  private Collection<ValueAssignment> getAssignments(IExpression key, IExpression value) {

    // first check array-access.
    // those cases can return multiple assignments per model entry.
    if (creator.getEnv().hasArrayType(key)) {
      if (key instanceof IConstant && value instanceof IFunApp) {
        return buildArrayAssignments((IConstant) key, (IFunApp) value);
      } else {
        return ImmutableList.of();
      }

    } else {
      // then handle assignments for non-array cases.
      // we expect at most one assignment per model entry.

      String name;
      IFormula fAssignment;
      List<Object> argumentInterpretations = ImmutableList.of();

      if (key instanceof IAtom) {
        if (isArrayAccess(((IAtom) key).pred())) { // arrays are handled separately, see above
          return ImmutableList.of();
        }
        name = key.toString();
        fAssignment = new IBinFormula(IBinJunctor.Eqv(), (IAtom) key, (IFormula) value);

      } else if (key instanceof IConstant) {
        name = key.toString();
        fAssignment = ((IConstant) key).$eq$eq$eq((ITerm) value);

      } else if (key instanceof IFunApp) {
        IFunApp cKey = (IFunApp) key;
        if (isArrayAccess(cKey.fun())) { // arrays are handled separately, see above
          return ImmutableList.of();
        }
        // normal variable or UF
        argumentInterpretations = new ArrayList<>();
        for (ITerm arg : asJava(cKey.args())) {
          argumentInterpretations.add(creator.convertValue(arg));
        }
        name = cKey.fun().name();
        fAssignment = ((ITerm) key).$eq$eq$eq((ITerm) value);

      } else {
        throw new AssertionError(
            String.format("unknown type of key: %s -> %s (%s)", key, value, key.getClass()));
      }

      return ImmutableList.of(
          new ValueAssignment(
              creator.encapsulateWithTypeOf(key),
              creator.encapsulateWithTypeOf(value),
              creator.encapsulateBoolean(fAssignment),
              name,
              creator.convertValue(value),
              argumentInterpretations));
    }
  }

  private boolean isArrayAccess(Predicate predicate) {
    return "arrayConstant".equals(predicate.name());
  }

  private boolean isArrayAccess(IFunction function) {
    return "valueAlmostEverywhere".equals(function.name())
        || Select$.MODULE$.unapply(function).isDefined()
        || Store$.MODULE$.unapply(function).isDefined();
  }

  /**
   * Takes a (nested) select statement and returns its indices. For example: From "(SELECT (SELECT(
   * SELECT 3 arr) 2) 1)" we return "[1,2,3]"
   */
  private ImmutableList<IExpression> getArrayIndices(IExpression array) {
    ImmutableList.Builder<IExpression> indices = ImmutableList.builder();
    while (array instanceof IFunApp
        && ExtArray.Select$.MODULE$.unapply(((IFunApp) array).fun()).isDefined()) {
      indices.add(array.apply(1));
      array = array.apply(0);
    }
    return indices.build().reverse();
  }

  /** Takes a select statement with multiple indices and returns the variable name at the bottom. */
  private String getVar(IExpression array) {
    while (array instanceof IFunApp
        && ExtArray.Select$.MODULE$.unapply(((IFunApp) array).fun()).isDefined()) {
      array = array.apply(0);
    }
    return array.toString();
  }

  /** unrolls an constant array assignment. */
  private Collection<ValueAssignment> buildArrayAssignments(ITerm arraySymbol, IFunApp value) {

    // Iterate down the Store-chain: (Store tail index element)
    List<ValueAssignment> result = new ArrayList<>();
    while (ExtArray.Store$.MODULE$.unapply(value.fun()).isDefined()) {
      ITerm index = value.apply(1);
      ITerm element = value.apply(2);
      ITerm select = creator.getEnv().makeSelect(arraySymbol, index);

      // CASE 1: nested array dimension, let's recurse deeper
      if (creator.getEnv().hasArrayType(element)) {
        result.addAll(buildArrayAssignments(select, (IFunApp) element));

      } else {
        // CASE 2: final element, let's get the assignment and proceed with its sibling
        result.add(
            new ValueAssignment(
                creator.encapsulateWithTypeOf(select),
                creator.encapsulateWithTypeOf(element),
                creator.encapsulateBoolean(
                    ap.parser.IExpression.Eq$.MODULE$.apply(select, element)),
                getVar(arraySymbol),
                creator.convertValue(element),
                transformedImmutableListCopy(getArrayIndices(select), this::evaluateImpl)));
      }

      // Move to the next Store in the chain
      value = (IFunApp) value.apply(0);
    }

    // End of chain must be CONST_ARRAY.
    checkState(
        ExtArray.Const$.MODULE$.unapply(value.fun()).isDefined(),
        "Unexpected array value structure: %s",
        value);

    return result;
  }

  @Override
  public String toString() {
    return model.toString();
  }

  @Override
  protected @Nullable IExpression evalImpl(IExpression formula) {
    IExpression simplified = creator.getEnv().simplify(formula);
    if (formula instanceof ITerm) {
      return model.evalToTerm((ITerm) simplified).getOrElse(() -> null);
    } else if (formula instanceof IFormula) {
      return model.evalExpression(simplified).getOrElse(() -> null);
    } else {
      throw new AssertionError(); // unreachable
    }
  }
}
