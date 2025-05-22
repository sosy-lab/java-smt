// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Bitwuzla;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;

class BitwuzlaModel extends AbstractModel<Term, Sort, Void> {

  // The prover env, not the creator env!
  private final Bitwuzla bitwuzlaEnv;

  private final BitwuzlaTheoremProver prover;

  private final BitwuzlaFormulaCreator bitwuzlaCreator;
  private final ImmutableList<Term> assertedTerms;

  protected BitwuzlaModel(
      Bitwuzla bitwuzlaEnv,
      BitwuzlaTheoremProver prover,
      BitwuzlaFormulaCreator bitwuzlaCreator,
      Collection<Term> assertedTerms) {
    super(prover, bitwuzlaCreator);
    this.bitwuzlaEnv = bitwuzlaEnv;
    this.prover = prover;
    this.bitwuzlaCreator = bitwuzlaCreator;
    this.assertedTerms = ImmutableList.copyOf(assertedTerms);
  }

  /** Build a list of assignments that stays valid after closing the model. */
  @Override
  public ImmutableList<ValueAssignment> asList() {
    Preconditions.checkState(!isClosed());
    Preconditions.checkState(!prover.isClosed(), "Cannot use model after prover is closed");
    ImmutableSet.Builder<ValueAssignment> variablesBuilder = ImmutableSet.builder();
    Deque<Term> queue = new ArrayDeque<>(assertedTerms);
    while (!queue.isEmpty()) {
      Term term = queue.removeFirst();
      Sort sort = term.sort();
      Vector_Term children = term.children();
      // The term might be a value (variable or const, w only variable having a symbol)
      // an array, an UF, or an FP or a function.
      // Functions are just split into their children and those are traversed
      if (sort.is_rm()) {
        // Do nothing
      } else if (term.kind() == Kind.APPLY) {
        variablesBuilder.add(getUFAssignment(term));
        for (int i = 1; i < children.size(); i++) {
          queue.addLast(children.get(i));
        }

      } else if (sort.is_bv() && term.is_const()) {
        variablesBuilder.add(getSimpleAssignment(term));

      } else if (sort.is_bool() && term.is_const()) {
        variablesBuilder.add(getSimpleAssignment(term));

      } else if (sort.is_fp() && term.is_const()) {
        // We can't eval FP properly at the moment, we just return whatever the solver gives us
        // (BV representation of the FP)
        variablesBuilder.add(getSimpleAssignment(term));

      } else if (sort.is_array() && term.is_const()) {
        variablesBuilder.addAll(getArrayAssignment(term));

      } else {
        for (Term child : children) {
          queue.addLast(child);
        }
      }
    }

    return variablesBuilder.build().asList();
  }

  private ValueAssignment getSimpleAssignment(Term pTerm) {
    List<Object> argumentInterpretation = new ArrayList<>();
    Term valueTerm = bitwuzlaEnv.get_value(pTerm);
    String name = pTerm.symbol();
    assert name != null;
    return new ValueAssignment(
        bitwuzlaCreator.encapsulateWithTypeOf(pTerm),
        bitwuzlaCreator.encapsulateWithTypeOf(valueTerm),
        bitwuzlaCreator.encapsulateBoolean(buildEqForTwoTerms(pTerm, valueTerm)),
        name,
        bitwuzlaCreator.convertValue(valueTerm),
        argumentInterpretation);
  }

  private Collection<ValueAssignment> getArrayAssignment(Term pTerm) {
    return getArrayAssignments(pTerm, ImmutableList.of());
  }

  // TODO: check this in detail. I think this might be incomplete.
  // We should add more Model tests in general. As most are parsing and int based!
  private Collection<ValueAssignment> getArrayAssignments(Term pTerm, List<Object> upperIndices) {
    // Array children for store are structured in the following way:
    // {starting array, index, value} in "we add value at index to array"
    // Selections are structured: {starting array, index}
    // Just declared (empty) arrays return an empty array

    // Example Formula: (SELECT ARRAY INDEX)
    // new ValueAssignment((SELECT ARRAY INDEX), value formula of INDEX, (SELECT ARRAY INDEX) =
    // value of index, name of INDEX, actual java value of index, {return java value of the
    // formula})

    // TODO: Array equals value
    Term array = pTerm;
    Collection<ValueAssignment> assignments = new ArrayList<>();
    Set<Term> indices = new HashSet<>();
    while (array.sort().is_array()) {
      // Here we either have STORE; SELECT or an empty Array
      Vector_Term children = array.children();
      List<Object> innerIndices = new ArrayList<>(upperIndices);
      String name = getArrayName(array);
      Preconditions.checkNotNull(name, "unexpected array %s without name", array);
      if (children.isEmpty()) {
        // Empty array
        return assignments;
      } else if (children.size() == 2) {
        // SELECT expression
        Term index = children.get(1);
        if (!indices.add(index)) {
          continue;
        }

        Term indexValue = bitwuzlaEnv.get_value(index);
        innerIndices.add(evaluateImpl(indexValue));

        // The value of an SELECT is equal to the content
        Term valueTerm = bitwuzlaEnv.get_value(array);

        assignments.add(
            new ValueAssignment(
                bitwuzlaCreator.encapsulateWithTypeOf(array),
                bitwuzlaCreator.encapsulateWithTypeOf(valueTerm),
                creator.encapsulateBoolean(buildEqForTwoTerms(array, valueTerm)),
                name,
                evaluateImpl(valueTerm),
                innerIndices));
        array = children.get(0);

      } else {
        // STORE expression
        assert children.size() == 3;
        Term index = children.get(1);
        Term content = children.get(2);

        if (!indices.add(index)) {
          continue;
        }

        Term indexValue = bitwuzlaEnv.get_value(index);
        Term contentValue = bitwuzlaEnv.get_value(content);
        innerIndices.add(evaluateImpl(indexValue));
        assignments.add(
            new ValueAssignment(
                bitwuzlaCreator.encapsulateWithTypeOf(array),
                bitwuzlaCreator.encapsulateWithTypeOf(content),
                creator.encapsulateBoolean(buildEqForTwoTerms(array, contentValue)),
                name,
                evaluateImpl(contentValue),
                innerIndices));

        array = children.get(0);
        assignments.addAll(getArrayAssignments(array, innerIndices));
      }
    }
    return assignments;
  }

  private String getArrayName(Term array) {
    String name = array.symbol();
    if (name != null) {
      return name;
    }
    return getArrayName(array.get(0));
  }

  private Term buildEqForTwoTerms(Term left, Term right) {
    assert left.sort().equals(right.sort());
    Kind kind = Kind.EQUAL;
    if (left.sort().is_fp() || right.sort().is_fp()) {
      kind = Kind.FP_EQUAL;
    }
    return bitwuzlaCreator.getTermManager().mk_term(kind, left, right);
  }

  private ValueAssignment getUFAssignment(Term pTerm) {
    Term valueTerm = bitwuzlaEnv.get_value(pTerm);
    // The first child is the decl, the others are args
    Vector_Term children = pTerm.children();
    String name = children.get(0).symbol();
    assert name != null;

    List<Object> argumentInterpretation = new ArrayList<>();
    for (int i = 1; i < children.size(); i++) {
      Term child = children.get(i);
      Term childValue = bitwuzlaEnv.get_value(child);
      argumentInterpretation.add(creator.convertValue(childValue));
    }

    return new ValueAssignment(
        bitwuzlaCreator.encapsulateWithTypeOf(pTerm),
        bitwuzlaCreator.encapsulateWithTypeOf(valueTerm),
        bitwuzlaCreator.encapsulateBoolean(buildEqForTwoTerms(pTerm, valueTerm)),
        name,
        bitwuzlaCreator.convertValue(valueTerm),
        argumentInterpretation);
  }

  @Override
  protected @Nullable Term evalImpl(Term formula) {
    Preconditions.checkState(!prover.isClosed(), "Cannot use model after prover is closed");
    return bitwuzlaEnv.get_value(formula);
  }
}
