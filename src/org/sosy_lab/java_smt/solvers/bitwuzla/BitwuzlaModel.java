// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Bitwuzla;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.TermManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;

class BitwuzlaModel extends AbstractModel<Term, Sort, Void> {

  // The prover env, not the creator env!
  private final Bitwuzla bitwuzlaEnv;

  private final BitwuzlaTheoremProver prover;

  private final BitwuzlaFormulaCreator bitwuzlaCreator;
  private final ImmutableList<ValueAssignment> model;

  protected BitwuzlaModel(
      Bitwuzla bitwuzlaEnv,
      BitwuzlaTheoremProver prover,
      BitwuzlaFormulaCreator bitwuzlaCreator,
      Collection<Term> assertedTerms) {
    super(prover, bitwuzlaCreator);
    this.bitwuzlaEnv = bitwuzlaEnv;
    this.prover = prover;
    this.bitwuzlaCreator = bitwuzlaCreator;

    // We need to generate and save this at construction time as Bitwuzla has no functionality to
    // give a persistent reference to the model. If the SMT engine is used somewhere else, the
    // values we get out of it might change!
    model = generateModel(assertedTerms);
  }

  /** Build a list of assignments that stays valid after closing the model. */
  private ImmutableList<ValueAssignment> generateModel(Collection<Term> assertedTerms) {
    checkState(!isClosed());
    checkState(!prover.isClosed(), "Cannot use model after prover is closed");
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    for (Term expr : assertedTerms) {
      creator.extractVariablesAndUFs(expr, true, (name, f) -> builder.addAll(getAssignments(f)));
    }
    return builder.build().asList();
  }

  /**
   * Takes a (nested) select statement and returns its indices. For example: From "(SELECT (SELECT(
   * SELECT 3 arr) 2) 1)" we return "[1,2,3]"
   */
  private ImmutableList<Term> getArrayIndices(Term array) {
    ImmutableList.Builder<Term> indices = ImmutableList.builder();
    while (array.kind().equals(Kind.ARRAY_SELECT)) {
      indices.add(array.get(1));
      array = array.get(0);
    }
    return indices.build().reverse();
  }

  /** Takes a select statement with multiple indices and returns the variable name at the bottom. */
  private String getVar(Term array) {
    while (array.kind().equals(Kind.ARRAY_SELECT)) {
      array = array.get(0);
    }
    return array.symbol();
  }

  /**
   * Build assignment for an array value.
   *
   * @param expr The array term, e.g., a variable
   * @param value The model value term returned by Bitwuzla for the array, e.g., a Store chain
   * @return A list of value assignments for all elements in the array, including nested arrays
   */
  private List<ValueAssignment> buildArrayAssignments(Term expr, Term value) {
    TermManager termManager = bitwuzlaCreator.getTermManager();

    // Iterate down the Store-chain: (Store tail index element)
    List<ValueAssignment> result = new ArrayList<>();
    while (value.kind().equals(Kind.ARRAY_STORE)) {
      Term index = value.get(1);
      Term element = value.get(2);
      Term select = termManager.mk_term(Kind.ARRAY_SELECT, expr, index);

      // CASE 1: nested array dimension, let's recurse deeper
      if (expr.sort().array_element().is_array()) {
        result.addAll(buildArrayAssignments(select, element));

      } else {
        // CASE 2: final element, let's get the assignment and proceed with its sibling
        result.add(
            new ValueAssignment(
                creator.encapsulate(creator.getFormulaType(element), select),
                creator.encapsulate(creator.getFormulaType(element), element),
                creator.encapsulateBoolean(termManager.mk_term(Kind.EQUAL, select, element)),
                getVar(expr),
                creator.convertValue(element, element),
                FluentIterable.from(getArrayIndices(select))
                    .transform(creator::convertValue)
                    .toList()));
      }

      // Move to the next Store in the chain
      value = value.get(0);
    }

    // End of chain must be CONST_ARRAY.
    checkState(
        value.kind().equals(Kind.CONST_ARRAY), "Unexpected array value structure: %s", value);

    return result;
  }

  private Term buildEqForTwoTerms(Term left, Term right) {
    assert left.sort().equals(right.sort());
    Kind kind = Kind.EQUAL;
    if (left.sort().is_fp() || right.sort().is_fp()) {
      kind = Kind.FP_EQUAL;
    }
    return bitwuzlaCreator.getTermManager().mk_term(kind, left, right);
  }

  private ValueAssignment getAssignmentForUfInstantiation(Term pTerm) {
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

  private List<ValueAssignment> getAssignments(Term pKeyTerm) {

    // handle UF instantiations
    if (pKeyTerm.kind() == Kind.APPLY) {
      return ImmutableList.of(getAssignmentForUfInstantiation(pKeyTerm));
    }

    // handle array assignments
    final Term valueTerm = bitwuzlaEnv.get_value(pKeyTerm);
    if (pKeyTerm.sort().is_array()) {
      return buildArrayAssignments(pKeyTerm, valueTerm);
    }

    // handle simple assignments
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    for (Term child : pKeyTerm.children()) {
      argumentInterpretationBuilder.add(evaluateImpl(child));
    }
    return ImmutableList.of(
        new ValueAssignment(
            creator.encapsulateWithTypeOf(pKeyTerm),
            creator.encapsulateWithTypeOf(valueTerm),
            creator.encapsulateBoolean(buildEqForTwoTerms(pKeyTerm, valueTerm)),
            checkNotNull(pKeyTerm.symbol()),
            creator.convertValue(pKeyTerm, valueTerm),
            argumentInterpretationBuilder.build()));
  }

  @Override
  protected @Nullable Term evalImpl(Term formula) {
    checkState(!isClosed());
    checkState(!prover.isClosed(), "Cannot use model after prover is closed");
    return bitwuzlaEnv.get_value(formula);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return model;
  }
}
