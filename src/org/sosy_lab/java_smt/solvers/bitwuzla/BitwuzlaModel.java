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

class BitwuzlaModel extends AbstractModel<Long, Long, Long> {

  // The prover env, not the creator env!
  private final long bitwuzlaEnv;

  private final BitwuzlaTheoremProver prover;

  private final BitwuzlaFormulaCreator bitwuzlaCreator;
  private final ImmutableList<Long> assertedTerms;

  protected BitwuzlaModel(
      long bitwuzlaEnv,
      BitwuzlaTheoremProver prover,
      BitwuzlaFormulaCreator bitwuzlaCreator,
      Collection<Long> assertedTerms) {
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
    Deque<Long> queue = new ArrayDeque<>(assertedTerms);
    while (!queue.isEmpty()) {
      long term = queue.removeFirst();
      long[] children = bitwuzlaJNI.bitwuzla_term_get_children(term, new long[1]);
      // The term might be a value (variable or const, w only variable having a symbol)
      // an array, an UF, or an FP or a function.
      // Functions are just split into their children and those are traversed
      if (bitwuzlaJNI.bitwuzla_term_is_rm(term)) {
        // Do nothing
      } else if (bitwuzlaJNI.bitwuzla_term_get_kind(term)
          == BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue()) {
        variablesBuilder.add(getUFAssignment(term));
        for (int i = 1; i < children.length; i++) {
          queue.addLast(children[i]);
        }

      } else if (bitwuzlaJNI.bitwuzla_term_is_bv(term)
          && bitwuzlaJNI.bitwuzla_term_is_const(term)) {
        variablesBuilder.add(getSimpleAssignment(term));

      } else if (bitwuzlaJNI.bitwuzla_term_is_bool(term)
          && bitwuzlaJNI.bitwuzla_term_is_const(term)) {
        variablesBuilder.add(getSimpleAssignment(term));

      } else if (bitwuzlaJNI.bitwuzla_term_is_fp(term)
          && bitwuzlaJNI.bitwuzla_term_is_const(term)) {
        // We can't eval FP properly at the moment, we just return whatever the solver gives us
        // (BV representation of the FP)
        variablesBuilder.add(getSimpleAssignment(term));

      } else if (bitwuzlaJNI.bitwuzla_term_is_array(term)
          && bitwuzlaJNI.bitwuzla_term_is_const(term)) {
        variablesBuilder.addAll(getArrayAssignment(term));

      } else {
        for (long child : children) {
          queue.addLast(child);
        }
      }
    }

    return variablesBuilder.build().asList();
  }

  private ValueAssignment getSimpleAssignment(long pTerm) {
    List<Object> argumentInterpretation = new ArrayList<>();
    long valueTerm = bitwuzlaJNI.bitwuzla_get_value(bitwuzlaEnv, pTerm);
    String name = bitwuzlaJNI.bitwuzla_term_get_symbol(pTerm);
    assert name != null;
    return new ValueAssignment(
        bitwuzlaCreator.encapsulateWithTypeOf(pTerm),
        bitwuzlaCreator.encapsulateWithTypeOf(valueTerm),
        bitwuzlaCreator.encapsulateBoolean(buildEqForTwoTerms(pTerm, valueTerm)),
        name,
        bitwuzlaCreator.convertValue(valueTerm),
        argumentInterpretation);
  }

  private Collection<ValueAssignment> getArrayAssignment(long pTerm) {
    return getArrayAssignments(pTerm, ImmutableList.of());
  }

  // TODO: check this in detail. I think this might be incomplete.
  // We should add more Model tests in general. As most are parsing and int based!
  private Collection<ValueAssignment> getArrayAssignments(long pTerm, List<Object> upperIndices) {
    // Array children for store are structured in the following way:
    // {starting array, index, value} in "we add value at index to array"
    // Selections are structured: {starting array, index}
    // Just declared (empty) arrays return an empty array

    // Example Formula: (SELECT ARRAY INDEX)
    // new ValueAssignment((SELECT ARRAY INDEX), value formula of INDEX, (SELECT ARRAY INDEX) =
    // value of index, name of INDEX, actual java value of index, {return java value of the
    // formula})

    // TODO: Array equals value
    long array = pTerm;
    Collection<ValueAssignment> assignments = new ArrayList<>();
    Set<Long> indices = new HashSet<>();
    while (bitwuzlaJNI.bitwuzla_term_is_array(array)) {
      // Here we either have STORE; SELECT or an empty Array
      long[] children = bitwuzlaJNI.bitwuzla_term_get_children(array, new long[1]);
      List<Object> innerIndices = new ArrayList<>(upperIndices);
      String name = getArrayName(array);
      assert name != null;
      if (children.length == 0) {
        // Empty array
        return assignments;
      } else if (children.length == 2) {
        // SELECT expression
        long index = children[1];

        if (!indices.add(index)) {
          continue;
        }

        long indexValue = bitwuzlaJNI.bitwuzla_get_value(bitwuzlaEnv, index);
        innerIndices.add(evaluateImpl(indexValue));

        // The value of an SELECT is equal to the content
        long valueTerm = bitwuzlaJNI.bitwuzla_get_value(bitwuzlaEnv, array);

        assignments.add(
            new ValueAssignment(
                bitwuzlaCreator.encapsulateWithTypeOf(array),
                bitwuzlaCreator.encapsulateWithTypeOf(valueTerm),
                creator.encapsulateBoolean(buildEqForTwoTerms(pTerm, valueTerm)),
                name,
                evaluateImpl(valueTerm),
                innerIndices));
        array = children[0];

      } else {
        // STORE expression
        assert children.length == 3;
        long index = children[1];
        long content = children[2];

        if (!indices.add(index)) {
          continue;
        }

        long indexValue = bitwuzlaJNI.bitwuzla_get_value(bitwuzlaEnv, index);
        long contentValue = bitwuzlaJNI.bitwuzla_get_value(bitwuzlaEnv, content);
        innerIndices.add(evaluateImpl(indexValue));
        assignments.add(
            new ValueAssignment(
                bitwuzlaCreator.encapsulateWithTypeOf(array),
                bitwuzlaCreator.encapsulateWithTypeOf(content),
                creator.encapsulateBoolean(buildEqForTwoTerms(array, contentValue)),
                name,
                evaluateImpl(contentValue),
                innerIndices));

        array = children[0];
        assignments.addAll(getArrayAssignments(array, innerIndices));
      }
    }
    return assignments;
  }

  private String getArrayName(long array) {
    String name = bitwuzlaJNI.bitwuzla_term_get_symbol(array);
    if (name != null) {
      return name;
    }
    return getArrayName(bitwuzlaJNI.bitwuzla_term_get_children(array, new long[1])[0]);
  }

  private long buildEqForTwoTerms(long left, long right) {
    assert bitwuzlaJNI.bitwuzla_term_is_equal_sort(left, right);
    BitwuzlaKind kind = BitwuzlaKind.BITWUZLA_KIND_EQUAL;
    if (bitwuzlaJNI.bitwuzla_term_is_fp(left)) {
      kind = BitwuzlaKind.BITWUZLA_KIND_FP_EQUAL;
    }
    return bitwuzlaJNI.bitwuzla_mk_term2(kind.swigValue(), left, right);
  }

  private ValueAssignment getUFAssignment(long pTerm) {
    long valueTerm = bitwuzlaJNI.bitwuzla_get_value(bitwuzlaEnv, pTerm);
    // The first child is the decl, the others are args
    long[] children = bitwuzlaJNI.bitwuzla_term_get_children(pTerm, new long[1]);
    String name = bitwuzlaJNI.bitwuzla_term_get_symbol(children[0]);
    assert name != null;

    List<Object> argumentInterpretation = new ArrayList<>();
    for (int i = 1; i < children.length; i++) {
      long child = children[i];
      long childValue = bitwuzlaJNI.bitwuzla_get_value(bitwuzlaEnv, child);
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
  protected @Nullable Long evalImpl(Long formula) {
    Preconditions.checkState(!prover.isClosed(), "Cannot use model after prover is closed");
    return bitwuzlaJNI.bitwuzla_get_value(bitwuzlaEnv, formula);
  }
}
