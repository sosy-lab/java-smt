// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
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
        variablesBuilder.addAll(buildArrayAssignment(term, bitwuzlaEnv.get_value(term)));

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

  /** Takes a (nested) select statement and returns its indices. */
  private Iterable<Term> getArgs(Term array) {
    if (array.kind().equals(Kind.ARRAY_SELECT)) {
      return FluentIterable.concat(getArgs(array.get(0)), ImmutableList.of(array.get(1)));
    } else {
      return ImmutableList.of();
    }
  }

  /** Takes a select statement with multiple indices and returns the variable name at the bottom. */
  private String getVar(Term array) {
    if (array.kind().equals(Kind.ARRAY_SELECT)) {
      return getVar(array.get(0));
    } else {
      return array.symbol();
    }
  }

  /** Build assignment for an array value. */
  private Iterable<ValueAssignment> buildArrayAssignment(Term expr, Term value) {
    // Bitwuzla returns values such as "(Store (Store ... i1,1 e1,1) i1,0 e1,0)" where the i1,x
    // match the first index of the array and the elements e1,Y can again be arrays (if there is
    // more than one index). We need "pattern match" this values to extract assignments from it.
    // Initially we have:
    //  arr = (Store (Store ... i1,1 e1,1) i1,0 e1,0)
    // where 'arr' is the name of the variable. By applying (Select i1,0 ...) to both side we get:
    // (Select i1,0 arr) = (Select i1,0 (Store (Store ... i1,1 e1,1) i1,0 e1,0))
    // The right side simplifies to e1,0 as the index matches. We need to continue with this for
    // all other matches to the first index, that is
    //  (Select i1,1 arr) = (Select i1,0 (Store (Store ... i1,1 e1,1) i1,0 e1,0))
    //                    = (Select i1,0 (Store ... i1,1 e1,1))
    //                    = e1,1
    // until all matches are explored and the bottom of the Store chain is reached. If the array
    // has more than one dimension we also have to descend into the elements to apply the next
    // index there. For instance, let's consider a 2-dimensional array with type (Array Int ->
    // (Array Int -> Int)). After matching the first index just as in the above example we might
    // have:
    //  (Select i1,0 arr) = (Select i1,0 (Store (Store ... i1,1 e1,1) i1,0 e1,0)) = e1,0
    // In this case e1,0 is again a Store chain, let's say e1,0 := (Store (Store ... i2,1 e2,1)
    // i2,0 e2,0), and we now continue with the second index:
    //  (Select i2,1 (Select i1,0 arr)) = (Select i2,1 (Store (Store ... i2,1 e2,1) i2,0 e2,0)) =
    //                                  = e2,1
    // This again has to be done for all possible matches.
    // Once we've reached the last index, the successor element will be a non-array value. We
    // then create the final assignments and return:
    //  (Select iK,mK ... (Select i2,1 (Select i1,0 arr)) = eik,mK
    if (value.kind().equals(Kind.ARRAY_STORE)) {
      // This is a Store node for the current index. We need to follow the chain downwards to
      // match this index, while also exploring the successor for the other indices
      Term index = value.get(1);
      Term element = value.get(2);

      TermManager termManager = bitwuzlaCreator.getTermManager();
      Term select = termManager.mk_term(Kind.ARRAY_SELECT, expr, index);

      Iterable<ValueAssignment> current;
      if (expr.sort().array_element().is_array()) {
        current = buildArrayAssignment(select, element);
      } else {
        Term equation = termManager.mk_term(Kind.EQUAL, select, element);

        current =
            FluentIterable.of(
                new ValueAssignment(
                    creator.encapsulate(creator.getFormulaType(element), select),
                    creator.encapsulate(creator.getFormulaType(element), element),
                    creator.encapsulateBoolean(equation),
                    getVar(expr),
                    creator.convertValue(element, element),
                    FluentIterable.from(getArgs(select))
                        .transform(creator::convertValue)
                        .toList()));
      }
      return FluentIterable.concat(current, buildArrayAssignment(expr, value.get(0)));

    } else if (value.kind().equals(Kind.CONST_ARRAY)) {
      // We've reached the end of the Store chain
      return ImmutableList.of();

    } else {
      // Should be unreachable
      // We assume that array values are made up of "const" and "store" nodes with non-array
      // constants as leaves
      throw new AssertionError(
          String.format(
              "Can't process model value for variable '%s'. Please report this issue to the "
                  + "JavaSMT developers",
              getVar(expr)));
    }
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
