// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableListCopy;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

public class CVC5Model extends AbstractModel<Term, Sort, TermManager> {

  private final ImmutableList<ValueAssignment> model;
  private final TermManager termManager;
  private final Solver solver;

  @SuppressWarnings("unused")
  private final FormulaManager mgr;

  CVC5Model(
      CVC5AbstractProver<?> pProver,
      FormulaManager pMgr,
      CVC5FormulaCreator pCreator,
      Collection<Term> pAssertedExpressions) {
    super(pProver, pCreator);
    termManager = pCreator.getEnv();
    solver = pProver.solver;
    mgr = pMgr;

    // We need to generate and save this at construction time as CVC5 has no functionality to give a
    // persistent reference to the model. If the SMT engine is used somewhere else, the values we
    // get out of it might change!
    model = generateModel(pAssertedExpressions);
  }

  @Override
  public Term evalImpl(Term f) {
    checkState(!isClosed());
    return solver.getValue(f);
  }

  private ImmutableList<ValueAssignment> generateModel(Collection<Term> assertedExpressions) {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    for (Term expr : assertedExpressions) {
      creator.extractVariablesAndUFs(
          expr,
          true,
          (name, f) -> {
            try {
              if (f.getKind() == Kind.APPLY_UF) {
                builder.add(getAssignmentForUfInstantiation(f));
              } else {
                builder.addAll(getAssignments(f));
              }
            } catch (CVC5ApiException e) {
              throw new IllegalArgumentException(
                  "Failure when retrieving assignments for term '" + f + "'.", e);
            }
          });
    }
    return builder.build().asList();
  }

  /**
   * Get a single value assignment from an instantiation of the given uninterpreted function.
   *
   * @param pKeyTerm the UF instantiation as "(UF_NAME ARGS...)"
   * @return the value assignment as "(UF_NAME ARGS...) := VALUE"
   * @throws CVC5ApiException if CVC5 API calls fail
   */
  private ValueAssignment getAssignmentForUfInstantiation(Term pKeyTerm) throws CVC5ApiException {
    // An uninterpreted function "(UF_NAME ARGS...)" consist of N+1 children,
    // the first child is the function definition as a lambda and the result,
    // while the remaining children are the arguments.
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    for (int i = 1; i < pKeyTerm.getNumChildren(); i++) {
      Term child = pKeyTerm.getChild(i);
      checkState(
          !child.getKind().equals(Kind.VARIABLE),
          "Unexpected bound variable in UF argument: %s",
          child);
      argumentInterpretationBuilder.add(evaluateImpl(child));
    }

    String nameStr = ((CVC5FormulaCreator) creator).getName(pKeyTerm);
    Term valueTerm = solver.getValue(pKeyTerm);
    Formula keyFormula = creator.encapsulateWithTypeOf(pKeyTerm);
    Formula valueFormula = creator.encapsulateWithTypeOf(valueTerm);
    BooleanFormula equation =
        creator.encapsulateBoolean(termManager.mkTerm(Kind.EQUAL, pKeyTerm, valueTerm));
    Object value = creator.convertValue(pKeyTerm, valueTerm);

    return new ValueAssignment(
        keyFormula, valueFormula, equation, nameStr, value, argumentInterpretationBuilder.build());
  }

  /**
   * Takes a (nested) select statement and returns its indices. For example: From "(SELECT (SELECT(
   * SELECT 3 arr) 2) 1)" we return "[1,2,3]"
   */
  private ImmutableList<Term> getArrayIndices(Term array) throws CVC5ApiException {
    ImmutableList.Builder<Term> indices = ImmutableList.builder();
    while (array.getKind().equals(Kind.SELECT)) {
      indices.add(array.getChild(1));
      array = array.getChild(0);
    }
    return indices.build().reverse();
  }

  /** Takes a select statement with multiple indices and returns the variable name at the bottom. */
  private String getVar(Term array) throws CVC5ApiException {
    if (array.getKind().equals(Kind.SELECT)) {
      return getVar(array.getChild(0));
    } else {
      return array.getSymbol();
    }
  }

  /**
   * Build assignment for an array value.
   *
   * @param expr The array term, e.g., a variable
   * @param value The model value term returned by CVC5 for the array, e.g., a Store chain
   * @return A list of value assignments for all elements in the array, including nested arrays
   * @throws CVC5ApiException If CVC5 API calls fail
   */
  private List<ValueAssignment> buildArrayAssignments(Term expr, Term value)
      throws CVC5ApiException {
    // CVC5 returns values such as "(Store (Store ... i1,1 e1,1) i1,0 e1,0)" where the i1,x match
    // the first index of the array and the elements e1,Y can again be arrays (if there is more
    // than one index). We need "pattern match" this values to extract assignments from it.
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

    // Iterate down the Store-chain: (Store tail index element)
    List<ValueAssignment> result = new ArrayList<>();
    while (value.getKind().equals(Kind.STORE)) {
      Term index = value.getChild(1);
      Term element = value.getChild(2);
      Term select = creator.getEnv().mkTerm(Kind.SELECT, expr, index);

      // CASE 1: nested array dimension, let's recurse deeper
      if (expr.getSort().getArrayElementSort().isArray()) {
        result.addAll(buildArrayAssignments(select, element));

      } else {
        // CASE 2: final element, let's get the assignment and proceed with its sibling
        Term equation = creator.getEnv().mkTerm(Kind.EQUAL, select, element);
        result.add(
            new ValueAssignment(
                creator.encapsulate(creator.getFormulaType(element), select),
                creator.encapsulate(creator.getFormulaType(element), element),
                creator.encapsulateBoolean(equation),
                getVar(expr),
                creator.convertValue(element, element),
                transformedImmutableListCopy(getArrayIndices(select), this::evaluateImpl)));
      }

      // Move to the next Store in the chain
      value = value.getChild(0);
    }

    // End of chain must be CONST_ARRAY.
    checkState(
        value.getKind().equals(Kind.CONST_ARRAY), "Unexpected array value structure: %s", value);

    return result;
  }

  private List<ValueAssignment> getAssignments(Term pKeyTerm) throws CVC5ApiException {
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    for (int i = 0; i < pKeyTerm.getNumChildren(); i++) {
      argumentInterpretationBuilder.add(evaluateImpl(pKeyTerm.getChild(i)));
    }

    String nameStr = ((CVC5FormulaCreator) creator).getName(pKeyTerm);
    Term valueTerm = solver.getValue(pKeyTerm);
    if (valueTerm.getSort().isArray()) {
      return buildArrayAssignments(pKeyTerm, valueTerm);
    } else {
      Formula keyFormula = creator.encapsulateWithTypeOf(pKeyTerm);
      Formula valueFormula = creator.encapsulateWithTypeOf(valueTerm);
      BooleanFormula equation =
          creator.encapsulateBoolean(termManager.mkTerm(Kind.EQUAL, pKeyTerm, valueTerm));
      Object value = creator.convertValue(pKeyTerm, valueTerm);
      return ImmutableList.of(
          new ValueAssignment(
              keyFormula,
              valueFormula,
              equation,
              nameStr,
              value,
              argumentInterpretationBuilder.build()));
    }
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return model;
  }
}
