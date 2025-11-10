// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
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

    // We need to generate and save this at construction time as CVC4 has no functionality to give a
    // persistent reference to the model. If the SMT engine is used somewhere else, the values we
    // get out of it might change!
    model = generateModel(pAssertedExpressions);
  }

  @Override
  public Term evalImpl(Term f) {
    Preconditions.checkState(!isClosed());
    return solver.getValue(f);
  }

  private ImmutableList<ValueAssignment> generateModel(Collection<Term> assertedExpressions) {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    // Using creator.extractVariablesAndUFs we wouldn't get accurate information anymore as we
    // translate all bound vars back to their free counterparts in the visitor!
    for (Term expr : assertedExpressions) {
      // creator.extractVariablesAndUFs(expr, true, (name, f) -> builder.add(getAssignment(f)));
      try {
        recursiveAssignmentFinder(builder, expr);
      } catch (CVC5ApiException e) {
        throw new IllegalArgumentException(
            "Failure when retrieving assignments for term '" + expr + "'.", e);
      }
    }
    return builder.build().asList();
  }

  // TODO this method is highly recursive and should be rewritten with a proper visitor
  private void recursiveAssignmentFinder(ImmutableSet.Builder<ValueAssignment> builder, Term expr)
      throws CVC5ApiException {
    Sort sort = expr.getSort();
    Kind kind = expr.getKind();
    if (kind == Kind.VARIABLE || sort.isFunction()) {
      // We don't care about functions, as that's just the function definition and the nested
      // lambda term
      // We don't care about bound vars (not in a UF), as they don't return a value.
      return;
    } else if (kind == Kind.CONSTANT) {
      // Vars and UFs, as well as bound vars in UFs!
      // In CVC5 consts are variables! Free variables (in CVC5s notation, we call them bound
      // variables, created with mkVar() can never have a value!)
      builder.addAll(getAssignments(expr));
    } else if (kind == Kind.FORALL || kind == Kind.EXISTS) {
      // Body of the quantifier, with bound vars!
      Term body = expr.getChild(1);
      recursiveAssignmentFinder(builder, body);
    } else if (kind == Kind.CONST_STRING
        || kind == Kind.CONST_ARRAY
        || kind == Kind.CONST_BITVECTOR
        || kind == Kind.CONST_BOOLEAN
        || kind == Kind.CONST_FLOATINGPOINT
        || kind == Kind.CONST_RATIONAL
        || kind == Kind.CONST_ROUNDINGMODE
        || kind == Kind.CONST_SEQUENCE) {
      // Constants, do nothing
    } else if (kind == Kind.APPLY_UF) {
      builder.add(getAssignmentForUf(expr));

    } else {
      // Only nested terms (AND, OR, ...) are left
      for (Term child : expr) {
        recursiveAssignmentFinder(builder, child);
      }
    }
  }

  private ValueAssignment getAssignmentForUf(Term pKeyTerm) throws CVC5ApiException {
    // Ufs consist of arguments + 1 child, the first child is the function definition as a lambda
    // and the result, while the remaining children are the arguments.
    // Note: we can't evaluate bound variables!
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    boolean boundFound = false;
    // We don't want the first argument of uf applications as it is the declaration
    for (int i = 1; i < pKeyTerm.getNumChildren(); i++) {
      Term child = pKeyTerm.getChild(i);
      if (child.getKind().equals(Kind.VARIABLE)) {
        // Remember if we encountered bound variables
        boundFound = true;
        // Bound vars are extremely volatile in CVC5. Nearly every call to them ends in an
        // exception. Also, we don't want to substitute them with their non bound values.
        argumentInterpretationBuilder.add(child.toString());
      } else {
        argumentInterpretationBuilder.add(evaluateImpl(child));
      }
    }

    // In applied UFs, the child with the name is the 0th child (as it is the declaration)
    String nameStr = pKeyTerm.getChild(0).getSymbol();
    if (nameStr.startsWith("|") && nameStr.endsWith("|")) {
      nameStr = nameStr.substring(1, nameStr.length() - 1);
    }

    Term valueTerm;
    // You can't get a value if there is a bound variable present
    if (!boundFound) {
      valueTerm = solver.getValue(pKeyTerm);
    } else {
      // But you may be able to get one nested in the function itself for some reason
      valueTerm = solver.getValue(pKeyTerm.getChild(0)).getChild(1);
    }

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
  private Iterable<Term> getArgs(Term array) throws CVC5ApiException {
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

  /** Build assignment for an array value. */
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
    if (value.getKind().equals(Kind.STORE)) {
      // This is a Store node for the current index. We need to follow the chain downwards to
      // match this index, while also exploring the successor for the other indices
      Term index = value.getChild(1);
      Term element = value.getChild(2);

      Term select = creator.getEnv().mkTerm(Kind.SELECT, expr, index);

      Iterable<ValueAssignment> current;
      if (expr.getSort().getArrayElementSort().isArray()) {
        // nested array element
        current = buildArrayAssignments(select, element);
      } else {
        // final element
        Term equation = creator.getEnv().mkTerm(Kind.EQUAL, select, element);
        current =
            FluentIterable.of(
                new ValueAssignment(
                    creator.encapsulate(creator.getFormulaType(element), select),
                    creator.encapsulate(creator.getFormulaType(element), element),
                    creator.encapsulateBoolean(equation),
                    getVar(expr),
                    creator.convertValue(element, element),
                    FluentIterable.from(getArgs(select)).transform(this::evaluateImpl).toList()));
      }
      // continue with the next Store in the chain
      return FluentIterable.concat(current, buildArrayAssignments(expr, value.getChild(0))).toList();

    } else if (value.getKind().equals(Kind.CONST_ARRAY)) {
      // We've reached the end of the Store chain
      return ImmutableList.of();

    } else {
      // Should be unreachable
      // We assume that array values are made up of "const" and "store" nodes with non-array
      // constants as leaves
      throw new IllegalArgumentException();
    }
  }

  private List<ValueAssignment> getAssignments(Term pKeyTerm) throws CVC5ApiException {
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    for (int i = 0; i < pKeyTerm.getNumChildren(); i++) {
      argumentInterpretationBuilder.add(evaluateImpl(pKeyTerm.getChild(i)));
    }

    String nameStr;
    if (pKeyTerm.hasSymbol()) {
      nameStr = pKeyTerm.getSymbol();
    } else {
      // Default if there is no name
      nameStr = "UNKNOWN_VARIABLE";
    }

    if (nameStr.startsWith("|") && nameStr.endsWith("|")) {
      nameStr = nameStr.substring(1, nameStr.length() - 1);
    }

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
