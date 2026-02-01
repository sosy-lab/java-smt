// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableListCopy;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import edu.stanford.CVC4.ArrayType;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.SmtEngine;
import edu.stanford.CVC4.Type;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

public class CVC4Model extends AbstractModel<Expr, Type, ExprManager> {

  private final ImmutableList<ValueAssignment> model;
  private final SmtEngine smtEngine;
  private final CVC4TheoremProver prover;

  CVC4Model(
      CVC4TheoremProver pProver,
      CVC4FormulaCreator pCreator,
      SmtEngine pSmtEngine,
      Collection<Expr> pAssertedExpressions) {
    super(pProver, pCreator);
    smtEngine = pSmtEngine;
    prover = pProver;

    // We need to generate and save this at construction time as CVC4 has no functionality to give a
    // persistent reference to the model. If the SMT engine is used somewhere else, the values we
    // get out of it might change!
    model = generateModel(pAssertedExpressions);
  }

  @Override
  public Expr evalImpl(Expr f) {
    // This method looks like a violation of the constraint above: the SMT engine can be changed
    // before querying this method. However, the prover guarantees to close the model before this
    // can happen.
    Preconditions.checkState(!isClosed());
    return getValue(f);
  }

  /** we need to convert the given expression into the current context. */
  private Expr getValue(Expr f) {
    return prover.exportExpr(smtEngine.getValue(prover.importExpr(f)));
  }

  private Set<Expr> collectModelTerms(Collection<Expr> asserted) {
    ImmutableSet.Builder<Expr> builder = ImmutableSet.builder();
    // We wrap Expr in CVC4Formula for the hash() override. Without the override, we end up
    // collecting duplicate terms
    // (This problem has been fixed on CVC5/Bitwula)
    var cache = new HashSet<CVC4Formula>();
    var work = new ArrayDeque<CVC4Formula>();
    work.addAll(transformedImmutableListCopy(asserted, CVC4Formula::new));
    while (!work.isEmpty()) {
      var next = work.pop();
      if (cache.add(next)) {
        var term = next.getTerm();
        var kind = term.getKind();
        if (kind == Kind.VARIABLE) {
          builder.add(term);
        } else {
          if (kind == Kind.APPLY_UF) {
            builder.add(term);
          }
          for (int c = 0; c < term.getNumChildren(); c++) {
            work.push(new CVC4Formula(term.getChild(c)));
          }
        }
      }
    }
    return builder.build();
  }

  private ImmutableList<ValueAssignment> generateModel(Collection<Expr> assertedExpressions) {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    for (Expr expr : collectModelTerms(assertedExpressions)) {
      builder.addAll(getAssignments(expr));
    }
    return builder.build().asList();
  }

  /**
   * Get a single value assignment from an instantiation of the given uninterpreted function.
   *
   * @param pKeyExpr the UF instantiation as "(UF_NAME ARGS...)"
   * @return the value assignment as "(UF_NAME ARGS...) := VALUE"
   */
  private ValueAssignment getAssignmentForUfInstantiation(Expr pKeyExpr) {
    // An uninterpreted function "(UF_NAME ARGS...)" consist of N children,
    // each child is one argument, and the UF itself is the operator of the keyExpr.
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    for (int i = 0; i < pKeyExpr.getNumChildren(); i++) {
      Expr child = pKeyExpr.getChild(i);
      argumentInterpretationBuilder.add(evaluateImpl(child));
    }

    final Expr valueExpr = getValue(pKeyExpr);
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(pKeyExpr),
        creator.encapsulateWithTypeOf(valueExpr),
        creator.encapsulateBoolean(creator.getEnv().mkExpr(Kind.EQUAL, pKeyExpr, valueExpr)),
        CVC4FormulaCreator.getName(pKeyExpr),
        creator.convertValue(pKeyExpr, valueExpr),
        argumentInterpretationBuilder.build());
  }

  /**
   * Takes a (nested) select statement and returns its indices. For example: From "(SELECT (SELECT(
   * SELECT 3 arr) 2) 1)" we return "[1,2,3]"
   */
  private ImmutableList<Expr> getArrayIndices(Expr array) {
    ImmutableList.Builder<Expr> indices = ImmutableList.builder();
    while (array.getKind().equals(Kind.SELECT)) {
      indices.add(array.getChild(1));
      array = array.getChild(0);
    }
    return indices.build().reverse();
  }

  /** Takes a select statement with multiple indices and returns the variable name at the bottom. */
  private String getVar(Expr array) {
    while (array.getKind().equals(Kind.SELECT)) {
      array = array.getChild(0);
    }
    return array.toString();
  }

  /**
   * Build assignment for an array value.
   *
   * @param expr The array term, e.g., a variable
   * @param value The model value term returned by CVC4 for the array, e.g., a Store chain
   * @return A list of value assignments for all elements in the array, including nested arrays
   */
  private List<ValueAssignment> buildArrayAssignments(Expr expr, Expr value) {

    // Iterate down the Store-chain: (Store tail index element)
    List<ValueAssignment> result = new ArrayList<>();
    while (value.getKind().equals(Kind.STORE)) {
      Expr index = value.getChild(1);
      Expr element = value.getChild(2);
      Expr select = creator.getEnv().mkExpr(Kind.SELECT, expr, index);

      // CASE 1: nested array dimension, let's recurse deeper
      if (new ArrayType(expr.getType()).getConstituentType().isArray()) {
        result.addAll(buildArrayAssignments(select, element));

      } else {
        // CASE 2: final element, let's get the assignment and proceed with its sibling
        result.add(
            new ValueAssignment(
                creator.encapsulate(creator.getFormulaType(element), select),
                creator.encapsulate(creator.getFormulaType(element), element),
                creator.encapsulateBoolean(creator.getEnv().mkExpr(Kind.EQUAL, select, element)),
                getVar(expr),
                creator.convertValue(element, element),
                transformedImmutableListCopy(getArrayIndices(select), this::evaluateImpl)));
      }

      // Move to the next Store in the chain
      value = value.getChild(0);
    }

    // End of chain must be CONST_ARRAY.
    checkState(
        value.getKind().equals(Kind.STORE_ALL), "Unexpected array value structure: %s", value);

    return result;
  }

  private List<ValueAssignment> getAssignments(Expr pKeyExpr) {

    // handle UF instantiations
    if (pKeyExpr.getKind() == Kind.APPLY_UF) {
      return ImmutableList.of(getAssignmentForUfInstantiation(pKeyExpr));
    }
    // handle array assignments
    final Expr valueExpr = getValue(pKeyExpr);
    if (valueExpr.getType().isArray()) {
      return buildArrayAssignments(pKeyExpr, valueExpr);
    }

    // handle simple assignments
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    for (int i = 0; i < pKeyExpr.getNumChildren(); i++) {
      argumentInterpretationBuilder.add(evaluateImpl(pKeyExpr.getChild(i)));
    }
    return ImmutableList.of(
        new ValueAssignment(
            creator.encapsulateWithTypeOf(pKeyExpr),
            creator.encapsulateWithTypeOf(valueExpr),
            creator.encapsulateBoolean(creator.getEnv().mkExpr(Kind.EQUAL, pKeyExpr, valueExpr)),
            CVC4FormulaCreator.getName(pKeyExpr),
            creator.convertValue(pKeyExpr, valueExpr),
            argumentInterpretationBuilder.build()));
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return model;
  }
}
