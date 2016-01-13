package org.sosy_lab.solver.basicimpl.tactics;

import static com.google.common.collect.FluentIterable.from;
import static com.google.common.collect.Iterables.concat;
import static java.util.Collections.singletonList;

import com.google.common.base.Predicate;
import com.google.common.collect.FluentIterable;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FuncDecl;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;

import java.util.ArrayList;
import java.util.List;

class CNFVisitor implements BooleanFormulaVisitor<List<BooleanFormula>> {

  private final BooleanFormulaManager bfmgr;
  private final int maxDepth;
  private int currentDepth = 0;

  /**
   * Create a Visitor that creates a CNF (if pMaxDepth is -1) or an approximation
   * of a CNF, that uses a heuristic to decide when to stop creating conjuncts.
   *
   * @param pBfmgr the FormulaManager to use
   * @param pMaxDepth the depth up to which point conjuncts should be created,
   *                  -1 is for infinitely deep
   */
  CNFVisitor(BooleanFormulaManager pBfmgr, int pMaxDepth) {
    bfmgr = pBfmgr;
    maxDepth = pMaxDepth;
  }

  @Override
  public List<BooleanFormula> visitTrue() {
    return singletonList(bfmgr.makeBoolean(true));
  }

  @Override
  public List<BooleanFormula> visitFalse() {
    return singletonList(bfmgr.makeBoolean(false));
  }

  @Override
  public List<BooleanFormula> visitBoundVar(BooleanFormula var, int deBruijnIdx) {
    throw new IllegalStateException("Traversed formula is not in NNF if quantifiers are present");
  }

  @Override
  public List<BooleanFormula> visitAtom(BooleanFormula pAtom, FuncDecl decl) {
    return singletonList(pAtom);
  }

  @Override
  public List<BooleanFormula> visitNot(BooleanFormula pOperand) {
    // the traversed formula is assumed to be in NNF so just return the operand
    return singletonList(bfmgr.not(pOperand));
  }

  private List<List<BooleanFormula>> visitAll(List<BooleanFormula> pOperands) {
    List<List<BooleanFormula>> args = new ArrayList<>(pOperands.size());
    for (BooleanFormula arg : pOperands) {
      args.add(bfmgr.visit(this, arg));
    }
    return args;
  }

  @Override
  public List<BooleanFormula> visitAnd(List<BooleanFormula> pOperands) {
    if (maxDepth >= 0 && currentDepth > maxDepth) {
      return singletonList(bfmgr.and(pOperands));
    }

    currentDepth++;
    FluentIterable<BooleanFormula> operands = from(concat(visitAll(pOperands)));

    // if any of the operands of a conjunction is false we can replace the
    // whole conjunction with FALSE, TODO should we do that or do we want to
    // have the whole formula?
    if (operands.anyMatch(
        new Predicate<BooleanFormula>() {
          @Override
          public boolean apply(BooleanFormula pInput) {
            return bfmgr.isFalse(pInput);
          }
        })) {
      return singletonList(bfmgr.makeBoolean(false));
    }

    currentDepth--;
    return operands.toList();
  }

  @Override
  public List<BooleanFormula> visitOr(List<BooleanFormula> pOperands) {
    if (maxDepth >= 0 && currentDepth > maxDepth) {
      return singletonList(bfmgr.or(pOperands));
    }

    currentDepth++;
    FluentIterable<List<BooleanFormula>> operands = from(visitAll(pOperands));

    List<BooleanFormula> newConjuncts = new ArrayList<>();
    for (List<BooleanFormula> op : operands) {
      // first iteration
      if (newConjuncts.isEmpty()) {
        newConjuncts.addAll(op);

      } else {
        List<BooleanFormula> tmpConjuncts = new ArrayList<>();
        for (BooleanFormula nextF : op) {
          for (BooleanFormula oldF : newConjuncts) {
            tmpConjuncts.add(bfmgr.or(nextF, oldF));
          }
        }
        newConjuncts = tmpConjuncts;
      }
    }
    currentDepth--;

    return newConjuncts;
  }

  @Override
  public List<BooleanFormula> visitXor(BooleanFormula operand1, BooleanFormula operand2) {
    throw new IllegalStateException("Traversed formula is not in NNF if XOR is present");
  }

  @Override
  public List<BooleanFormula> visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    throw new IllegalStateException("Traversed formula is not in NNF if equivalence is present");
  }

  @Override
  public List<BooleanFormula> visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    throw new IllegalStateException("Traversed formula is not in NNF if implication is present");
  }

  @Override
  public List<BooleanFormula> visitIfThenElse(
      BooleanFormula pCondition,
      BooleanFormula pThtmpConjunctsenFormula,
      BooleanFormula pElseFormula) {
    // the traversed formula is assumed to be in NNF without ITEs
    // so we can throw an exception here
    throw new IllegalStateException("Traversed formula is not in NNF without ITEs");
  }

  @Override
  public List<BooleanFormula> visitQuantifier(
      Quantifier quantifier, List<Formula> boundVars, BooleanFormula pBody) {
    throw new IllegalStateException("Traversed formula is not in NNF if quantifiers are present");
  }
}
