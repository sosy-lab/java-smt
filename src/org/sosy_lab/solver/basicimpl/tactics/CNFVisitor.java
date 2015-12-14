package org.sosy_lab.solver.basicimpl.tactics;

import static com.google.common.collect.FluentIterable.from;

import com.google.common.base.Function;
import com.google.common.base.Predicate;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.Maps;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.visitors.BooleanFormulaTransformationVisitor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import javax.annotation.Nonnull;

class CNFVisitor extends BooleanFormulaTransformationVisitor {

  private final BooleanFormulaManager bfmgr;
  private final Set<BooleanFormula> lastConjuncts = new HashSet<>();

  CNFVisitor(FormulaManager pFmgr) {
    super(pFmgr, Maps.<BooleanFormula, BooleanFormula>newHashMap());
    bfmgr = pFmgr.getBooleanFormulaManager();
  }

  @Override
  public BooleanFormula visitTrue() {
    return bfmgr.makeBoolean(true);
  }

  @Override
  public BooleanFormula visitFalse() {
    return bfmgr.makeBoolean(false);
  }

  @Override
  public BooleanFormula visitAtom(BooleanFormula pAtom) {
    return pAtom;
  }

  @Override
  public BooleanFormula visitNot(BooleanFormula pOperand) {
    // the traversed formula is assumed to be in NNF so just return the operand
    return bfmgr.not(pOperand);
  }

  @Override
  public BooleanFormula visitAnd(List<BooleanFormula> pOperands) {
    FluentIterable<BooleanFormula> operands = from(visitIfNotSeen(pOperands));

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
      lastConjuncts.clear();
      return bfmgr.makeBoolean(false);
    }

    lastConjuncts.addAll(operands.toList());

    return bfmgr.and(lastConjuncts);
  }

  @Override
  public BooleanFormula visitOr(List<BooleanFormula> pOperands) {
    // previous content is interesting after this method but not in here
    // so we save it for later use
    Set<BooleanFormula> lastConjunctsSaved = new HashSet<>(lastConjuncts);
    lastConjuncts.clear();

    List<OperandWithConjuncts> operands = new ArrayList<>();
    for (BooleanFormula f : pOperands) {
      BooleanFormula conv = visitIfNotSeen(f);
      operands.add(new OperandWithConjuncts(conv, new HashSet<>(lastConjuncts)));
      lastConjuncts.clear();
    }

    List<BooleanFormula> newConjuncts = new ArrayList<>();
    for (OperandWithConjuncts op : operands) {
      // first iteration
      if (newConjuncts.isEmpty()) {
        if (op.conjuncts.isEmpty()) {
          newConjuncts.add(op.operand);
        } else {
          newConjuncts.addAll(op.conjuncts);
        }

      } else {

        List<BooleanFormula> tmpConjuncts = new ArrayList<>();
        for (BooleanFormula nextF : op.conjunctsOrOperand()) {
          for (BooleanFormula oldF : newConjuncts) {
            tmpConjuncts.add(bfmgr.or(nextF, oldF));
          }
        }
        newConjuncts = tmpConjuncts;
      }
    }

    lastConjuncts.addAll(lastConjunctsSaved);
    lastConjuncts.addAll(newConjuncts);

    return bfmgr.and(lastConjuncts);
  }

  @Override
  public BooleanFormula visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    // the traversed formula is assumed to be in NNF without equivalences
    // so we can throw an exception here
    throw new IllegalStateException("Traversed formula is not in NNF without equivalences");
  }

  @Override
  public BooleanFormula visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    // the traversed formula is assumed to be in NNF without implications
    // so we can throw an exception here
    throw new IllegalStateException("Traversed formula is not in NNF without implications");
  }

  @Override
  public BooleanFormula visitIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    // the traversed formula is assumed to be in NNF without ITEs
    // so we can throw an exception here
    throw new IllegalStateException("Traversed formula is not in NNF without ITEs");
  }

  static class OperandWithConjuncts {
    private BooleanFormula operand;
    private Set<BooleanFormula> conjuncts;

    private OperandWithConjuncts(BooleanFormula op, Set<BooleanFormula> conj) {
      operand = op;
      conjuncts = conj;
    }

    public Set<BooleanFormula> conjunctsOrOperand() {
      if (conjuncts.isEmpty()) {
        return Collections.singleton(operand);
      } else {
        return conjuncts;
      }
    }

    public static final Predicate<Set<BooleanFormula>> IS_EMPTY =
        new Predicate<Set<BooleanFormula>>() {
          @Override
          public boolean apply(@Nonnull Set<BooleanFormula> pInput) {
            return pInput.isEmpty();
          }
        };

    public static final Function<OperandWithConjuncts, BooleanFormula> GET_OPERAND =
        new Function<OperandWithConjuncts, BooleanFormula>() {
          @Override
          public BooleanFormula apply(@Nonnull OperandWithConjuncts pInput) {
            return pInput.operand;
          }
        };

    public static final Function<OperandWithConjuncts, Set<BooleanFormula>> GET_CONJUNCTS =
        new Function<OperandWithConjuncts, Set<BooleanFormula>>() {
          @Override
          public Set<BooleanFormula> apply(@Nonnull OperandWithConjuncts pInput) {
            return pInput.conjuncts;
          }
        };
  }
}
