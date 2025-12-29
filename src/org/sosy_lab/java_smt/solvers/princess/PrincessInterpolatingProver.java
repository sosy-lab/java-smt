// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static scala.collection.JavaConverters.asJava;
import static scala.collection.JavaConverters.asScala;

import ap.api.SimpleAPI;
import ap.basetypes.IdealInt;
import ap.basetypes.Tree;
import ap.parser.BooleanCompactifier;
import ap.parser.IBoolLit;
import ap.parser.IEquation;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IIntFormula;
import ap.parser.IIntLit;
import ap.parser.IIntRelation;
import ap.parser.IPlus;
import ap.parser.ISortedQuantified;
import ap.parser.ISortedVariable;
import ap.parser.ITimes;
import ap.parser.PartialEvaluator;
import ap.parser.Rewriter;
import ap.theories.bitvectors.ModuloArithmetic;
import ap.types.Sort;
import ap.types.Sort.Integer$;
import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;
import com.google.common.graph.Traverser;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import scala.collection.Seq;
import scala.collection.mutable.ArrayBuffer;

class PrincessInterpolatingProver extends PrincessAbstractProver<Integer>
    implements InterpolatingProverEnvironment<Integer> {

  PrincessInterpolatingProver(
      PrincessFormulaManager pMgr,
      PrincessFormulaCreator creator,
      SimpleAPI pApi,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions) {
    super(pMgr, creator, pApi, pShutdownNotifier, pOptions);
  }

  @Override
  protected Integer addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    return addConstraint0(constraint);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Integer> pTermNamesOfA) throws SolverException {
    checkGenerateInterpolants();
    checkArgument(
        getAssertedConstraintIds().containsAll(pTermNamesOfA),
        "interpolation can only be done over previously asserted formulas.");

    Set<Integer> indexesOfA = ImmutableSet.copyOf(pTermNamesOfA);

    // calc difference: termNamesOfB := assertedFormulas - termNamesOfA
    Set<Integer> indexesOfB = Sets.difference(partitions.peek().keySet(), indexesOfA);

    // get interpolant of groups
    List<BooleanFormula> itp = getSeqInterpolants(ImmutableList.of(indexesOfA, indexesOfB));
    assert itp.size() == 1; // 2 groups -> 1 interpolant

    return itp.get(0);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      final List<? extends Collection<Integer>> pPartitions) throws SolverException {
    checkGenerateInterpolants();
    Preconditions.checkArgument(
        !pPartitions.isEmpty(), "at least one partition should be available.");
    final ImmutableSet<Integer> assertedConstraintIds = getAssertedConstraintIds();
    checkArgument(
        pPartitions.stream().allMatch(assertedConstraintIds::containsAll),
        "interpolation can only be done over previously asserted formulas.");

    // convert to needed data-structure
    final ArrayBuffer<scala.collection.immutable.Set<Object>> args = new ArrayBuffer<>();
    for (Collection<Integer> partition : pPartitions) {
      args.$plus$eq(asScala(partition).toSet());
    }

    // do the hard work
    Seq<IFormula> itps;
    try {
      itps = api.getInterpolants(args.toSeq(), api.getInterpolants$default$2());
    } catch (StackOverflowError e) {
      // Princess is recursive and thus produces stack overflows on large formulas.
      // Princess itself also catches StackOverflowError and returns "OutOfMemory" in checkSat(),
      // so we can do the same for getInterpolants().
      throw new SolverException(
          "Princess ran out of stack memory, try increasing the stack size.", e);
    } catch (NullPointerException npe) {
      try {
        checkState(isUnsat(), "Illegal solver state");
        itps = api.getInterpolants(args.toSeq(), api.getInterpolants$default$2());
      } catch (InterruptedException ie) {
        Thread.currentThread().interrupt();
        throw new SolverException("Thread was interrupted", ie);
      } catch (StackOverflowError e) {
        throw new SolverException(
            "Princess ran out of stack memory, try increasing the stack size.", e);
      }
    }

    assert itps.length() == pPartitions.size() - 1
        : "There should be (n-1) interpolants for n partitions";

    // convert data-structure back
    final List<BooleanFormula> result = new ArrayList<>();
    for (final IFormula itp : asJava(itps)) {
      var simplified = PartialEvaluator.apply(BooleanCompactifier.apply(itp));
      var unsigned =
          Rewriter.rewrite(
              simplified,
              term -> {
                if (term instanceof IFunApp) {
                  // Rewrite casts to signed bitvectors as casts to unsigned bitvectors
                  var app = (IFunApp) term;
                  if (app.fun().name().equals("mod_cast")) {
                    var par1 = (IIntLit) app.apply(0);
                    var par2 = (IIntLit) app.apply(1);
                    if (par1.value().$less(IdealInt.ZERO())) {
                      var diff = par2.value().$minus(par1.value());
                      return new IFunApp(
                          app.fun(),
                          PrincessEnvironment.toITermSeq(
                              IExpression.i(0), IExpression.i(diff), app.apply(2)));
                    }
                  }
                }
                return term;
              });
      var quantifiedVariableFix =
          Rewriter.rewrite(
              unsigned,
              term -> {
                // Rewrite quantifiers with missing variable sorts
                if (term instanceof ISortedQuantified) {
                  var quantified = (ISortedQuantified) term;
                  if (quantified.sort().name().equals("any")) {
                    return new ISortedQuantified(
                        quantified.quan(), Integer$.MODULE$, quantified.subformula());
                  }
                }
                if (term instanceof ISortedVariable) {
                  var variable = (ISortedVariable) term;
                  if (variable.sort().name().equals("any")) {
                    return new ISortedVariable(variable.index(), Integer$.MODULE$);
                  }
                }
                return term;
              });
      var selectBugFixed =
          Rewriter.rewrite(
              quantifiedVariableFix,
              term -> {
                // Add missing conversions for select(arr, idx) if the arrays maps to bitvectors
                if (term instanceof ITimes) {
                  var times = (ITimes) term;
                  if (!PrincessEnvironment.getFormulaType(times.subterm()).isIntegerType()) {
                    return new ITimes(times.coeff(), ModuloArithmetic.cast2Int(times.subterm()));
                  }
                }
                if (term instanceof IPlus) {
                  var plus = (IPlus) term;
                  var t1 = plus.t1();
                  if (!PrincessEnvironment.getFormulaType(t1).isIntegerType()) {
                    t1 = ModuloArithmetic.cast2Int(t1);
                  }
                  var t2 = plus.t2();
                  if (!PrincessEnvironment.getFormulaType(t2).isIntegerType()) {
                    t2 = ModuloArithmetic.cast2Int(t2);
                  }
                  if (t1 != plus.t1() || t2 != plus.t2()) {
                    return new IPlus(t1, t2);
                  }
                }
                if (term instanceof IEquation) {
                  var eq = (IEquation) term;
                  var sort1 = Sort.sortOf(eq.left());
                  var sort2 = Sort.sortOf(eq.right());
                  if (sort1.equals(Integer$.MODULE$) && !sort2.equals(Integer$.MODULE$)) {
                    return new IEquation(eq.left(), ModuloArithmetic.cast2Int(eq.right()));
                  }
                  if (!sort1.equals(Integer$.MODULE$) && sort2.equals(Integer$.MODULE$)) {
                    return new IEquation(ModuloArithmetic.cast2Int(eq.left()), eq.right());
                  }
                }
                if (term instanceof IIntFormula) {
                  var formula = (IIntFormula) term;
                  if (formula.rel().equals(IIntRelation.GeqZero())
                      || formula.rel().equals(IIntRelation.EqZero())) {
                    if (!Sort.sortOf(formula.t()).equals(Integer$.MODULE$)) {
                      return new IIntFormula(formula.rel(), ModuloArithmetic.cast2Int(formula.t()));
                    }
                  }
                }
                return term;
              });
      var eqZero =
          Rewriter.rewrite(
              selectBugFixed,
              term -> {
                // Rewrite (= term 0) as (=0 term)
                if (term instanceof IEquation) {
                  var equation = (IEquation) term;
                  if (equation.right() instanceof IIntLit
                      && ((IIntLit) equation.right()).value().isZero()) {
                    return IExpression.eqZero(equation.left());
                  }
                }
                return term;
              });
      result.add(mgr.encapsulateBooleanFormula(eqZero));
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException {
    checkGenerateInterpolants();
    final ImmutableSet<Integer> assertedConstraintIds = getAssertedConstraintIds();
    checkArgument(
        partitionedFormulas.stream().allMatch(assertedConstraintIds::containsAll),
        "interpolation can only be done over previously asserted formulas.");
    assert InterpolatingProverEnvironment.checkTreeStructure(
        partitionedFormulas.size(), startOfSubTree);

    // reconstruct the trees from the labels in post-order
    final Deque<Tree<scala.collection.immutable.Set<Object>>> stack = new ArrayDeque<>();
    final Deque<Integer> subtreeStarts = new ArrayDeque<>();

    for (int i = 0; i < partitionedFormulas.size(); ++i) {
      Preconditions.checkState(stack.size() == subtreeStarts.size());
      int start = startOfSubTree[i];
      ArrayBuffer<Tree<scala.collection.immutable.Set<Object>>> children = new ArrayBuffer<>();
      // while-loop: inner node -> merge children
      // otherwise:  leaf-node  -> start new subtree, no children
      while (!subtreeStarts.isEmpty() && start <= subtreeStarts.peek()) {
        subtreeStarts.pop();
        children.$plus$eq$colon(stack.pop()); // prepend
      }
      subtreeStarts.push(start);
      stack.push(new Tree<>(asScala(partitionedFormulas.get(i)).toSet(), children.toList()));
    }

    Preconditions.checkState(subtreeStarts.peek() == 0, "subtree of root should start at 0.");
    Tree<scala.collection.immutable.Set<Object>> root = stack.pop();
    Preconditions.checkState(stack.isEmpty(), "root should be last element in stack.");

    final Tree<IFormula> itps;
    try {
      itps = api.getTreeInterpolant(root, api.getTreeInterpolant$default$2());
    } catch (StackOverflowError e) {
      // Princess is recursive and thus produces stack overflows on large formulas.
      // Princess itself also catches StackOverflowError and returns "OutOfMemory" in checkSat(),
      // so we can do the same for getInterpolants().
      throw new SolverException(
          "Princess ran out of stack memory, try increasing the stack size.", e);
    }

    List<BooleanFormula> result = tree2List(itps);
    assert result.size() == startOfSubTree.length - 1;
    return result;
  }

  /** returns a post-order iteration of the tree. */
  private List<BooleanFormula> tree2List(Tree<IFormula> tree) {
    List<BooleanFormula> lst =
        FluentIterable.from(
                Traverser.<Tree<IFormula>>forTree(node -> asJava(node.children()))
                    .depthFirstPostOrder(tree))
            .transform(node -> mgr.encapsulateBooleanFormula(node.d()))
            .toList();
    // root of interpolation tree is false, and we have to remove it.
    assert Iterables.getLast(lst).equals(mgr.encapsulateBooleanFormula(new IBoolLit(false)));
    return lst.subList(0, lst.size() - 1);
  }
}
