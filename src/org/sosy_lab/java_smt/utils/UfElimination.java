// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.utils;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.Maps.difference;

import com.google.auto.value.AutoValue;
import com.google.common.base.Verify;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableListMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Streams;
import com.google.errorprone.annotations.CheckReturnValue;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicBoolean;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

/**
 * UfElimination replaces UFs by fresh variables and adds constraints to enforce the functional
 * consistency.
 */
public class UfElimination {

  public static class Result {

    private final BooleanFormula formula;
    private final BooleanFormula constraints;
    private final ImmutableMap<Formula, Formula> substitutions;
    private final ImmutableMultimap<FunctionDeclaration<?>, UninterpretedFunctionApplication> ufs;

    public static Result empty(FormulaManager pFormulaManager) {
      BooleanFormula trueFormula = pFormulaManager.getBooleanFormulaManager().makeTrue();
      return new Result(trueFormula, trueFormula, ImmutableMap.of(), ImmutableListMultimap.of());
    }

    Result(
        BooleanFormula pFormula,
        BooleanFormula pConstraints,
        ImmutableMap<Formula, Formula> pSubstitutions,
        ImmutableMultimap<FunctionDeclaration<?>, UninterpretedFunctionApplication> pUfs) {
      formula = checkNotNull(pFormula);
      constraints = checkNotNull(pConstraints);
      substitutions = checkNotNull(pSubstitutions);
      ufs = checkNotNull(pUfs);
    }

    /**
     * @return the new {@link Formula} without UFs
     */
    public BooleanFormula getFormula() {
      return formula;
    }

    /**
     * @return the constraints enforcing the functional consistency.
     */
    public BooleanFormula getConstraints() {
      return constraints;
    }

    /**
     * @return the substitution used to replace UFs
     */
    public Map<Formula, Formula> getSubstitution() {
      return substitutions;
    }

    /**
     * @return all eliminated application of Ufs
     */
    Multimap<FunctionDeclaration<?>, UninterpretedFunctionApplication> getUfs() {
      return ufs;
    }
  }

  private static final UniqueIdGenerator UNIQUE_ID_GENERATOR = new UniqueIdGenerator();

  private static final String prefix = "__UF_fresh_";

  private final BooleanFormulaManager bfmgr;
  private final FormulaManager fmgr;

  UfElimination(FormulaManager pFmgr) {
    bfmgr = pFmgr.getBooleanFormulaManager();
    fmgr = pFmgr;
  }

  /**
   * Applies the Ackermann transformation to the given {@link Formula}. Quantified formulas are not
   * supported.
   *
   * @param f the {@link Formula} to remove all Ufs from
   * @return the new {@link Formula} and the substitution done during transformation
   */
  public BooleanFormula eliminateUfs(BooleanFormula f) {
    Result result = eliminateUfs(f, Result.empty(fmgr));
    return fmgr.getBooleanFormulaManager().and(result.getFormula(), result.getConstraints());
  }

  /**
   * Applies the Ackermann transformation to the given {@link Formula} with respect to the {@link
   * Result} of another formula. Quantified formulas are not supported.
   *
   * @param pF the {@link Formula} to remove all Ufs from
   * @param pOtherResult result of eliminating Ufs in another {@link BooleanFormula}
   * @return the {@link Result} of the Ackermannization
   */
  public Result eliminateUfs(BooleanFormula pF, Result pOtherResult) {
    checkArgument(!isQuantified(pF));
    BooleanFormula f;
    if (!pOtherResult.getSubstitution().isEmpty()) {
      f = fmgr.substitute(pF, pOtherResult.getSubstitution());
    } else {
      f = pF;
    }

    int depth = getNestingDepthOfUfs(f);
    Multimap<FunctionDeclaration<?>, UninterpretedFunctionApplication> ufs = findUFs(f);
    merge(ufs, pOtherResult);

    ImmutableMap.Builder<Formula, Formula> substitutionsBuilder = ImmutableMap.builder();
    List<BooleanFormula> extraConstraints = new ArrayList<>();

    for (FunctionDeclaration<?> function : ufs.keySet()) {
      List<UninterpretedFunctionApplication> applications = new ArrayList<>(ufs.get(function));
      for (int idx1 = 0; idx1 < applications.size(); idx1++) {
        UninterpretedFunctionApplication application = applications.get(idx1);

        Formula uf = application.getFormula();
        List<Formula> args = application.getArguments();

        Formula substitution = application.getSubstitution();
        substitutionsBuilder.put(uf, substitution);

        for (int idx2 = idx1 + 1; idx2 < applications.size(); idx2++) {
          UninterpretedFunctionApplication application2 = applications.get(idx2);
          List<Formula> otherArgs = application2.getArguments();

          /*
           * Add constraints to enforce functional consistency.
           */
          Verify.verify(args.size() == otherArgs.size());
          BooleanFormula argumentsEquality =
              Streams.zip(args.stream(), otherArgs.stream(), this::makeEqual)
                  .collect(bfmgr.toConjunction());

          BooleanFormula functionEquality = makeEqual(substitution, application2.getSubstitution());
          extraConstraints.add(bfmgr.implication(argumentsEquality, functionEquality));
        }
      }
    }

    // Get rid of UFs.
    ImmutableMap<Formula, Formula> substitutions = substitutionsBuilder.buildOrThrow();
    BooleanFormula formulaWithoutUFs = fmgr.substitute(f, substitutions);

    // substitute all UFs in the additional constraints,
    // required if UFs are arguments of UFs, e.g. uf(uf(1, 2), 2)
    for (int i = 0; i < depth; i++) {
      extraConstraints.replaceAll(c -> fmgr.substitute(c, substitutions));
    }

    Map<Formula, Formula> otherSubstitution =
        difference(pOtherResult.getSubstitution(), substitutions).entriesOnlyOnLeft();
    substitutionsBuilder.putAll(otherSubstitution);
    ImmutableMap<Formula, Formula> allSubstitutions = substitutionsBuilder.buildOrThrow();
    BooleanFormula constraints = bfmgr.and(extraConstraints);
    return new Result(
        formulaWithoutUFs, constraints, allSubstitutions, ImmutableListMultimap.copyOf(ufs));
  }

  private void merge(
      Multimap<FunctionDeclaration<?>, UninterpretedFunctionApplication> pUfs,
      Result pPreviousResult) {
    for (Map.Entry<FunctionDeclaration<?>, UninterpretedFunctionApplication> ufInOtherFormula :
        pPreviousResult.getUfs().entries()) {
      if (pUfs.containsKey(ufInOtherFormula.getKey())) {
        pUfs.put(ufInOtherFormula.getKey(), ufInOtherFormula.getValue());
      }
    }
  }

  @SuppressWarnings("unchecked")
  @CheckReturnValue
  private BooleanFormula makeEqual(Formula pLhs, Formula pRhs) {
    BooleanFormula t;
    if (pLhs instanceof BooleanFormula && pRhs instanceof BooleanFormula) {
      t = bfmgr.equivalence((BooleanFormula) pLhs, (BooleanFormula) pRhs);
    } else if (pLhs instanceof IntegerFormula && pRhs instanceof IntegerFormula) {
      t = fmgr.getIntegerFormulaManager().equal((IntegerFormula) pLhs, (IntegerFormula) pRhs);
    } else if (pLhs instanceof StringFormula && pRhs instanceof StringFormula) {
      t = fmgr.getStringFormulaManager().equal((StringFormula) pLhs, (StringFormula) pRhs);
    } else if (pLhs instanceof NumeralFormula && pRhs instanceof NumeralFormula) {
      t = fmgr.getRationalFormulaManager().equal((NumeralFormula) pLhs, (NumeralFormula) pRhs);
    } else if (pLhs instanceof BitvectorFormula) {
      t = fmgr.getBitvectorFormulaManager().equal((BitvectorFormula) pLhs, (BitvectorFormula) pRhs);
    } else if (pLhs instanceof FloatingPointFormula && pRhs instanceof FloatingPointFormula) {
      FloatingPointFormulaManager fpfmgr = fmgr.getFloatingPointFormulaManager();
      t = fpfmgr.equalWithFPSemantics((FloatingPointFormula) pLhs, (FloatingPointFormula) pRhs);
    } else if (pLhs instanceof ArrayFormula<?, ?> && pRhs instanceof ArrayFormula<?, ?>) {
      ArrayFormula<?, ?> lhs = (ArrayFormula<?, ?>) pLhs;
      @SuppressWarnings("rawtypes")
      ArrayFormula rhs = (ArrayFormula) pRhs;
      t = fmgr.getArrayFormulaManager().equivalence(lhs, rhs);
    } else {
      throw new IllegalArgumentException("Not supported interface");
    }

    return t;
  }

  private boolean isQuantified(Formula f) {
    AtomicBoolean result = new AtomicBoolean();
    fmgr.visitRecursively(
        f,
        new DefaultFormulaVisitor<>() {

          @Override
          protected TraversalProcess visitDefault(Formula pF) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitQuantifier(
              BooleanFormula pF,
              Quantifier pQ,
              List<Formula> pBoundVariables,
              BooleanFormula pBody) {
            result.set(true);
            return TraversalProcess.ABORT;
          }
        });

    return result.get();
  }

  private int getNestingDepthOfUfs(Formula pFormula) {
    return fmgr.visit(
        pFormula,
        new DefaultFormulaVisitor<>() {

          @Override
          protected Integer visitDefault(Formula pF) {
            return 0;
          }

          @Override
          public Integer visitFunction(
              Formula pF, List<Formula> pArgs, FunctionDeclaration<?> pFunctionDeclaration) {
            int depthOfArgs = pArgs.stream().mapToInt(f -> fmgr.visit(f, this)).max().orElse(0);

            // count only UFs
            if (pFunctionDeclaration.getKind() == FunctionDeclarationKind.UF) {
              return depthOfArgs + 1;
            } else {
              return depthOfArgs;
            }
          }

          @Override
          public Integer visitQuantifier(
              BooleanFormula pF,
              Quantifier pQ,
              List<Formula> pBoundVariables,
              BooleanFormula pBody) {
            return fmgr.visit(pBody, this);
          }
        });
  }

  private Multimap<FunctionDeclaration<?>, UninterpretedFunctionApplication> findUFs(
      Formula pFormula) {
    Multimap<FunctionDeclaration<?>, UninterpretedFunctionApplication> ufs = HashMultimap.create();

    fmgr.visitRecursively(
        pFormula,
        new DefaultFormulaVisitor<>() {

          @Override
          protected TraversalProcess visitDefault(Formula f) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitFunction(
              Formula f, List<Formula> args, FunctionDeclaration<?> decl) {
            if (decl.getKind() == FunctionDeclarationKind.UF) {
              Formula substitution = freshUfReplaceVariable(decl.getType());
              ufs.put(decl, UninterpretedFunctionApplication.create(f, args, substitution));
            }
            return TraversalProcess.CONTINUE;
          }
        });

    return ufs;
  }

  private Formula freshUfReplaceVariable(FormulaType<?> pType) {
    return fmgr.makeVariable(pType, prefix + UNIQUE_ID_GENERATOR.getFreshId());
  }

  @AutoValue
  abstract static class UninterpretedFunctionApplication {

    static UninterpretedFunctionApplication create(
        Formula pF, List<Formula> pArguments, Formula pSubstitution) {
      return new AutoValue_UfElimination_UninterpretedFunctionApplication(
          pF, ImmutableList.copyOf(pArguments), pSubstitution);
    }

    abstract Formula getFormula();

    abstract ImmutableList<Formula> getArguments();

    abstract Formula getSubstitution();
  }
}
