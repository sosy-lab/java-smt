/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3;


import com.microsoft.z3.Native;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_sort_kind;
import java.util.HashMap;
import java.util.Map;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.Formula;

public class Z3ProofParser {
  private final long z3context;
  private final long z3solver;
  private final Z3FormulaCreator formulaCreator;
  private final Z3AbstractProver prover;
  private final Map<Long, Z3ProofNode> parsed = new HashMap<>();


  Z3ProofParser(
      long ctx, long solver, Z3FormulaCreator creator,
      Z3AbstractProver pProver) {
    z3context = ctx;
    z3solver = solver;
    formulaCreator = creator;
    prover = pProver;
  }

  Z3ProofNode fromAST(long proof) {
    if (parsed.containsKey(proof)) {
      return parsed.get(proof);
    }

    Native.incRef(z3context, proof);
    long sort = Native.getSort(z3context, proof);
    long sortKind = Native.getSortKind(z3context, sort);
    int declKind = Native.getDeclKind(z3context,
        Native.getAppDecl(z3context, proof));
    int numArgs = Native.getAppNumArgs(z3context, proof);
    Z3_sort_kind sort_kind = Z3_sort_kind.fromInt((int) sortKind);
    Formula formula;
    Z3ProofRule proofRule;

    if (sort_kind != Z3_sort_kind.Z3_UNKNOWN_SORT) {
      formula = generateFormula(proof);
    } else {

      long z3expr = Native.getAppArg(z3context, proof, numArgs - 1);
      formula = generateFormula(z3expr);
    }
    proofRule = getPRfromDK(declKind);
    Z3ProofNode proofNode = new Z3ProofNode(formula, proofRule);
    parsed.put(proof, proofNode);

    for (int i = 0; i < numArgs - 1; i++) {
      long arg = Native.getAppArg(z3context, proof, i);
      proofNode.addChild(fromAST(arg));
    }
    Native.decRef(z3context, proof);
    return proofNode;
  }

  private Z3ProofRule getPRfromDK(int declKind) {
    Z3_decl_kind dk = Z3_decl_kind.fromInt(declKind);
    switch (dk) {
      case Z3_OP_PR_UNDEF:
        return Z3ProofRule.UNDEF;

      case Z3_OP_PR_TRUE:
        return Z3ProofRule.TRUE;

      case Z3_OP_PR_ASSERTED:
        return Z3ProofRule.ASSERTED;

      case Z3_OP_PR_GOAL:
        return Z3ProofRule.GOAL;

      case Z3_OP_PR_MODUS_PONENS:
        return Z3ProofRule.MODUS_PONENS;

      case Z3_OP_PR_REFLEXIVITY:
        return Z3ProofRule.REFLEXIVITY;

      case Z3_OP_PR_SYMMETRY:
        return Z3ProofRule.SYMMETRY;

      case Z3_OP_PR_TRANSITIVITY:
        return Z3ProofRule.TRANSITIVITY;

      case Z3_OP_PR_TRANSITIVITY_STAR:
        return Z3ProofRule.TRANSITIVITY_STAR;
      case Z3_OP_PR_MONOTONICITY:
        return Z3ProofRule.MONOTONICITY;
      case Z3_OP_PR_QUANT_INTRO:
        return Z3ProofRule.QUANT_INTRO;
      case Z3_OP_PR_BIND:
        return Z3ProofRule.BIND;
      case Z3_OP_PR_DISTRIBUTIVITY:
        return Z3ProofRule.DISTRIBUTIVITY;
      case Z3_OP_PR_AND_ELIM:
        return Z3ProofRule.AND_ELIM;
      case Z3_OP_PR_NOT_OR_ELIM:
        return Z3ProofRule.NOT_OR_ELIM;
      case Z3_OP_PR_REWRITE:
        return Z3ProofRule.REWRITE;
      case Z3_OP_PR_REWRITE_STAR:
        return Z3ProofRule.REWRITE_STAR;
      case Z3_OP_PR_PULL_QUANT:
        return Z3ProofRule.PULL_QUANT;
      case Z3_OP_PR_PUSH_QUANT:
        return Z3ProofRule.PUSH_QUANT;
      case Z3_OP_PR_ELIM_UNUSED_VARS:
        return Z3ProofRule.ELIM_UNUSED_VARS;
      case Z3_OP_PR_DER:
        return Z3ProofRule.DER;
      case Z3_OP_PR_QUANT_INST:
        return Z3ProofRule.QUANT_INST;
      case Z3_OP_PR_HYPOTHESIS:
        return Z3ProofRule.HYPOTHESIS;
      case Z3_OP_PR_LEMMA:
        return Z3ProofRule.LEMMA;
      case Z3_OP_PR_UNIT_RESOLUTION:
        return Z3ProofRule.UNIT_RESOLUTION;
      case Z3_OP_PR_IFF_TRUE:
        return Z3ProofRule.IFF_TRUE;
      case Z3_OP_PR_IFF_FALSE:
        return Z3ProofRule.IFF_FALSE;
      case Z3_OP_PR_COMMUTATIVITY:
        return Z3ProofRule.COMMUTATIVITY;
      case Z3_OP_PR_DEF_AXIOM:
        return Z3ProofRule.DEF_AXIOM;
      case Z3_OP_PR_ASSUMPTION_ADD:
        return Z3ProofRule.ASSUMPTION_ADD;
      case Z3_OP_PR_LEMMA_ADD:
        return Z3ProofRule.LEMMA_ADD;
      case Z3_OP_PR_REDUNDANT_DEL:
        return Z3ProofRule.REDUNDANT_DEL;
      case Z3_OP_PR_CLAUSE_TRAIL:
        return Z3ProofRule.CLAUSE_TRAIL;
      case Z3_OP_PR_DEF_INTRO:
        return Z3ProofRule.DEF_INTRO;
      case Z3_OP_PR_APPLY_DEF:
        return Z3ProofRule.APPLY_DEF;
      case Z3_OP_PR_IFF_OEQ:
        return Z3ProofRule.IFF_OEQ;
      case Z3_OP_PR_NNF_POS:
        return Z3ProofRule.NNF_POS;
      case Z3_OP_PR_NNF_NEG:
        return Z3ProofRule.NNF_NEG;
      case Z3_OP_PR_SKOLEMIZE:
        return Z3ProofRule.SKOLEMIZE;
      case Z3_OP_PR_MODUS_PONENS_OEQ:
        return Z3ProofRule.MODUS_PONENS_OEQ;
      case Z3_OP_PR_TH_LEMMA:
        return Z3ProofRule.TH_LEMMA;
      case Z3_OP_PR_HYPER_RESOLVE:
        return Z3ProofRule.HYPER_RESOLVE;
      default:
        return Z3ProofRule.OPERATION;
    }
  }

  //@Nullable
  //private Formula getFromStoredConstraints(long proof) {
  //  String varName = Native.astToString(z3context, proof);
  //  if (prover.getStoredConstraints().peek().containsKey(varName)) {
  //    return prover.getStoredConstraints().peek().get(varName);
  //  } else {
  //   return null;
  // }
  // }

  private Formula generateFormula(long proof) {
    Formula formula = null;
    //Formula formula = getFromStoredConstraints(proof);
    if (formula == null) {
      formula = formulaCreator.encapsulate(formulaCreator.getFormulaType(proof), proof);
    }
    return formula;
  }
}


