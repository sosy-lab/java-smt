/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.api.proofs;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5ProofRule;
//import org.sosy_lab.java_smt.solvers.z3.Z3ProofRule;

/**
 * Registry for proof rules. This class is used to register and retrieve proof rules by their name.
 * It checks for the solver that called to retrieve the according rule.
 */
 class ProofRuleRegistry {
   /*
  // Key: ProofRule class, Value: (Key: Name, Value: ProofRule)
  private static final Map<Class<? extends ProofRule>, Map<String, ProofRule>> RULES =
      new ConcurrentHashMap<>();

  private static void register(Class<? extends ProofRule> clazz, ProofRule rule) {
    RULES.computeIfAbsent(clazz, k -> new HashMap<>()).put(rule.getName(), rule);
  }

  public static ProofRule fromName(Class<? extends ProofRule> clazz, String name) {
    return RULES.getOrDefault(clazz, new HashMap<>()).get(name.toLowerCase());
  }

  static {
    for (CVC5ProofRule rule : CVC5ProofRule.values()) {
      ProofRuleRegistry.register(CVC5ProofRule.class, rule);
    }

    for (Z3ProofRule rule : Z3ProofRule.values()) {
      ProofRuleRegistry.register(Z3ProofRule.class, rule);
    }
  }

    */
}
