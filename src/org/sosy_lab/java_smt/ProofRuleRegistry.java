/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt;

import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

public class ProofRuleRegistry {
  // Key: ProofRule class, Value: (Key: Name, Value: ProofRule)
  private static final Map<Class<? extends ProofRule>, Map<String, ProofRule>> RULES =
      new HashMap<>();

  public static void register(Class<? extends ProofRule> clazz, ProofRule rule) {
    RULES.computeIfAbsent(clazz, k -> new HashMap<>()).put(rule.getName(), rule);
  }

  public static ProofRule fromName(Class<? extends ProofRule> clazz, String name) {
    return RULES.getOrDefault(clazz, new HashMap<>()).get(name);
  }
}
