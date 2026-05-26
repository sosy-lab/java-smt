/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3legacy;

import com.google.common.collect.ImmutableMap;
import com.microsoft.z3legacy.Native;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractEnumerationFormulaManager;

class Z3LegacyEnumerationFormulaManager
    extends AbstractEnumerationFormulaManager<Long, Long, Long, Long> {

  private final long z3context;

  Z3LegacyEnumerationFormulaManager(Z3LegacyFormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
  }

  @Override
  protected EnumType declareEnumeration0(EnumerationFormulaType pType) {
    long symbol = Native.mkStringSymbol(z3context, pType.getName());

    String[] elements = pType.getElements().toArray(new String[] {});
    long[] elementSymbols = new long[elements.length];
    for (int i = 0; i < elements.length; i++) {
      elementSymbols[i] = Native.mkStringSymbol(z3context, elements[i]);
    }

    long[] constants = new long[pType.getElements().size()];
    long[] predicates = new long[pType.getElements().size()]; // unused later

    long enumType =
        Native.mkEnumerationSort(
            z3context, symbol, elements.length, elementSymbols, constants, predicates);
    Native.incRef(z3context, enumType);

    // we store the constants for later access
    ImmutableMap.Builder<String, Long> constantsMapping = ImmutableMap.builder();
    for (int i = 0; i < elements.length; i++) {
      long constantApp = Native.mkApp(z3context, constants[i], 0, null);
      Native.incRef(z3context, constantApp);
      constantsMapping.put(elements[i], constantApp);
    }
    return new EnumType(pType, enumType, constantsMapping.buildOrThrow());
  }

  @Override
  protected Long equivalenceImpl(Long pF1, Long pF2) {
    return Native.mkEq(z3context, pF1, pF2);
  }
}
