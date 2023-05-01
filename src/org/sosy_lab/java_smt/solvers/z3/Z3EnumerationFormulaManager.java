// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.Native;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractEnumerationFormulaManager;

class Z3EnumerationFormulaManager
    extends AbstractEnumerationFormulaManager<Long, Long, Long, Long> {

  private static class EnumType {
    private final EnumerationFormulaType eType;
    private final long type;
    private final ImmutableMap<String, Long> constants;

    private EnumType(
        EnumerationFormulaType pEType, long pType, ImmutableMap<String, Long> pConstants) {
      eType = pEType;
      type = pType;
      constants = pConstants;
    }
  }

  private final long z3context;

  private final Map<String, EnumType> enumConstants = new LinkedHashMap<>();

  Z3EnumerationFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
  }

  @Override
  protected EnumerationFormulaType declareEnumerationImpl(String pName, Set<String> pElementNames) {
    final EnumerationFormulaType type = FormulaType.getEnumerationType(pName, pElementNames);
    EnumType existingType = enumConstants.get(pName);
    if (existingType == null) {
      enumConstants.put(pName, declareEnumeration0(type));
    } else {
      Preconditions.checkArgument(
          type.equals(existingType.eType),
          "Enumeration type '%s' is already declared as '%s'.",
          type,
          existingType.eType);
    }
    return type;
  }

  private EnumType declareEnumeration0(EnumerationFormulaType pType) {
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
  protected Long makeConstantImpl(String pName, EnumerationFormulaType pType) {
    return checkNotNull(enumConstants.get(pType.getName()).constants.get(pName));
  }

  @Override
  protected Long makeVariableImpl(String pVar, EnumerationFormulaType pType) {
    return getFormulaCreator().makeVariable(enumConstants.get(pType.getName()).type, pVar);
  }

  @Override
  protected Long equivalenceImpl(Long pF1, Long pF2) {
    return Native.mkEq(z3context, pF1, pF2);
  }
}
