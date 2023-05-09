// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static com.google.common.base.Preconditions.checkNotNull;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_enum_constants;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_enum_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_term;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractEnumerationFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class Mathsat5EnumerationFormulaManager
    extends AbstractEnumerationFormulaManager<Long, Long, Long, Long> {

  /** The class 'EnumType' is just a plain internal value-holding class. */
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

  private final long mathsatEnv;

  private final Map<String, EnumType> enumerations = new LinkedHashMap<>();

  protected Mathsat5EnumerationFormulaManager(FormulaCreator<Long, Long, Long, Long> pCreator) {
    super(pCreator);
    this.mathsatEnv = pCreator.getEnv();
  }

  @Override
  protected EnumerationFormulaType declareEnumerationImpl(String pName, Set<String> pElementNames) {
    final EnumerationFormulaType type = FormulaType.getEnumerationType(pName, pElementNames);
    EnumType existingType = enumerations.get(pName);
    if (existingType == null) {
      enumerations.put(pName, declareEnumeration0(type));
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

    // MathSAT does not support equal-named enumeration elements in distinct enumeration types.
    for (EnumType existingType : enumerations.values()) {
      Preconditions.checkArgument(
          Iterables.all(pType.getElements(), e -> !existingType.constants.containsKey(e)),
          "Enumeration type '%s' has elements that already appear in enumeration type '%s'.",
          pType,
          existingType.eType);
    }

    String[] elements = pType.getElements().toArray(new String[] {});
    long enumType = msat_get_enum_type(mathsatEnv, pType.getName(), elements.length, elements);

    // we store the constants for later access
    long[] constantDecls = msat_get_enum_constants(mathsatEnv, enumType);
    ImmutableMap.Builder<String, Long> constantsMapping = ImmutableMap.builder();
    for (int i = 0; i < elements.length; i++) {
      long constant = msat_make_term(mathsatEnv, constantDecls[i], new long[] {});
      constantsMapping.put(elements[i], constant);
    }
    return new EnumType(pType, enumType, constantsMapping.buildOrThrow());
  }

  @Override
  protected Long makeConstantImpl(String pName, EnumerationFormulaType pType) {
    return checkNotNull(enumerations.get(pType.getName()).constants.get(pName));
  }

  @Override
  protected Long makeVariableImpl(String pVar, EnumerationFormulaType pType) {
    return getFormulaCreator().makeVariable(enumerations.get(pType.getName()).type, pVar);
  }

  @Override
  protected Long equivalenceImpl(Long pF1, Long pF2) {
    return msat_make_equal(mathsatEnv, pF1, pF2);
  }
}
