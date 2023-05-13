// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_enum_constants;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_enum_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_term;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractEnumerationFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class Mathsat5EnumerationFormulaManager
    extends AbstractEnumerationFormulaManager<Long, Long, Long, Long> {

  private final long mathsatEnv;

  protected Mathsat5EnumerationFormulaManager(FormulaCreator<Long, Long, Long, Long> pCreator) {
    super(pCreator);
    this.mathsatEnv = pCreator.getEnv();
  }

  @Override
  protected EnumType declareEnumeration0(EnumerationFormulaType pType) {

    // MathSAT does not support equal-named enumeration elements in distinct enumeration types.
    for (EnumType existingType : enumerations.values()) {
      Preconditions.checkArgument(
          Iterables.all(pType.getElements(), e -> !existingType.constants.containsKey(e)),
          "Enumeration type '%s' has elements that already appear in enumeration type '%s'.",
          pType,
          existingType.enumerationFormulaType);
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
  protected Long equivalenceImpl(Long pF1, Long pF2) {
    return msat_make_equal(mathsatEnv, pF1, pF2);
  }
}
