// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import io.github.cvc5.Datatype;
import io.github.cvc5.DatatypeConstructorDecl;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractEnumerationFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class CVC5EnumerationFormulaManager
    extends AbstractEnumerationFormulaManager<Term, Sort, Solver, Term> {

  /** The class 'EnumType' is just a plain internal value-holding class. */
  private static class EnumType {
    private final EnumerationFormulaType eType;
    private final Sort sort;

    private EnumType(EnumerationFormulaType pEType, Sort pSort) {
      eType = pEType;
      sort = pSort;
    }
  }

  private final Solver solver;

  private final Map<String, EnumType> enumerations = new LinkedHashMap<>();

  protected CVC5EnumerationFormulaManager(FormulaCreator<Term, Sort, Solver, Term> pCreator) {
    super(pCreator);
    solver = pCreator.getEnv();
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
    DatatypeConstructorDecl[] constructors =
        pType.getElements().stream()
            .map(solver::mkDatatypeConstructorDecl)
            .toArray(DatatypeConstructorDecl[]::new);
    Sort enumType = solver.declareDatatype(pType.getName(), constructors);
    return new EnumType(pType, enumType);
  }

  @Override
  protected Term makeConstantImpl(String pName, EnumerationFormulaType pType) {
    Datatype enumType = enumerations.get(pType.getName()).sort.getDatatype();
    return solver.mkTerm(Kind.APPLY_CONSTRUCTOR, enumType.getConstructor(pName).getTerm());
  }

  @Override
  protected Term makeVariableImpl(String pVar, EnumerationFormulaType pType) {
    Sort enumType = enumerations.get(pType.getName()).sort;
    return getFormulaCreator().makeVariable(enumType, pVar);
  }

  @Override
  protected Term equivalenceImpl(Term pF1, Term pF2) {
    return solver.mkTerm(Kind.EQUAL, pF1, pF2);
  }
}
