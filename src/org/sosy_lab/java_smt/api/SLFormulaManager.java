// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

/**
 * The {@link SLFormulaManager} can build formulae for separation logic.
 *
 * <p>Info: A {@link ProverEnvironment} only supports the assertion of well-typed SL-formulae, i.e.
 * all formulae for one heap need to use matching types (sorts) for the AdressFormulae and
 * ValueFormulae. The user has to take care of this, otherwise the {@link ProverEnvironment}
 * complains at runtime!
 *
 * @see <a href="https://en.wikipedia.org/wiki/Separation_logic">Separation Logic</a>
 * @see <a href="https://cacm.acm.org/research/separation-logic/">Separation Logic</a>
 * @see <a
 *     href="https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/cs818A3-11.html">15-818A3
 *     Introduction to Separation Logic (6 units) Spring 2011</a>
 * @see <a href="https://www.philipzucker.com/executable-seperation">Modeling Separation Logic with
 *     Python Dicts and Z3</a>
 */
@SuppressWarnings("MethodTypeParameterName")
public interface SLFormulaManager {

  /**
   * Creates a formula representing the "separating conjunction" (*) of two Boolean formulas. In
   * separation logic, the separating conjunction asserts that the two formulas describe disjoint
   * parts of the heap. It is similar to the logical AND operator, but with the additional
   * constraint that the memory regions described by the two formulas do not overlap.
   *
   * @return a Boolean formula representing the separating conjunction of {@code f1} and {@code f2}.
   */
  BooleanFormula makeStar(BooleanFormula f1, BooleanFormula f2);

  /**
   * Creates a formula representing a "points-to" relation in the heap. The "points-to" relation
   * asserts that a pointer points to a specific value in memory.
   *
   * @param <AF> the type of the address formula.
   * @param <VF> the type of the value formula.
   * @param ptr the pointer formula.
   * @param to the value formula.
   * @return a Boolean formula representing the "points-to" relation.
   */
  <AF extends Formula, VF extends Formula> BooleanFormula makePointsTo(AF ptr, VF to);

  /**
   * Creates a formula representing the "magic wand" (-*) operator in separation logic. The "magic
   * wand" operator asserts that if the first formula holds, then the second formula can be added to
   * the heap without conflict. It is a form of implication (=&gt;) that takes into account the
   * disjointness of memory regions.
   *
   * @return a Boolean formula representing the "magic wand" of {@code f1} and {@code f2}.
   */
  BooleanFormula makeMagicWand(BooleanFormula f1, BooleanFormula f2);

  /**
   * Creates a formula representing an empty heap. The empty heap formula asserts that no memory is
   * allocated for the given address and value types.
   *
   * @param <AF> the type of the address formula.
   * @param <VF> the type of the value formula.
   * @param <AT> the type of the address formula type.
   * @param <VT> the type of the value formula type.
   * @param pAddressType the type of the address formula.
   * @param pValueType the type of the value formula.
   * @return a Boolean formula representing an empty heap.
   */
  <AF extends Formula, VF extends Formula, AT extends FormulaType<AF>, VT extends FormulaType<VF>>
      BooleanFormula makeEmptyHeap(AT pAddressType, VT pValueType);

  /**
   * Creates a formula representing the "nil" element for a given address type. The "nil" element is
   * used to represent a null pointer or an unallocated memory address.
   *
   * @param <AF> the type of the address formula.
   * @param <AT> the type of the address formula type.
   * @param pAddressType the type of the address formula.
   * @return a formula representing the "nil" element for the given address type.
   */
  <AF extends Formula, AT extends FormulaType<AF>> AF makeNilElement(AT pAddressType);
}
