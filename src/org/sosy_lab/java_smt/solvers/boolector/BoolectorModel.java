/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.boolector;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;

class BoolectorModel extends CachingAbstractModel<Long, Long, BoolectorEnvironment> {

  private final static char BOOLECTOR_VARIABLE_ARBITRARI_REPLACEMENT = '1';

  private final long btor;
  private final BoolectorAbstractProver<?> prover;
  private final BoolectorFormulaCreator creator;
  private boolean closed = false;

  private final ImmutableList<Long> assertedTerms;

  BoolectorModel(
      long btor,
      BoolectorFormulaCreator creator,
      BoolectorAbstractProver<?> pProver,
      Collection<Long> assertedTerms) {
    super(creator);
    this.creator = creator;
    this.btor = btor;
    this.prover = pProver;
    this.assertedTerms = ImmutableList.copyOf(assertedTerms);
  }

  @Override
  public void close() {
    if (!closed) {
      // BtorJNI.boolector_delete(btor);
      // Technically boolector has no model
      closed = true;
    }
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!prover.closed, "cannot use model after prover is closed");
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    for (Long formula : assertedTerms) {
      for (Entry<String, Long> entry : creator.extractVariablesAndUFs(formula, true).entrySet()) {
        String name = entry.getKey();
        Long var = entry.getValue();
        System.out.println("toList with: " + name);
        System.out.println(BtorJNI.boolector_help_dump_node_smt2(btor, var));
        /*
         * if (BtorJNI.boolector_is_array(btor, var)) {
         * assignments.add(getArrayAssignment(formula)); } else if (BtorJNI.boolector_is_uf(btor,
         * var)) { assignments.add(getUFAssignment(formula)); } else if
         * (BtorJNI.boolector_is_var(btor, var)) { if (BtorJNI.boolector_get_width(btor, var) == 1)
         * { assignments.add(getBoolAssignment(formula)); } else {
         * assignments.add(getBvAssignment(formula)); } }
         */
      }
    }
    return assignments.build();
  }

  private ValueAssignment getBoolAssignment(long key) {
    List<Object> argumentInterpretation = new ArrayList<>();
    Long value = evalImpl(key);
    // TODO revisit equality method!!!
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(value),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, value)),
        creator.getName(key, btor),
        creator.convertValue(key, value),
        argumentInterpretation);
  }

  private ValueAssignment getBvAssignment(long key) {
    List<Object> argumentInterpretation = new ArrayList<>();
    Long value = evalImpl(key);
    // TODO revisit equality method!!!
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(value),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, value)),
        creator.getName(key, btor),
        creator.convertValue(key, value),
        argumentInterpretation);
  }

  private ValueAssignment getUFAssignment(long key) {
    List<Object> argumentInterpretation = new ArrayList<>();
    Long value = evalImpl(key);
    // TODO
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(value),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, value)),
        creator.getName(key, btor),
        creator.convertValue(key, value),
        argumentInterpretation);
  }

  private ValueAssignment getArrayAssignment(long key) {
    List<Object> argumentInterpretation = new ArrayList<>();
    Long value = evalImpl(key);
    // TODO
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(value),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, value)),
        creator.getName(key, btor),
        creator.convertValue(key, value),
        argumentInterpretation);
  }

  // check for array/uf/quant
  @Override
  protected Long evalImpl(Long pFormula) {
    Preconditions.checkState(!closed);
    if (BtorJNI.boolector_is_array(btor, pFormula)) {
      String assignment = BtorJNI.boolector_bv_assignment(btor, pFormula);
      return parseLong(assignment);
    } else if (BtorJNI.boolector_is_const(btor, pFormula)) {
      String assignment = BtorJNI.boolector_get_bits(btor, pFormula);
      return parseLong(assignment);
    } else if (BtorJNI.boolector_is_bitvec_sort(btor, BtorJNI.boolector_get_sort(btor, pFormula))) {
      BtorJNI.boolector_bv_assignment(btor, pFormula);
      return parseLong(BtorJNI.boolector_bv_assignment(btor, pFormula));
    }
    String assignment = BtorJNI.boolector_bv_assignment(btor, pFormula);
    return parseLong(assignment);
  }

  /**
   * Boolector puts out Strings containing 1,0 or x that have to be parsed. If you want different
   * values for x, change it in the constant! (BOOLECTOR_VARIABLE_ARBITRARI_REPLACEMENT)
   *
   * @param assignment String with the assignment of Boolector var.
   * @return BigInteger in decimal.
   */
  private Long parseLong(String assignment) {
    try {
      BigInteger bigInt = new BigInteger(assignment, 2);
      return bigInt.longValue();
    } catch (NumberFormatException e) {
      char[] charArray = assignment.toCharArray();
      for (int i = 0; i < charArray.length; i++) {
        if (charArray[i] == 'x') {
          charArray[i] = '1';
        } else if (charArray[i] != '0' && charArray[i] != '1') {
          throw new IllegalArgumentException(
              "Boolector gave back an assignment that is not parseable.");
        }
      }
      assignment = charArray.toString();
    }
    BigInteger bigInt = new BigInteger(assignment, 2);
    return bigInt.longValue();
  }

}
