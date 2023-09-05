/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.java_smt.solvers.bitwuzla;

import java.util.List;
import java.util.stream.LongStream;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Long, Long, Long, Long> {
  private final long bitwuzla;

  protected BitwuzlaQuantifiedFormulaManager(FormulaCreator<Long, Long, Long, Long> pCreator) {
    super(pCreator);
    bitwuzla = getFormulaCreator().getEnv();
  }

  @Override
  protected Long eliminateQuantifiers(Long pExtractInfo)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Bitwuzla does not support eliminating Quantifiers.");
  }

  @Override
  public Long mkQuantifier(Quantifier q, List<Long> vars, Long body) {
    long[] argsAndBody =
        LongStream.concat(vars.stream().mapToLong(Long::longValue), LongStream.of(body)).toArray();
    if (q.equals(Quantifier.FORALL)) {
      return bitwuzlaJNI.bitwuzla_mk_term(
          BitwuzlaKind.BITWUZLA_KIND_FORALL.swigValue(), argsAndBody.length, argsAndBody);
    } else {
      return bitwuzlaJNI.bitwuzla_mk_term(
          BitwuzlaKind.BITWUZLA_KIND_EXISTS.swigValue(), argsAndBody.length, argsAndBody);
    }
  }
}
