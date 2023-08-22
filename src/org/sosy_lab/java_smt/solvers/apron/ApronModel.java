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

package org.sosy_lab.java_smt.solvers.apron;

import apron.ApronException;
import apron.Environment;
import apron.Interval;
import apron.Manager;
import apron.MpqScalar;
import apron.Scalar;
import apron.Tcons1;
import apron.Texpr1BinNode;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.math.BigInteger;
import java.util.Collection;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronIntBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronIntCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronIntVarNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronRatBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronRatCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronRatVarNode;

public class ApronModel extends AbstractModel<ApronNode, ApronFormulaType, Environment> {

  private final ApronFormulaCreator formulaCreator;
  private final ApronTheoremProver prover;
  private final ImmutableList<ApronConstraint> assertedExpressions;

  protected ApronModel(
      ApronTheoremProver pProver,
      ApronFormulaCreator creator,
      Collection<ApronConstraint> pAssertedExpressions) {
    super(pProver, creator);
    this.formulaCreator = creator;
    this.prover = pProver;
    this.assertedExpressions = ImmutableList.copyOf(pAssertedExpressions);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    Preconditions.checkState(!isClosed());
    return generateModel();
  }

  private ImmutableList<ValueAssignment> generateModel() {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    for (ApronConstraint constraint : assertedExpressions) {
      for (String var : constraint.getVarNames()) {
        builder.add(getAssignment(constraint, var));
      }
    }
    return builder.build().asList();
  }

  private ValueAssignment getAssignment(ApronConstraint pFormula, String pVar) {
    //needed: Formula keyFormula, Formula valueFormula, BooleanFormula formula (x = 3),
    // Object value, List<?> argumentInterpretation
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder(); //TODO
    // : empty list!
    try {
      ApronConstraint constraint = pFormula;
      String varName = pVar;
      if (pFormula.getApronNode().getType().equals(FormulaType.INTEGER)) {
        ApronNode keyFormula = new ApronIntVarNode(pVar, formulaCreator);
        Manager man = this.prover.getAbstract1().getCreationManager();
        Interval interval = this.prover.getAbstract1().getBound(man, pVar);
        MpqScalar value = (MpqScalar) interval.sup;
        int castIntValue = Integer.parseInt(value.toString());
        ApronIntCstNode valueFormula = new ApronIntCstNode(BigInteger.valueOf(castIntValue));
        ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(keyFormula, valueFormula,
            Texpr1BinNode.OP_SUB);
        BooleanFormula formula = new ApronConstraint(Tcons1.EQ, formulaCreator.getEnvironment(),
            binaryNode);
        return new ValueAssignment(keyFormula, valueFormula, formula, pVar, value,
            argumentInterpretationBuilder.build());
      } else {
        ApronNode keyFormula = new ApronRatVarNode(pVar, formulaCreator);
        Manager man = this.prover.getAbstract1().getCreationManager();
        Interval interval = this.prover.getAbstract1().getBound(man, pVar);
        Scalar value = interval.sup;
        //TODO: unfortunatly it is not possible to extract nominator and denominator out of an
        // Scalar; So all models show Integer Values
        int castRatValue = Integer.parseInt(value.toString());
        ApronRatCstNode valueFormula = new ApronRatCstNode(BigInteger.valueOf(castRatValue),
            BigInteger.ONE);
        ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(keyFormula, valueFormula,
            Texpr1BinNode.OP_SUB);
        BooleanFormula formula = new ApronConstraint(Tcons1.EQ, formulaCreator.getEnvironment(),
            binaryNode);
        return new ValueAssignment(keyFormula, valueFormula, formula, pVar, value,
            argumentInterpretationBuilder.build());
      }
    } catch (ApronException pApronException) {
      throw new RuntimeException(pApronException);
    }
  }

  @Override
  protected @Nullable ApronNode evalImpl(ApronNode formula) {
    Preconditions.checkState(!isClosed());
    return formula;
  }
}
