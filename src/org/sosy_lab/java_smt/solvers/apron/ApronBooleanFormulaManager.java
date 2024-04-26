// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.apron;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Tcons1;
import apron.Texpr1Node;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntCstNode;

/**
 * Apron only supports and-operations by stacking constraints. Boolean type variables do not exist.
 */
public class ApronBooleanFormulaManager
    extends AbstractBooleanFormulaManager<ApronNode, ApronFormulaType, Environment, Long> {

  private final ApronFormulaCreator apronFormulaCreator;
  private final Logger logger = Logger.getLogger("BooleanFormula logger");

  protected ApronBooleanFormulaManager(ApronFormulaCreator pCreator) {
    super(pCreator);
    this.apronFormulaCreator = pCreator;
  }

  @Override
  protected ApronNode makeVariableImpl(String pVar) {
    throw new UnsupportedOperationException("Apron supports only numeral variables.");
  }

  /**
   * True is symbolized by 1=1, false by 1!=1.
   *
   * @param value boolean value to implement
   * @return ApronConstraint of the form 1=1 (true) or 1!=1 (false)
   */
  @Override
  protected ApronNode makeBooleanImpl(boolean value) {
    ApronIntCstNode one = new ApronIntCstNode(BigInteger.ONE);
    Map<ApronNode, Integer> map = new HashMap<>();
    if (value) {
      // 1 != 0
      map.put(one, Tcons1.DISEQ);
    } else {
      // 1 = 0
      map.put(one, Tcons1.EQ);
    }
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }

  @Override
  protected ApronNode not(ApronNode pParam1) {
    throw new UnsupportedOperationException("Apron does not support not() operations.");
  }

  /**
   * the and() method is implemented by stacking two constraints.
   *
   * @param pParam1 ApronConstraint 1
   * @param pParam2 ApronConstraint 2
   * @return new ApronConstraint which combines the two input constraints
   */
  @Override
  protected ApronNode and(ApronNode pParam1, ApronNode pParam2) {
    ApronConstraint cons1 = (ApronConstraint) pParam1;
    ApronConstraint cons2 = (ApronConstraint) pParam2;
    List<ApronConstraint> constraints = new ArrayList<>();
    constraints.add(cons1);
    constraints.add(cons2);
    return new ApronConstraint(constraints, apronFormulaCreator.getFormulaEnvironment());
  }

  @Override
  protected ApronNode or(ApronNode pParam1, ApronNode pParam2) {
    throw new UnsupportedOperationException("Apron does not support or() operations.");
  }

  @Override
  protected ApronNode xor(ApronNode pParam1, ApronNode pParam2) {
    throw new UnsupportedOperationException("Apron does not support xor() operations.");
  }

  @Override
  protected ApronNode equivalence(ApronNode bits1, ApronNode bits2) {
    throw new UnsupportedOperationException("Apron does not support equivalence() operations.");
  }

  /**
   * For checking whether a BooleanFormula is true, Apron needs an Abstract1 object with the formula
   * as input. Then one can check, if the Abstract1 object is bottom (for false).
   *
   * @param bits ApronConstraint to check
   * @return !isBottom()
   */
  @Override
  protected boolean isTrue(ApronNode bits) {
    try {
      ApronConstraint constraint = (ApronConstraint) bits;
      Map<Tcons1, Texpr1Node> map = constraint.getConstraintNodes();
      Tcons1[] tcons1s = map.keySet().toArray(new Tcons1[map.size()]);
      Abstract1 helper = new Abstract1(this.apronFormulaCreator.getManager(), tcons1s);
      boolean isBottom = helper.isBottom(this.apronFormulaCreator.getManager());
      if (isBottom) {
        return false;
      } else {
        logger.setLevel(Level.WARNING);
        logger.warning(
            "Apron can only guarantee for clear results for UNSAT! SAT can "
                + "also mean UNKNOWN!");
        return true;
      }
    } catch (ApronException pException) {
      throw new RuntimeException(pException);
    }
  }

  /**
   * For checking whether a BooleanFormula is false, Apron needs an Abstract1 object with the
   * formula as input. Then one can check, if the Abstract1 object is bottom (for false).
   *
   * @param bits ApronConstraint to check
   * @return isBottom()
   */
  @Override
  protected boolean isFalse(ApronNode bits) {
    try {
      ApronConstraint constraint = (ApronConstraint) bits;
      Map<Tcons1, Texpr1Node> map = constraint.getConstraintNodes();
      Tcons1[] tcons1s = map.keySet().toArray(new Tcons1[map.size()]);
      Abstract1 helper = new Abstract1(this.apronFormulaCreator.getManager(), tcons1s);
      Boolean isBottom = helper.isBottom(this.apronFormulaCreator.getManager());
      if (!isBottom) {
        logger.setLevel(Level.WARNING);
        logger.warning(
            "Apron can only guarantee for clear results for UNSAT! SAT can also mean UNKNOWN!");
      }
      return isBottom;
    } catch (ApronException pException) {
      throw new RuntimeException(pException);
    }
  }

  @Override
  protected ApronNode ifThenElse(ApronNode cond, ApronNode f1, ApronNode f2) {
    throw new UnsupportedOperationException("Apron does not support ifThenElse() operations.");
  }
}
