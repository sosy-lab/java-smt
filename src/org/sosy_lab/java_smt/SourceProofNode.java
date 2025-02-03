/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.basicimpl.AbstractProofNode;

public class SourceProofNode extends AbstractProofNode<resProofRule.Rule>
    implements ProofNode<resProofRule.Rule> {


  public SourceProofNode(resProofRule.Rule rule, Formula formula) {
    super(rule, formula);
  }


  @Override
  public boolean isSource() {
    return true;
  }
}
