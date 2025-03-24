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

import org.sosy_lab.java_smt.basicimpl.AbstractProofDag;

/**
 * This class represents a resolution proof DAG. Its nodes might be of the type
 * {@link SourceProofNode} or {@link ResolutionProofNode}. It is used to represent proofs based on
 * the RESOLUTE proof format from SMTInterpol.
 *
 * @see ResProofRule
 */
@SuppressWarnings("all")
public class ResolutionProofDag extends AbstractProofDag {
  //Work in progress. The functionality of producing just nodes should be provided first.
  //The idea is to provide extended functionality (by providng a set of edges for example).
}
