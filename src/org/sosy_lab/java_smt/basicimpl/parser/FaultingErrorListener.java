/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl.parser;

import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;

public class FaultingErrorListener extends BaseErrorListener {
  private final String prefix;

  public FaultingErrorListener(String pMessage) {
    prefix = pMessage;
  }

  @Override
  public void syntaxError(
      Recognizer<?, ?> recognizer, Object o, int i, int i1, String s, RecognitionException e) {
    throw new IllegalArgumentException(prefix + ": " + s);
  }
}
