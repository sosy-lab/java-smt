/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import com.google.common.base.Joiner;
import com.google.common.collect.FluentIterable;
import java.util.Arrays;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.UFManager;

public class TraceUFManager implements UFManager {
  private final UFManager delegate;
  private final TraceLogger logger;

  TraceUFManager(UFManager pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, List<FormulaType<?>> args) {
    return logger.logDef(
        "mgr.getUFManager()",
        String.format(
            "declareUF(\"%s\", %s, ImmutableList.of(%s))",
            name,
            logger.printFormulaType(returnType),
            Joiner.on(", ").join(FluentIterable.from(args).transform(logger::printFormulaType))),
        () -> delegate.declareUF(name, returnType, args));
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, FormulaType<?>... args) {
    return declareUF(name, returnType, Arrays.asList(args));
  }

  @Override
  public <T extends Formula> T callUF(
      FunctionDeclaration<T> funcType, List<? extends Formula> args) {
    return logger.logDef(
        "mgr.getUFManager()",
        String.format(
            "callUF(%s, ImmutableList.of(%s))",
            logger.toVariable(funcType),
            Joiner.on(", ").join(FluentIterable.from(args).transform(logger::toVariable))),
        () -> delegate.callUF(funcType, args));
  }

  @Override
  public <T extends Formula> T callUF(FunctionDeclaration<T> funcType, Formula... args) {
    return callUF(funcType, Arrays.asList(args));
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs) {
    throw new UnsupportedOperationException();
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, Formula... pArgs) {
    throw new UnsupportedOperationException();
  }
}
