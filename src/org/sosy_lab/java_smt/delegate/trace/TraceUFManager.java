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
import com.google.common.collect.ImmutableList;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.UFManager;

public class TraceUFManager implements UFManager {
  private final UFManager delegate;

  private final FormulaManager mgr;
  private final TraceLogger logger;

  TraceUFManager(UFManager pDelegate, FormulaManager pMgr, TraceLogger pLogger) {
    delegate = pDelegate;
    mgr = pMgr;
    logger = pLogger;
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, List<FormulaType<?>> args) {
    String var = logger.newVariable();
    logger.appendDef(
        var,
        String.format(
            "mgr.getUFManager().declareUF(%s, %s, ImmutableList.of(%s))",
            logger.printString(name),
            logger.printFormulaType(returnType),
            FluentIterable.from(args).transform(logger::printFormulaType).join(Joiner.on(", "))));
    FunctionDeclaration<T> f = delegate.declareUF(name, returnType, args);
    if (logger.isTracked(f)) {
      logger.undoLast();
    } else {
      logger.keepLast();
      logger.mapVariable(var, f);
    }
    return f;
  }

  @Override
  public <T extends Formula> T callUF(
      FunctionDeclaration<T> funcType, List<? extends Formula> args) {
    if (funcType.getKind().equals(FunctionDeclarationKind.UF)) {
      return logger.logDef(
          "mgr.getUFManager()",
          String.format(
              "callUF(%s, ImmutableList.of(%s))",
              logger.toVariable(funcType), logger.toVariables(args)),
          () -> delegate.callUF(funcType, args));
    } else {
      return mgr.makeApplication(funcType, args);
    }
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs) {
    ImmutableList.Builder<FormulaType<?>> builder = ImmutableList.builder();
    for (Formula f : pArgs) {
      builder.add(mgr.getFormulaType(f));
    }
    return callUF(declareUF(name, pReturnType, builder.build()), pArgs);
  }
}
