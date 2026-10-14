/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.parsing;

import com.google.common.collect.ImmutableList;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.UFManager;

public class ParsingUFManager implements UFManager {
  private final UFManager delegate;

  private final FormulaManager mgr;
  private final ParsingFormulaManager.Declarations declarations;

  public ParsingUFManager(
      UFManager pDelegate, FormulaManager pMgr, ParsingFormulaManager.Declarations pDeclarations) {
    delegate = pDelegate;
    mgr = pMgr;
    declarations = pDeclarations;
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, List<FormulaType<?>> args) {
    FunctionDeclaration<T> uf = delegate.declareUF(name, returnType, args);
    declarations.addFunction(name, uf);
    return uf;
  }

  @Override
  public <T extends Formula> T callUF(
      FunctionDeclaration<T> funcType, List<? extends Formula> args) {
    return delegate.callUF(funcType, args);
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
