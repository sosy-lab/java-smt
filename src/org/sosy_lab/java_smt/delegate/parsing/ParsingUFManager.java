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

import com.google.common.collect.Lists;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.delegate.parsing.ParsingFormulaManager.SymbolManager;

public class ParsingUFManager implements UFManager {
  private final SymbolManager symbolManager;
  private final FormulaManager manager;
  private final UFManager delegate;

  public ParsingUFManager(
      SymbolManager pSymbolManager, FormulaManager pManager, UFManager pDelegate) {
    symbolManager = pSymbolManager;
    manager = pManager;
    delegate = pDelegate;
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, List<FormulaType<?>> args) {
    var uf = delegate.declareUF(name, returnType, args);
    symbolManager.addFunction(name, p -> delegate.callUF(uf, p));
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
    var uf = declareUF(name, pReturnType, Lists.transform(pArgs, manager::getFormulaType));
    return callUF(uf, pArgs);
  }
}
