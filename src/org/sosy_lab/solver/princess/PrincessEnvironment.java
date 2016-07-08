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
package org.sosy_lab.solver.princess;

import static com.google.common.collect.Iterables.getOnlyElement;
import static scala.collection.JavaConversions.asJavaIterable;
import static scala.collection.JavaConversions.iterableAsScalaIterable;
import static scala.collection.JavaConversions.mapAsJavaMap;
import static scala.collection.JavaConversions.seqAsJavaList;

import ap.SimpleAPI;
import ap.parser.IAtom;
import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.ITerm;
import ap.parser.SMTLineariser;
import ap.parser.SMTParser2InputAbsy;
import ap.parser.SMTParser2InputAbsy.SMTFunctionType;
import ap.parser.SMTParser2InputAbsy.SMTType;
import ap.terfor.ConstantTerm;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Sets;

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;

import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.solver.princess.PrincessSolverContext.PrincessOptions;

import scala.Tuple2;
import scala.Tuple3;
import scala.collection.Seq;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import javax.annotation.Nullable;

/** This is a Wrapper around Princess.
 * This Wrapper allows to set a logfile for all Smt-Queries (default "princess.###.smt2").
 * It also manages the "shared variables": each variable is declared for all stacks.
 */
class PrincessEnvironment {

  /** cache for variables, because they do not implement equals() and hashCode(),
   * so we need to have the same objects. */
  private final Map<String, IFormula> boolVariablesCache = new HashMap<>();
  private final Map<String, ITerm> intVariablesCache = new HashMap<>();
  private final Map<String, ITerm> arrayVariablesCache = new HashMap<>();

  private final Map<String, IFunction> functionsCache = new HashMap<>();
  private final Map<IFunction, PrincessTermType> functionsReturnTypes = new HashMap<>();

  private final @Nullable PathCounterTemplate basicLogfile;
  private final ShutdownNotifier shutdownNotifier;

  /** The wrapped API is the first created API.
   * It will never be used outside of this class and never be closed.
   * If a variable is declared, it is declared in the first api,
   * then copied into all registered APIs. Each API has its own stack for formulas. */
  private final SimpleAPI api;
  private final List<PrincessAbstractProver<?, ?>> registeredProvers =
      new ArrayList<>(); // where an API is used
  private final List<SimpleAPI> reusableAPIs = new ArrayList<>();
  private final Map<SimpleAPI, Boolean> allAPIs = new LinkedHashMap<>();

  final PrincessOptions princessOptions;

  PrincessEnvironment(
      @Nullable final PathCounterTemplate pBasicLogfile,
      ShutdownNotifier pShutdownNotifier,
      PrincessOptions pOptions) {

    basicLogfile = pBasicLogfile;
    shutdownNotifier = pShutdownNotifier;
    // this api is only used local in this environment, no need for interpolation
    api = getNewApi(false);
    princessOptions = pOptions;
  }

  /** This method returns a new prover, that is registered in this environment.
   * All variables are shared in all registered APIs. */
  PrincessAbstractProver<?, ?> getNewProver(
      boolean useForInterpolation, PrincessFormulaManager mgr, PrincessFormulaCreator creator) {

    SimpleAPI newApi = null;

    if (princessOptions.reuseProvers()) {
      // shortcut if we have a reusable stack
      for (Iterator<SimpleAPI> it = reusableAPIs.iterator(); it.hasNext(); ) {
        newApi = it.next();
        if (allAPIs.get(newApi) == useForInterpolation) {
          it.remove();
          break;
        }
      }
    }
    if (newApi == null) {
      // if not we have to create a new one
      newApi = getNewApi(useForInterpolation);

      // add all symbols, that are available until now
      boolVariablesCache.values().forEach(newApi::addBooleanVariable);
      intVariablesCache.values().forEach(newApi::addConstant);
      arrayVariablesCache.values().forEach(newApi::addConstant);
      functionsCache.values().forEach(newApi::addFunction);
      allAPIs.put(newApi, useForInterpolation);
    }

    PrincessAbstractProver<?, ?> prover;
    if (useForInterpolation) {
      prover = new PrincessInterpolatingProver(mgr, creator, newApi, shutdownNotifier);
    } else {
      prover = new PrincessTheoremProver(mgr, shutdownNotifier, creator, newApi);
    }
    registeredProvers.add(prover);
    return prover;
  }

  @SuppressFBWarnings("NP_NULL_ON_SOME_PATH_FROM_RETURN_VALUE")
  private SimpleAPI getNewApi(boolean useForInterpolation) {
    final SimpleAPI newApi;
    if (basicLogfile != null) {
      Path logPath = basicLogfile.getFreshPath();
      String fileName = logPath.getFileName().toString();
      String absPath = logPath.toAbsolutePath().toString();
      File directory = new File(absPath.substring(0, absPath.length() - fileName.length()));
      newApi = SimpleAPI.spawnWithLogNoSanitise(fileName, directory);
    } else {
      newApi = SimpleAPI.spawnNoSanitise();
    }
    // we do not use 'sanitise', because variable-names contain special chars like "@" and ":"

    if (useForInterpolation) {
      newApi.setConstructProofs(true); // needed for interpolation
    }

    return newApi;
  }

  void unregisterStack(PrincessAbstractProver<?, ?> stack, SimpleAPI usedAPI) {
    assert registeredProvers.contains(stack) : "cannot unregister stack, it is not registered";
    registeredProvers.remove(stack);
    if (princessOptions.reuseProvers()) {
      reusableAPIs.add(usedAPI);
    } else {
      allAPIs.remove(usedAPI);
    }
  }

  void removeStack(PrincessAbstractProver<?, ?> stack, SimpleAPI usedAPI) {
    assert registeredProvers.contains(stack) : "cannot remove stack, it is not registered";
    registeredProvers.remove(stack);
    allAPIs.remove(usedAPI);
  }

  public List<? extends IExpression> parseStringToTerms(String s, PrincessFormulaCreator creator) {

    Tuple3<
            Seq<IFormula>, scala.collection.immutable.Map<IFunction, SMTFunctionType>,
            scala.collection.immutable.Map<ConstantTerm, SMTType>>
        triple = api.extractSMTLIBAssertionsSymbols(new StringReader(s));

    List<? extends IExpression> formula = seqAsJavaList(triple._1());
    Map<IFunction, SMTFunctionType> functionTypes = mapAsJavaMap(triple._2());
    Map<ConstantTerm, SMTType> constantTypes = mapAsJavaMap(triple._3());

    Set<IExpression> declaredFunctions = new HashSet<>();
    for (IExpression f : formula) {
      declaredFunctions.addAll(creator.extractVariablesAndUFs(f, true).values());
    }
    for (IExpression var : declaredFunctions) {
      if (var instanceof IConstant) {
        SMTType type = constantTypes.get(((IConstant) var).c());
        if (type instanceof SMTParser2InputAbsy.SMTArray) {
          arrayVariablesCache.put(var.toString(), (ITerm) var);
        } else {
          intVariablesCache.put(var.toString(), (ITerm) var);
        }
        addSymbol((IConstant) var);
      } else if (var instanceof IAtom) {
        boolVariablesCache.put(((IAtom) var).pred().name(), (IFormula) var);
        addSymbol((IAtom) var);
      } else if (var instanceof IFunApp) {
        IFunction fun = ((IFunApp) var).fun();
        functionsCache.put(fun.name(), fun);
        functionsReturnTypes.put(fun, convertToTermType(functionTypes.get(fun)));
        addFunction(fun);
      }
    }
    return formula;
  }

  private static PrincessTermType convertToTermType(SMTFunctionType type) {
    SMTType resultType = type.result();
    if (resultType.equals(SMTParser2InputAbsy.SMTBool$.MODULE$)) {
      return PrincessTermType.Boolean;
    } else {
      return PrincessTermType.Integer;
    }
  }

  public Appender dumpFormula(IFormula formula, final PrincessFormulaCreator creator) {
    // remove redundant expressions
    // TODO do we want to remove redundancy completely (as checked in the unit
    // tests (SolverFormulaIOTest class)) or do we want to remove redundancy up
    // to the point we do it for formulas that should be asserted
    Tuple2<IExpression, scala.collection.immutable.Map<IExpression, IExpression>> tuple =
        api.abbrevSharedExpressionsWithMap(formula, 1);
    final IExpression lettedFormula = tuple._1();
    final Map<IExpression, IExpression> abbrevMap = mapAsJavaMap(tuple._2());

    return new Appenders.AbstractAppender() {

      @Override
      public void appendTo(Appendable out) throws IOException {
        Set<IExpression> allVars =
            new HashSet<>(creator.extractVariablesAndUFs(lettedFormula, true).values());
        Deque<IExpression> declaredFunctions = new ArrayDeque<>(allVars);
        Set<String> doneFunctions = new HashSet<>();
        Set<String> todoAbbrevs = new HashSet<>();

        while (!declaredFunctions.isEmpty()) {
          IExpression var = declaredFunctions.poll();
          String name = getName(var);

          // we don't want to declare variables twice, so doublecheck
          // if we have already found the current variable
          if (doneFunctions.contains(name)) {
            continue;
          }
          doneFunctions.add(name);

          // we do only want to add declare-funs for things we really declared
          // the rest is done afterwards
          if (name.startsWith("abbrev_")) {
            todoAbbrevs.add(name);
            Set<IExpression> varsFromAbbrev =
                new HashSet<>(creator.extractVariablesAndUFs(abbrevMap.get(var), true).values());
            Sets.difference(varsFromAbbrev, allVars).forEach(declaredFunctions::push);
            allVars.addAll(varsFromAbbrev);
          } else {
            out.append("(declare-fun ").append(name);

            // function parameters
            out.append(" (");
            if (var instanceof IFunApp) {
              IFunApp function = (IFunApp) var;
              Iterator<ITerm> args = asJavaIterable(function.args()).iterator();
              while (args.hasNext()) {
                args.next();
                // Princess does only support IntegerFormulas in UIFs we don't need
                // to check the type here separately
                if (args.hasNext()) {
                  out.append("Int ");
                } else {
                  out.append("Int");
                }
              }
            }

            out.append(") ");
            out.append(getType(var));
            out.append(")\n");
          }
        }

        // now as everything we know from the formula is declared we have to add
        // the abbreviations, too
        for (Entry<IExpression, IExpression> entry : abbrevMap.entrySet()) {
          IExpression abbrev = entry.getKey();
          IExpression fullFormula = entry.getValue();
          String name =
              getName(getOnlyElement(creator.extractVariablesAndUFs(abbrev, true).values()));

          //only add the necessary abbreviations
          if (!todoAbbrevs.contains(name)) {
            continue;
          }

          out.append("(define-fun ").append(name);

          // the type of each abbreviation
          if (fullFormula instanceof IFormula) {
            out.append(" () Bool ");
          } else if (fullFormula instanceof ITerm) {
            out.append(" () Int ");
          }

          // the abbreviated formula
          out.append(SMTLineariser.asString(fullFormula)).append(" )\n");
        }

        // now add the final assert
        out.append("(assert ").append(SMTLineariser.asString(lettedFormula)).append(")");
      }
    };
  }

  private static String getName(IExpression var) {
    if (var instanceof IAtom) {
      return ((IAtom) var).pred().name();
    } else if (var instanceof IConstant) {
      return var.toString();
    } else if (var instanceof IFunApp) {
      String fullStr = ((IFunApp) var).fun().toString();
      return fullStr.substring(0, fullStr.indexOf("/"));
    }

    throw new IllegalArgumentException("The given parameter is no variable or function");
  }

  private static String getType(IExpression var) {
    if (var instanceof IFormula) {
      return "Bool";

      // functions are included here, they cannot be handled separate for princess
    } else if (var instanceof ITerm) {
      return "Int";
    }

    throw new IllegalArgumentException("The given parameter is no variable or function");
  }

  public IExpression makeVariable(PrincessTermType type, String varname) {
    switch (type) {
      case Boolean:
        {
          if (boolVariablesCache.containsKey(varname)) {
            return boolVariablesCache.get(varname);
          } else {
            IFormula var = api.createBooleanVariable(varname);
            addSymbol(var);
            boolVariablesCache.put(varname, var);
            return var;
          }
        }

      case Integer:
        {
          if (intVariablesCache.containsKey(varname)) {
            return intVariablesCache.get(varname);
          } else {
            ITerm var = api.createConstant(varname);
            addSymbol(var);
            intVariablesCache.put(varname, var);
            return var;
          }
        }
      case Array:
        {
          if (arrayVariablesCache.containsKey(varname)) {
            return arrayVariablesCache.get(varname);
          } else {
            ITerm var = api.createConstant(varname);
            addSymbol(var);
            arrayVariablesCache.put(varname, var);
            return var;
          }
        }

      default:
        throw new AssertionError("unsupported type: " + type);
    }
  }

  /** This function declares a new functionSymbol, that has a given number of params.
   * Princess has no support for typed params, only their number is important. */
  public IFunction declareFun(String name, int nofArgs, PrincessTermType returnType) {
    if (functionsCache.containsKey(name)) {
      assert returnType == functionsReturnTypes.get(functionsCache.get(name));
      return functionsCache.get(name);

    } else {
      IFunction funcDecl = api.createFunction(name, nofArgs);
      addFunction(funcDecl);
      functionsCache.put(name, funcDecl);
      functionsReturnTypes.put(funcDecl, returnType);
      return funcDecl;
    }
  }

  PrincessTermType getReturnTypeForFunction(IFunction fun) {
    return functionsReturnTypes.get(fun);
  }

  public ITerm makeSelect(ITerm array, ITerm index) {
    List<ITerm> args = ImmutableList.of(array, index);
    return api.select(iterableAsScalaIterable(args).toSeq());
  }

  public ITerm makeStore(ITerm array, ITerm index, ITerm value) {
    List<ITerm> args = ImmutableList.of(array, index, value);
    return api.store(iterableAsScalaIterable(args).toSeq());
  }

  public boolean hasArrayType(IExpression exp) {
    return arrayVariablesCache.containsValue(exp)
        || (exp instanceof IFunApp && ((IFunApp) exp).fun().toString().equals("store/3"));
  }

  public IFormula elimQuantifiers(IFormula formula) {
    return api.simplify(formula);
  }

  public String getVersion() {
    return "Princess (unknown version)";
  }

  private void addSymbol(IFormula symbol) {
    for (SimpleAPI otherAPI : allAPIs.keySet()) {
      otherAPI.addBooleanVariable(symbol);
    }
    for (PrincessAbstractProver<?, ?> prover : registeredProvers) {
      prover.addSymbol(symbol);
    }
  }

  private void addSymbol(ITerm symbol) {
    for (SimpleAPI otherAPI : allAPIs.keySet()) {
      otherAPI.addConstant(symbol);
    }
    for (PrincessAbstractProver<?, ?> prover : registeredProvers) {
      prover.addSymbol(symbol);
    }
  }

  private void addFunction(IFunction funcDecl) {
    for (SimpleAPI otherAPI : allAPIs.keySet()) {
      otherAPI.addFunction(funcDecl);
    }
    for (PrincessAbstractProver<?, ?> prover : registeredProvers) {
      prover.addSymbol(funcDecl);
    }
  }
}
