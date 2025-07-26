// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultBooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

/**
 * This program parses user-given formulas and prints out the (minimal) matching theory for them.
 *
 * <p>Warning: This is a prototype and not intended for larger usage.
 */
@SuppressWarnings("unused")
public class FormulaClassifier {

  private final FormulaManager mgr;
  private final SolverContext context;
  private final Classifier v = new Classifier();
  private int levelLinearArithmetic = 0;

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException, IOException {

    if (args.length == 0) {
      help();
    }

    Solvers solver = Solvers.MATHSAT5;
    Path path = null;
    for (String arg : args) {
      if (arg.startsWith("-solver=")) {
        solver = Solvers.valueOf(arg.substring(8));
      } else if (path == null) {
        path = Path.of(arg);
      } else {
        help();
      }
    }

    if (path == null) {
      help();
    }

    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();
    // we need a solver that supports all theories, at least for parsing.
    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {
      List<BooleanFormula> formulas = new ArrayList<>();

      // read all formulas from the file
      List<String> definitions = new ArrayList<>();
      for (String line : Files.readAllLines(path)) {
        // we assume a line-based content
        if (Iterables.any(
            ImmutableList.of(";", "(push ", "(pop ", "(reset", "(set-logic"), line::startsWith)) {
          continue;
        } else if (line.startsWith("(assert ")) {
          BooleanFormula bf =
              context.getFormulaManager().parse(Joiner.on("").join(definitions) + line);
          formulas.add(bf);
        } else {
          // it is a definition
          definitions.add(line);
        }
      }

      // classify the formulas
      FormulaClassifier fc = new FormulaClassifier(context);
      formulas.forEach(fc::visit);
      System.out.println(fc + ", checked formulas: " + formulas.size());

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

      // on some machines we support only some solvers,
      // thus we can ignore these errors.
      logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  private static void help() {
    throw new AssertionError("run $> TOOL [-solver=SOLVER] PATH");
  }

  public FormulaClassifier(SolverContext pContext) {
    context = pContext;
    mgr = context.getFormulaManager();
  }

  public void visit(BooleanFormula f) {
    // first split formula into atoms to avoid repeated analysis of common subtrees.
    AtomCollector atomCollector = new AtomCollector();
    mgr.getBooleanFormulaManager().visitRecursively(f, atomCollector);
    if (atomCollector.hasQuantifiers) {
      v.hasQuantifiers = true;
    }
    // then analyze each part
    for (BooleanFormula part : atomCollector.atoms) {
      int levelLA = mgr.visit(part, v);
      levelLinearArithmetic = Math.max(levelLA, levelLinearArithmetic);
    }
  }

  @Override
  public String toString() {
    // build logic string
    StringBuilder logic = new StringBuilder();
    if (!v.hasQuantifiers) {
      logic.append("QF_");
    }
    if (v.hasArrays) {
      logic.append("A");
    }
    if (v.hasUFs) {
      logic.append("UF");
    }
    if (v.hasBVs) {
      logic.append("BV");
    }
    if (v.nonLinearArithmetic || v.linearArithmetic) {
      if (v.hasInts && v.hasReals) {
        if (v.nonLinearArithmetic) {
          logic.append("N");
        } else if (v.linearArithmetic) {
          logic.append("L");
        }
        logic.append("IRA");
      } else if (v.hasInts) {
        if (v.nonLinearArithmetic) {
          logic.append("N");
        } else if (v.linearArithmetic) {
          logic.append("L");
        }
        logic.append("IA");
      } else if (v.hasReals) {
        if (v.nonLinearArithmetic) {
          logic.append("N");
        } else if (v.linearArithmetic) {
          logic.append("L");
        }
        logic.append("RA");
      }
    }
    if (v.hasFloats) {
      // TODO forthcoming, see http://smtlib.cs.uiowa.edu/logics.shtml
      logic.append("FP");
    }
    return logic.toString();
  }

  private static final class AtomCollector extends DefaultBooleanFormulaVisitor<TraversalProcess> {

    private final Collection<BooleanFormula> atoms = new LinkedHashSet<>();
    boolean hasQuantifiers = false;

    @Override
    protected TraversalProcess visitDefault() {
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitAtom(
        BooleanFormula atom, FunctionDeclaration<BooleanFormula> funcDecl) {
      atoms.add(atom);
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitQuantifier(
        Quantifier quantifier,
        BooleanFormula quantifiedAST,
        List<Formula> boundVars,
        BooleanFormula body) {
      hasQuantifiers = true;
      return visitDefault();
    }
  }

  private final class Classifier implements FormulaVisitor<Integer> {

    boolean hasUFs = false;
    boolean hasQuantifiers = false;

    boolean hasFloats = false;
    boolean hasInts = false;
    boolean hasReals = false;
    boolean hasBVs = false;
    boolean hasArrays = false;
    boolean linearArithmetic = false;
    boolean nonLinearArithmetic = false;

    void checkType(Formula f) {
      FormulaType<Formula> type = mgr.getFormulaType(f);
      if (type.isIntegerType()) {
        hasInts = true;
      }
      if (type.isRationalType()) {
        hasReals = true;
      }
      if (type.isFloatingPointType()) {
        hasFloats = true;
      }
      if (type.isBitvectorType()) {
        hasBVs = true;
      }
      if (type.isArrayType()) {
        hasArrays = true;
      }
    }

    @Override
    public Integer visitFreeVariable(Formula pF, String pName) {
      checkType(pF);
      return 1;
    }

    @Override
    public Integer visitConstant(Formula pF, Object pValue) {
      checkType(pF);
      return 0;
    }

    @Override
    public Integer visitFunction(
        Formula pF, List<Formula> args, FunctionDeclaration<?> pFunctionDeclaration) {
      if (pFunctionDeclaration.getKind() == FunctionDeclarationKind.UF) {
        hasUFs = true;
      }
      checkType(pF);
      int numNonConstantArgs = 0;
      int allArgLevel = 0;
      for (Formula arg : args) {
        int argLevel = mgr.visit(arg, this);
        if (argLevel >= 1) {
          numNonConstantArgs++;
        }
        allArgLevel = Math.max(allArgLevel, argLevel);
      }
      switch (pFunctionDeclaration.getKind()) {
        case MUL:
        case BV_MUL:
        case DIV:
        case BV_UDIV:
        case BV_SDIV:
        case MODULO:
        case BV_UREM:
        case BV_SREM:
          if (numNonConstantArgs >= 2) {
            nonLinearArithmetic = true;
            return allArgLevel + 1;
          }
        // $FALL-THROUGH$
        default:
          if (pFunctionDeclaration.getType().isBooleanType()) {
            if (EnumSet.of(
                    FunctionDeclarationKind.LT,
                    FunctionDeclarationKind.LTE,
                    FunctionDeclarationKind.GT,
                    FunctionDeclarationKind.GTE)
                .contains(pFunctionDeclaration.getKind())) {
              for (Formula arg : args) {
                FormulaType<Formula> type = mgr.getFormulaType(arg);
                if (type.isIntegerType() || type.isRationalType()) {
                  linearArithmetic = true;
                }
              }
            }
            return 0;
          } else {
            if (pFunctionDeclaration.getKind() != FunctionDeclarationKind.UF) {
              linearArithmetic = true;
            }
            return allArgLevel;
          }
      }
    }

    @Override
    public Integer visitQuantifier(
        BooleanFormula pF,
        Quantifier pQuantifier,
        List<Formula> pBoundVariables,
        BooleanFormula pBody) {
      hasQuantifiers = true;
      checkType(pF);
      return mgr.visit(pBody, this);
    }
  }
}
