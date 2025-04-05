// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Table;
import com.google.common.collect.Table.Cell;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Command;
import io.github.cvc5.InputParser;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.SymbolManager;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import io.github.cvc5.modes.InputLanguage;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.Tokenizer;

class CVC5FormulaManager extends AbstractFormulaManager<Term, Sort, TermManager, Term> {

  private final CVC5FormulaCreator creator;

  @SuppressWarnings("checkstyle:parameternumber")
  CVC5FormulaManager(
      CVC5FormulaCreator pFormulaCreator,
      CVC5UFManager pFfmgr,
      CVC5BooleanFormulaManager pBfmgr,
      CVC5IntegerFormulaManager pIfmgr,
      CVC5RationalFormulaManager pRfmgr,
      CVC5BitvectorFormulaManager pBvfmgr,
      CVC5FloatingPointFormulaManager pFpfmgr,
      CVC5QuantifiedFormulaManager pQfmgr,
      CVC5ArrayFormulaManager pAfmgr,
      CVC5SLFormulaManager pSLfmgr,
      CVC5StringFormulaManager pStrmgr,
      CVC5EnumerationFormulaManager pEfmgr) {
    super(
        pFormulaCreator,
        pFfmgr,
        pBfmgr,
        pIfmgr,
        pRfmgr,
        pBvfmgr,
        pFpfmgr,
        pQfmgr,
        pAfmgr,
        pSLfmgr,
        pStrmgr,
        pEfmgr);
    creator = pFormulaCreator;
  }

  static Term getCVC5Term(Formula pT) {
    if (pT instanceof CVC5Formula) {
      return ((CVC5Formula) pT).getTerm();
    }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + " in the Solver!");
  }

  @Override
  public Term parseImpl(String formulaStr) throws IllegalArgumentException {
    // Split the input string into a list of SMT-LIB2 commands
    List<String> tokens = Tokenizer.tokenize(formulaStr);

    Table<String, Sort, Term> cache = creator.getDeclaredVariables();

    // Process the declarations
    Map<String, Sort> localSymbols = new HashMap<>();
    ImmutableList.Builder<String> processed = ImmutableList.builder();
    for (String token : tokens) {
      if (Tokenizer.isDeclarationToken(token)) {
        // Parse the variable/UF declaration to get a name
        Solver solver = new Solver(getEnvironment());
        InputParser parser = new InputParser(solver);
        SymbolManager symbolManager = new SymbolManager(getEnvironment());
        parser.setStringInput(InputLanguage.SMT_LIB_2_6, "(set-logic ALL)" + token, "");
        parser.nextCommand().invoke(solver, symbolManager);
        parser.nextCommand().invoke(solver, symbolManager);

        Term parsed = symbolManager.getDeclaredTerms()[0];

        String symbol = parsed.getSymbol();
        if (symbol.startsWith("|") && symbol.endsWith("|")) {
          // Strip quotes from the name
          symbol = symbol.substring(1, symbol.length() - 1);
        }
        Sort sort = parsed.getSort();

        // Check if the symbol is already defined in the variable cache
        if (cache.containsRow(symbol)) {
          Sort typeDefinition = cache.row(symbol).keySet().toArray(new Sort[0])[0];
          Preconditions.checkArgument(
              cache.contains(symbol, sort),
              "Symbol '%s' is already used by the solver with a different type. The new type is "
                  + "%s, but we already have a definition with type %s.",
              symbol,
              sort,
              typeDefinition);
          continue; // Skip if it's a redefinition
        }

        // Check if it collides with a definition that was parsed earlier
        Preconditions.checkArgument(
            !localSymbols.containsKey(symbol) || localSymbols.get(symbol).equals(sort),
            "Symbol '%s' has already been defined by this script with a different type. The new "
                + "type is %s, but we have already a definition with type %s.",
            symbol,
            sort,
            localSymbols.get(symbol));

        // Add the symbol to the local definitions for this parse
        localSymbols.put(symbol, sort);
      }
      // Otherwise, keep the command
      processed.add(token);
    }

    // Build SMT-LIB2 declarations for all variables in the cache
    ImmutableList.Builder<String> builder = ImmutableList.builder();
    for (Cell<String, Sort, Term> c : cache.cellSet()) {
      String symbol = c.getValue().toString();
      List<Sort> args = ImmutableList.of();
      Sort sort = c.getValue().getSort();

      if (sort.isFunction()) {
        args = List.of(sort.getFunctionDomainSorts());
        sort = sort.getFunctionCodomainSort();
      }
      StringBuilder decl = new StringBuilder();
      decl.append("(declare-fun").append(" ");
      decl.append(symbol).append(" ");
      decl.append("(");
      for (Sort p : args) {
        decl.append(p).append(" ");
      }
      decl.append(")").append(" ");
      decl.append(sort);
      decl.append(")");

      builder.add(decl.toString());
    }

    String decls = String.join("\n", builder.build());
    String input = String.join("\n", processed.build());

    // Add the declarations to the input and parse everything
    Solver solver = new Solver(getEnvironment());
    InputParser parser = new InputParser(solver);
    SymbolManager symbolManager = parser.getSymbolManager();
    parser.setStringInput(InputLanguage.SMT_LIB_2_6, "(set-logic ALL)" + decls + input, "");

    Command cmd = parser.nextCommand();
    while (!cmd.isNull()) {
      try {
        Preconditions.checkArgument(
            ImmutableList.of("set-logic", "declare-fun", "declare-const", "define-fun", "assert")
                .contains(cmd.getCommandName()),
            "Command %s is not supported",
            cmd.getCommandName());
        cmd.invoke(solver, symbolManager);
        cmd = parser.nextCommand();
      } catch (Throwable e) {
        throw new IllegalArgumentException(e);
      }
    }

    // Get the assertions from the input
    Term[] asserted = solver.getAssertions();
    Term result = asserted.length == 1 ? asserted[0] : getEnvironment().mkTerm(Kind.AND, asserted);

    // Now get all declared symbols
    Term[] declared = symbolManager.getDeclaredTerms();

    // Check that all variables/UF have a single type signature
    // The CVC5 parser allows polymorphic types, but we don't support them in JavaSMT
    Set<String> duplicates =
        Arrays.stream(declared)
            .collect(Collectors.groupingBy(Term::getSymbol, Collectors.counting()))
            .entrySet()
            .stream()
            .filter(m -> m.getValue() > 1)
            .map(Entry::getKey)
            .collect(Collectors.toSet());
    Preconditions.checkArgument(
        duplicates.isEmpty(),
        "Parsing failed as there were multiple conflicting definitions for the symbol(s) '%s'",
        duplicates);

    // Process the symbols from the parser
    Map<Term, Term> subst = new HashMap<>();
    for (Term term : declared) {
      String symbol = term.getSymbol();
      if (symbol.startsWith("|") && symbol.endsWith("|")) {
        // Strip quotes from the name
        symbol = symbol.substring(1, symbol.length() - 1);
      }
      if (cache.containsRow(symbol)) {
        // Symbol is from the context: add the original term to the substitution map
        subst.put(term, cache.get(symbol, term.getSort()));
      } else {
        // Symbol is new, add it to the context
        cache.put(symbol, term.getSort(), term);
      }
    }

    // Substitute all symbols from the context with their original terms
    return result.substitute(
        subst.keySet().toArray(new Term[0]), subst.values().toArray(new Term[0]));
  }

  @Override
  public String dumpFormulaImpl(Term f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    StringBuilder out = new StringBuilder();
    // get all symbols
    final Map<String, Term> allVars = new LinkedHashMap<>();
    creator.extractVariablesAndUFs(f, true, allVars::put);

    // print all symbols
    for (Map.Entry<String, Term> entry : allVars.entrySet()) {
      String name = entry.getKey();
      Term var = entry.getValue();

      // escaping is stolen from SMTInterpol, lets hope this remains consistent
      out.append("(declare-fun ").append(PrintTerm.quoteIdentifier(name)).append(" (");

      // add function parameters
      Iterable<Sort> childrenTypes;
      try {
        if (var.getSort().isFunction() || var.getKind() == Kind.APPLY_UF) {
          childrenTypes = Iterables.skip(Iterables.transform(var, Term::getSort), 1);
        } else {
          childrenTypes = Iterables.transform(var, Term::getSort);
        }
      } catch (CVC5ApiException e) {
        childrenTypes = Iterables.transform(var, Term::getSort);
      }
      out.append(Joiner.on(" ").join(childrenTypes));

      // and return type
      out.append(") ").append(var.getSort().toString()).append(")\n");
    }

    // now add the final assert
    out.append("(assert ");
    // Formerly in CVC4:
    // f.toString() does expand all nested sub-expressions and causes exponential overhead.
    // f.toStream() uses LET-expressions and is exactly what we want.
    // However, in CVC5 toStream() does no longer exists.
    // TODO: either toString() will do, or we may need iterator().
    /*
    try (OutputStream stream =
        new OutputStream() {

          @Override
          public void write(int chr) throws IOException {
            out.append((char) chr);
          }
        }) {
      f.toStream(stream);
    }
    */
    out.append(f.toString());
    out.append(')');
    return out.toString();
  }

  @Override
  public <T extends Formula> T substitute(
      final T f, final Map<? extends Formula, ? extends Formula> fromToMapping) {
    Term[] changeFrom = new Term[fromToMapping.size()];
    Term[] changeTo = new Term[fromToMapping.size()];
    int idx = 0;
    for (Map.Entry<? extends Formula, ? extends Formula> e : fromToMapping.entrySet()) {
      changeFrom[idx] = extractInfo(e.getKey());
      changeTo[idx] = extractInfo(e.getValue());
      idx++;
    }
    Term input = extractInfo(f);
    FormulaType<T> type = getFormulaType(f);
    return getFormulaCreator().encapsulate(type, input.substitute(changeFrom, changeTo));
  }
}
