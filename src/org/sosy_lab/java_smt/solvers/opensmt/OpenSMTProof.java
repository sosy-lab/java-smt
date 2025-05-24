/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.opensmt;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProof;

class OpenSMTProof extends AbstractProof {
  class OpenSMTProofRule implements ProofRule {
    private String name;

    OpenSMTProofRule(String pName) {
      name = pName;
    }

    @Override
    public String getName() {
      return name;
    }
  }

  class OpenSMTSubproof extends AbstractSubproof {
    protected OpenSMTSubproof(ProofRule rule, Formula formula, AbstractProof proof) {
      super(rule, formula, proof);
    }
  }

  OpenSMTSubproof generateProof(String proof, OpenSmtFormulaCreator creator) {
    Deque<OpenSMTSubproof> resNodes = new ArrayDeque<>();
    Map<String, OpenSMTSubproof> nodes = new HashMap<>();
    Deque<Object> rootStack = ProofParser.parse(ProofParser.tokenize(proof));

    Deque<Iterator<Object>> iterStack = new ArrayDeque<>();
    iterStack.push(rootStack.iterator());

    OpenSMTSubproof result = null;
    Formula formula = null;
    String formulaStr = "";

    while (!iterStack.isEmpty()) {
      Iterator<Object> currentIter = iterStack.peek();

      if (!currentIter.hasNext()) {
        iterStack.pop();
        continue;
      }

      Object exp = currentIter.next();

      if (exp instanceof String) {
        String token = (String) exp;
        switch (token) {
          case "let":
            // next element is a Deque with clause name and formula
            if (!currentIter.hasNext()) {
              throw new IllegalStateException("Expected argument after 'let'");
            }
            Object letArg = currentIter.next();
            handleLet(letArg, nodes, resNodes, creator);
            break;

          case ";":
            if (!currentIter.hasNext()) {
              throw new IllegalStateException("Expected formula string after ';'");
            }
            formulaStr = (String) currentIter.next();
            formula = creator.encapsulate(creator.getEnv().parseFormula(formulaStr));
            break;

          case "res":
            String cls1 = (String) currentIter.next();
            String cls2 = (String) currentIter.next();
            String cls3 = (String) currentIter.next();

            OpenSMTSubproof pre = resNodes.pop();
            pre.setFormula(formula);
            this.addEdge(pre, nodes.get(cls1));
            this.addEdge(pre, nodes.get(cls2));
            formula = creator.encapsulate(creator.getEnv().parseFormula(cls3));
            OpenSMTSubproof pivot =
                new OpenSMTSubproof(new OpenSMTProofRule("pivot"), formula, this);
            this.addEdge(pre, nodes.get(cls3));

            if (formulaStr.equals("-")) result = pre;

          default:
            break;
        }
      } else if (exp instanceof Deque) {
        iterStack.push(((Deque<Object>) exp).iterator());
      }
    }

    return result;
  }

  void handleLet(
      Object stack,
      Map<String, OpenSMTSubproof> nodes,
      Deque<OpenSMTSubproof> resNodes,
      OpenSmtFormulaCreator creator) {
    assert stack instanceof Deque; // no unchecked cast
    Object exp = ((Deque<?>) stack).pop();
    if (exp instanceof String) { // first element should be the assigned name
      Object v1 = ((Deque<?>) stack).peek();
      if (v1 instanceof Deque) { // then a stack with the formula
        Object v2 = ((Deque<?>) stack).peek();
        if (v2 instanceof String) {
          if (v2.equals("res")) {
            OpenSMTSubproof res = new OpenSMTSubproof(new OpenSMTProofRule("res"), null, this);
            resNodes.push(res);
            nodes.putIfAbsent((String) exp, res);
          } else {
            String formulaStr = serializeDeque((Deque<?>) v2);
            nodes.putIfAbsent(
                (String) exp,
                new OpenSMTSubproof(
                    new OpenSMTProofRule("leaf"),
                    creator.encapsulate(creator.getEnv().parseFormula(formulaStr)),
                    this));
          }
        } else {
          String formulaStr = serializeDeque((Deque<?>) v1);
          nodes.putIfAbsent(
              (String) exp,
              new OpenSMTSubproof(
                  new OpenSMTProofRule("leaf"),
                  creator.encapsulate(creator.getEnv().parseFormula(formulaStr)),
                  this));
        }
      } else if (v1 instanceof String) { // or a formula
        nodes.putIfAbsent(
            (String) exp,
            new OpenSMTSubproof(
                new OpenSMTProofRule("leaf"),
                creator.encapsulate(creator.getEnv().parseFormula((String) v1)), // this does not
                // work right now
                this));
      }
    }
  }

  private String serializeDeque(Deque<?> deque) {
    StringBuilder sb = new StringBuilder();
    serializeHelper(deque, sb);
    return sb.toString();
  }

  private void serializeHelper(Object obj, StringBuilder sb) {
    if (obj instanceof Deque) {
      sb.append("(");
      Deque<?> inner = (Deque<?>) obj;
      boolean first = true;
      for (Object o : inner) {
        if (!first) sb.append(" ");
        serializeHelper(o, sb);
        first = false;
      }
      sb.append(")");
    } else if (obj instanceof String) {
      sb.append((String) obj);
    }
  }

  static class ProofParser {
    static List<String> tokenize(String input) {
      List<String> tokens = new ArrayList<>();
      StringBuilder sb = new StringBuilder();

      for (int i = 0; i < input.length(); i++) {
        char c = input.charAt(i);

        if (Character.isWhitespace(c)) {
          if (sb.length() > 0) {
            String token = sb.toString();
            if (":core".equals(token)) {
              tokens.add(")");
              break;
            }
            tokens.add(token);
            sb.setLength(0);
          }
        } else if (c == '(' || c == ')') {
          if (sb.length() > 0) {
            String token = sb.toString();
            if (":core".equals(token)) {
              tokens.add(")");
              break;
            }
            tokens.add(token);
            sb.setLength(0);
          }
          tokens.add(Character.toString(c));
        } else {
          sb.append(c);
        }
      }

      return tokens;
    }

    static Deque<Object> parse(List<String> tokens) {
      Deque<Deque<Object>> stack = new ArrayDeque<>();
      Deque<Object> current = new ArrayDeque<>();

      for (int i = 0; i < tokens.size(); i++) {
        String token = tokens.get(i);

        if ("(".equals(token)) {
          stack.push(current);
          current = new ArrayDeque<>();
        } else if (")".equals(token)) {
          Deque<Object> completed = current;
          current = stack.pop();
          current.addLast(completed);
        } else {
          current.addLast(token);
        }
      }

      return current;
    }
  }
}
