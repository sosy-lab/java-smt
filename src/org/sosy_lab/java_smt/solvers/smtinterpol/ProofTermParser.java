package org.sosy_lab.java_smt.solvers.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.ResolutionProofDag;
import org.sosy_lab.java_smt.ResolutionProofDag.AxiomProofNode;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.proofs.ProofNode;

// TODO: Correct parsing of the proof terms is missing, i.e. creation of nodes in the DAG and
// parsing annotations. Add relevant javadocs
@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access"})
public class ProofTermParser {

  private final ResolutionProofDag proofDag;
  private final Map<String, BooleanFormula> annotatedTerms;
  private final Map<String, Term> letBindings = new HashMap<>();
  private final Map<Term, ProofNode> termToNode = new HashMap<>();
  private final FormulaManager mgr;

  public ProofTermParser(Map<String, BooleanFormula> pAnnotatedTerms, FormulaManager pMgr) {
    annotatedTerms = pAnnotatedTerms;
    mgr = pMgr;
    proofDag = new ResolutionProofDag();
  }

  public static ResolutionProofDag convert(
      Term proof, FormulaManager pManager, Map<String, BooleanFormula> pAnnotatedTerms) {
    ProofTermParser parser = new ProofTermParser(pAnnotatedTerms, pManager);
    ProofNode rootNode = parser.parseProofTerm(proof);
    if (rootNode != null) {
      parser.proofDag.addNode(rootNode);
    }
    return parser.proofDag;
  }

  public ProofNode parseProofTerm(Term term) {
    if (termToNode.containsKey(term)) {
      return termToNode.get(term);
    }

    ProofNode node = null;

    if (term instanceof AnnotatedTerm) {
      node = parseAnnotatedTerm((AnnotatedTerm) term);
    } else if (term instanceof ApplicationTerm) {
      node = parseApplicationTerm((ApplicationTerm) term);
    } else if (term instanceof LetTerm) {
      node = parseLetTerm((LetTerm) term);
    }

    if (node != null) {
      termToNode.put(term, node);
    }

    return node;
  }

  private ProofNode parseAnnotatedTerm(AnnotatedTerm term) {
    for (Annotation annotation : term.getAnnotations()) {
      if (annotation.getKey().equals(":proves")
          || annotation.getKey().equals(":rup")
          || annotation.getKey().equals(":input")) {
        Term formulaTerm = extractFormulaFromAnnotation(annotation);
        BooleanFormula formula = getBooleanFormulaFromTerm(formulaTerm);
        ProofNode node = createSourceNode(ResAxiom.RESOLUTION, formula);
        return node;
      }
    }
    return parseProofTerm(term.getSubterm());
  }

  private ProofNode parseApplicationTerm(ApplicationTerm term) {
    String funcName = term.getFunction().getName();
    Term[] params = term.getParameters();

    if (funcName.equals("..res") && params.length >= 3) {
      Term clauseTerm = params[0];
      BooleanFormula formula = getBooleanFormulaFromTerm(clauseTerm);
      ProofNode resNode = createSourceNode(ResAxiom.RESOLUTION, formula);

      for (int i = 1; i < params.length; i++) {
        ProofNode childNode = parseProofTerm(params[i]);
        if (childNode != null) {
          proofDag.addEdge(resNode.getId(), childNode.getId());
        }
      }
      return resNode;
    } else if (funcName.equals("..assume") && params.length > 0) {
      Term assumedFormula = params[0];
      BooleanFormula formula = getBooleanFormulaFromTerm(assumedFormula);
      return createSourceNode(ResAxiom.ASSUME, formula);
    } else if (funcName.equals("..axiom") && params.length > 0) {
      Term axiomFormula = params[0];
      BooleanFormula formula = getBooleanFormulaFromTerm(axiomFormula);
      ResAxiom axiomType = inferAxiomType(funcName, params);
      return createSourceNode(axiomType, formula);
    } else if (funcName.startsWith("@")) {
      String lemmaType = funcName.substring(1);
      ResAxiom axiomType = mapTheoryLemmaToAxiom(lemmaType);

      if (params.length > 0) {
        Term lemmaFormula = params[0];
        BooleanFormula formula = getBooleanFormulaFromTerm(lemmaFormula);
        return createSourceNode(axiomType, formula);
      }
    }

    ProofNode lastNode = null;
    for (Term param : params) {
      lastNode = parseProofTerm(param);
    }

    return lastNode;
  }

  private ProofNode parseLetTerm(LetTerm term) {
    Map<String, Term> oldBindings = new HashMap<>(letBindings);
    TermVariable[] vars = term.getVariables();
    Term[] values = term.getValues();

    for (int i = 0; i < vars.length; i++) {
      letBindings.put(vars[i].getName(), values[i]);
    }

    ProofNode result = parseProofTerm(term.getSubTerm());
    letBindings.clear();
    letBindings.putAll(oldBindings);

    return result;
  }

  private Term extractFormulaFromAnnotation(Annotation annotation) {
    Object value = annotation.getValue();
    if (value instanceof Term) {
      return (Term) value;
    }
    return null;
  }

  private String extractName(Term term) {
    if (term instanceof AnnotatedTerm) {
      for (Annotation annot : ((AnnotatedTerm) term).getAnnotations()) {
        if (":named".equals(annot.getKey())) {
          return annot.getValue().toString();
        }
      }
    }
    return null;
  }

  private BooleanFormula getBooleanFormulaFromTerm(Term term) {
    String name = extractName(term);
    if (name != null && annotatedTerms.containsKey(name)) {
      return annotatedTerms.get(name);
    }
    return ((SmtInterpolFormulaManager) mgr).encapsulateBooleanFormula(term);
  }

  private ProofNode createSourceNode(ResAxiom rule, BooleanFormula formula) {
    ProofNode node = new AxiomProofNode(rule, formula);
    proofDag.addNode(node);
    return node;
  }

  private ResAxiom inferAxiomType(String funcName, Term[] params) {
    return ResAxiom.RESOLUTION;
  }

  private ResAxiom mapTheoryLemmaToAxiom(String lemmaType) {
    switch (lemmaType) {
      case "equalsTransitive":
        return ResAxiom.TRANSITIVITY;
      case "equalsSymmetric":
        return ResAxiom.SYMMETRY;
      case "equalsReflexive":
        return ResAxiom.REFLEXIVITY;
      case "distinctNegation":
        return ResAxiom.DISTINCT_NEGATIVE;
      case "store":
        return ResAxiom.SELECTSTORE1;
      case "select":
        return ResAxiom.SELECTSTORE2;
      default:
        return ResAxiom.RESOLUTION;
    }
  }
}
