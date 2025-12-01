/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.princess;

import static org.sosy_lab.java_smt.solvers.princess.PrincessCertificate.Certificate.BETA_CERTIFICATE;
import static org.sosy_lab.java_smt.solvers.princess.PrincessCertificate.Certificate.CLOSE_CERTIFICATE;
import static org.sosy_lab.java_smt.solvers.princess.PrincessCertificate.Certificate.CUT_CERTIFICATE;
import static org.sosy_lab.java_smt.solvers.princess.PrincessCertificate.Certificate.OMEGA_CERTIFICATE;
import static org.sosy_lab.java_smt.solvers.princess.PrincessCertificate.Certificate.SPLIT_EQ_CERTIFICATE;
import static org.sosy_lab.java_smt.solvers.princess.PrincessProofFields.*;

import ap.api.SimpleAPI;
import ap.basetypes.IdealInt;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.proof.certificates.AlphaInference;
import ap.proof.certificates.AntiSymmetryInference;
import ap.proof.certificates.BetaCertificate;
import ap.proof.certificates.BranchInference;
import ap.proof.certificates.BranchInferenceCertificate;
import ap.proof.certificates.CertEquation;
import ap.proof.certificates.CertFormula;
import ap.proof.certificates.Certificate;
import ap.proof.certificates.CloseCertificate;
import ap.proof.certificates.ColumnReduceInference;
import ap.proof.certificates.CombineEquationsInference;
import ap.proof.certificates.CombineInequalitiesInference;
import ap.proof.certificates.CutCertificate;
import ap.proof.certificates.DirectStrengthenInference;
import ap.proof.certificates.DivRightInference;
import ap.proof.certificates.GroundInstInference;
import ap.proof.certificates.MacroInference;
import ap.proof.certificates.OmegaCertificate;
import ap.proof.certificates.PartialCertificateInference;
import ap.proof.certificates.PredUnifyInference;
import ap.proof.certificates.QuantifierInference;
import ap.proof.certificates.ReduceInference;
import ap.proof.certificates.ReducePredInference;
import ap.proof.certificates.SimpInference;
import ap.proof.certificates.SplitEqCertificate;
import ap.proof.certificates.StrengthenCertificate;
import ap.proof.certificates.TheoryAxiomInference;
import ap.terfor.ConstantTerm;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofFrame;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProof;
import scala.Tuple2;
import scala.collection.immutable.Seq;
import scala.jdk.javaapi.CollectionConverters;

public final class PrincessProof extends AbstractProof {
  private static class Frame extends ProofFrame<Certificate> {
    protected Frame(Certificate proof) {
      super(proof);
    }
  }

  public PrincessProof(ProofRule pRule, @Nullable Formula pFormula) {
    super(pRule, pFormula);
  }

  public static PrincessProof buildProofDAG(
      Certificate root, PrincessFormulaCreator creator, SimpleAPI api) {
    Deque<Frame> stack = new ArrayDeque<>();

    Map<Certificate, PrincessProof> computed = new IdentityHashMap<>();

    stack.push(new Frame(root));

    while (!stack.isEmpty()) {
      Frame frame = stack.peek();

      if (!frame.isVisited()) {

        Seq<Certificate> subs = (Seq<Certificate>) frame.getProof().subCertificates();
        List<Certificate> children = CollectionConverters.asJava(subs);
        frame.setNumArgs(children.size());
        frame.setAsVisited(true);

        for (int i = children.size() - 1; i >= 0; i--) {
          Certificate child = children.get(i);
          if (!computed.containsKey(child)) {
            stack.push(new Frame(child));
          }
        }
      } else {

        stack.pop();
        // int numArgs = frame.getNumArgs();
        Certificate cert = frame.getProof();
        PrincessProof node = generateProof(cert, creator, api);

        Seq<Certificate> subs = (Seq<Certificate>) cert.subCertificates();
        List<Certificate> children = CollectionConverters.asJava(subs);

        for (Certificate c : children) {
          PrincessProof childNode = computed.get(c);
          if (childNode != null) {
            node.addChild(childNode);
          }
        }

        computed.put(cert, node);
      }
    }

    // return computed.get(root);
    throw new UnsupportedOperationException("Not yet implemented");
  }

  private static PrincessProof generateProof(
      Certificate cert, PrincessFormulaCreator creator, SimpleAPI api) {
    PrincessProof rule = handleProofCase(cert, creator, api);
    return rule;
  }

  // Helper function to store fields common to most Certificate nodes.
  private static void storeCommonFields(
      Certificate cert, PrincessCertificate rule, SimpleAPI api, PrincessFormulaCreator creator) {
    // 1) Closing constraint
    rule.specificFields.put(
        CLOSING_CONSTRAINT,
        creator.encapsulateWithTypeOf(api.asIFormula(cert.closingConstraint())));

    // 2) local assumed and assumed
    rule.specificFields.put(
        LOCAL_ASSUMED_FORMULAS,
        convertCertFormulaSet(
            CollectionConverters.asJava(cert.localAssumedFormulas()), api, creator));
    rule.specificFields.put(
        ASSUMED_FORMULAS,
        convertCertFormulaSet(CollectionConverters.asJava(cert.assumedFormulas()), api, creator));

    // 3) Provided formulas per branch
    List<Set<Formula>> encapsulatedProvidedFormulas =
        CollectionConverters.asJava(cert.localProvidedFormulas()).stream()
            .map(f -> convertCertFormulaSet(CollectionConverters.asJava(f), api, creator))
            .collect(Collectors.toList());
    rule.specificFields.put(LOCAL_PROVIDED_FORMULAS, encapsulatedProvidedFormulas);

    // 4) Local and visible constants
    rule.specificFields.put(
        LOCAL_BOUND_CONSTANTS,
        convertConstantTermSet(CollectionConverters.asJava(cert.localBoundConstants()), creator));
    rule.specificFields.put(
        CONSTANTS, convertConstantTermSet(CollectionConverters.asJava(cert.constants()), creator));

    // 5) Theory axioms
    rule.specificFields.put(
        THEORY_AXIOMS,
        convertCertFormulaSet(CollectionConverters.asJava(cert.theoryAxioms()), api, creator));
  }

  private static void storeCommonInferenceFields(
      BranchInference inf, PrincessInference rule, SimpleAPI api, PrincessFormulaCreator creator) {

    Set<CertFormula> assumedFormulas = CollectionConverters.asJava(inf.assumedFormulas());
    rule.specificFields.put(ASSUMED_FORMULAS, convertCertFormulaSet(assumedFormulas, api, creator));

    Set<CertFormula> providedFormulas = CollectionConverters.asJava(inf.providedFormulas());
    rule.specificFields.put(
        PROVIDED_FORMULAS, convertCertFormulaSet(providedFormulas, api, creator));

    Set<ConstantTerm> localBoundConstants = CollectionConverters.asJava(inf.localBoundConstants());
    rule.specificFields.put(
        LOCAL_BOUND_CONSTANTS, convertConstantTermSet(localBoundConstants, creator));

    Set<ConstantTerm> constants = CollectionConverters.asJava(inf.constants());
    rule.specificFields.put(CONSTANTS, convertConstantTermSet(constants, creator));
  }

  /**
   * Converts a Set of Princess's internal CertFormula objects into a Set of JavaSMT Formula
   * objects.
   *
   * <p>The conversion path is: CertFormula -> Conjunction -> IFormula -> JavaSMT Formula.
   */
  private static Set<Formula> convertCertFormulaSet(
      Set<CertFormula> certFormulas, SimpleAPI api, PrincessFormulaCreator creator) {
    return certFormulas.stream()
        .map(f -> creator.encapsulateWithTypeOf(api.asIFormula(f.toConj())))
        .collect(Collectors.toSet());
  }

  /**
   * Converts a List of Princess's internal CertFormula objects into a List of JavaSMT Formula
   * objects.
   *
   * <p>This method is distinct from the Set conversion because the return type is different,
   * offering clearer type safety than a highly generic single method.
   *
   * @param certFormulas The input list of CertFormula.
   * @param api The SimpleAPI instance, used to convert Conjunction to IFormula.
   * @param creator The PrincessFormulaCreator, used to encapsulate the final IFormula.
   * @return A List of JavaSMT Formula objects.
   */
  private static List<Formula> convertCertFormulaList(
      List<? extends CertFormula> certFormulas, SimpleAPI api, PrincessFormulaCreator creator) {
    return certFormulas.stream()
        .map(f -> creator.encapsulateWithTypeOf(api.asIFormula(f.toConj())))
        .collect(Collectors.toList());
  }

  /**
   * Converts a Set of Princess's internal ConstantTerm objects into a Set of JavaSMT Formula
   * objects.
   */
  private static Set<Formula> convertConstantTermSet(
      Set<ConstantTerm> constantTerms, PrincessFormulaCreator creator) {
    return constantTerms.stream()
        .map(c -> creator.encapsulateWithTypeOf(IExpression.ConstantTerm2ITerm(c)))
        .collect(Collectors.toSet());
  }

  // Converts a Scala Seq of (IdealInt, CertEquation) tuples into a Java List of Lists.
  // Each inner list contains [BigInteger, Formula], representing the pair (coefficient, equation).
  private static List<List<Object>> convertEquations(
      Seq<Tuple2<IdealInt, CertEquation>> scalaEquations,
      SimpleAPI api,
      PrincessFormulaCreator creator) {
    return CollectionConverters.asJava(scalaEquations).stream()
        .map(
            tuple -> {
              // Convert IdealInt to BigInteger
              BigInteger coeff = tuple._1().bigIntValue();

              // Convert CertEquation to Formula
              Formula equation = creator.encapsulateWithTypeOf(api.asIFormula(tuple._2().toConj()));

              // Return as a List [Coeff, Equation]
              return List.of(coeff, equation);
            })
        .collect(Collectors.toList());
  }

  public static PrincessProof handleProofCase(
      Certificate cert, PrincessFormulaCreator creator, SimpleAPI api) {
    PrincessCertificate rule;

    // BETA_CERTIFICATE
    if (cert instanceof BetaCertificate) {
      BetaCertificate betaCert = (BetaCertificate) cert;
      IFormula rightFormula = api.asIFormula(betaCert.rightFormula().toConj());
      IFormula leftFormula = api.asIFormula(betaCert.leftFormula().toConj());
      rule = new PrincessCertificate(BETA_CERTIFICATE);
      rule.specificFields.put(LEFT_FORMULA, creator.encapsulateWithTypeOf(leftFormula));
      rule.specificFields.put(RIGHT_FORMULA, creator.encapsulateWithTypeOf(rightFormula));
      rule.specificFields.put(LEMMA_FORMULA, betaCert.lemma());
    }

    // BINARY_CERTIFICATE
    // else if (cert instanceof BinaryCertificate) {
    // nothing to do, this is used for binary certificates like BetaCertificate

    // BRANCH_INFERENCE_CERTIFICATE
    else if (cert instanceof BranchInferenceCertificate) {
      return handleBranchInferenceCertificate((BranchInferenceCertificate) cert, creator, api);
    }
    // CLOSE_CERTIFICATE
    else if (cert instanceof CloseCertificate) {
      rule = new PrincessCertificate(CLOSE_CERTIFICATE);
      // No extra fields to store for CloseCertificate
    }
    // CUT_CERTIFICATE
    else if (cert instanceof CutCertificate) {
      CutCertificate cutCert = (CutCertificate) cert;
      IFormula cutFormula = api.asIFormula(cutCert.cutFormula().toConj());
      rule = new PrincessCertificate(CUT_CERTIFICATE);
      rule.specificFields.put(CUT_FORMULA, creator.encapsulateWithTypeOf(cutFormula));

    }
    // OMEGA_CERTIFICATE
    else if (cert instanceof OmegaCertificate) {
      OmegaCertificate omegaCert = (OmegaCertificate) cert;
      List<Formula> encapsulatedBoundsA =
          convertCertFormulaList(CollectionConverters.asJava(omegaCert.boundsA()), api, creator);
      List<Formula> encapsulatedBoundsB =
          convertCertFormulaList(CollectionConverters.asJava(omegaCert.boundsB()), api, creator);
      List<BigInteger> strengthenCases =
          CollectionConverters.asJava(omegaCert.strengthenCases()).stream()
              .map(IdealInt::bigIntValue)
              .collect(Collectors.toList());
      rule = new PrincessCertificate(OMEGA_CERTIFICATE);
      rule.specificFields.put(
          ELIM_CONSTANT,
          creator.encapsulateWithTypeOf(IExpression.ConstantTerm2ITerm(omegaCert.elimConst())));
      rule.specificFields.put(OMEGA_BOUNDS_A, encapsulatedBoundsA);
      rule.specificFields.put(OMEGA_BOUNDS_B, encapsulatedBoundsB);
      rule.specificFields.put(OMEGA_STRENGTHEN_CASES, strengthenCases);
    }
    // SPLIT_EQ_CERTIFICATE
    else if (cert instanceof SplitEqCertificate) {
      SplitEqCertificate seqCert = (SplitEqCertificate) cert;
      IFormula leftInEq = api.asIFormula(seqCert.leftInEq().toConj());
      IFormula rightInEq = api.asIFormula(seqCert.rightInEq().toConj());
      rule = new PrincessCertificate(SPLIT_EQ_CERTIFICATE);
      rule.specificFields.put(LEFT_INEQUALITY, creator.encapsulateWithTypeOf(leftInEq));
      rule.specificFields.put(RIGHT_INEQUALITY, creator.encapsulateWithTypeOf(rightInEq));
    }

    // STRENGTHEN_CERTIFICATE
    else if (cert instanceof StrengthenCertificate) {
      StrengthenCertificate strCert = (StrengthenCertificate) cert;
      IFormula weakInEq = api.asIFormula(strCert.weakInEq().toConj());
      rule = new PrincessCertificate(PrincessCertificate.Certificate.STRENGTHEN_CERTIFICATE);
      rule.specificFields.put(WEAK_INEQUALITY, creator.encapsulateWithTypeOf(weakInEq));
      rule.specificFields.put(EQ_CASES, strCert.eqCases().bigIntValue());
    }

    // PARTIAL_CERTIFICATE
    // else if (cert instanceof PartialCertificate) {
    //   rule = new PrincessCertificate(PrincessCertificate.Certificate.PARTIAL_CERTIFICATE);
    // }

    // Default Fallback
    else {
      throw new IllegalArgumentException(
          "Unknown proof certificate: " + cert.getClass().getSimpleName());
    }

    storeCommonFields(cert, rule, api, creator);
    return new PrincessProof(rule, null);
  }

  @SuppressWarnings("unchecked")
  public static PrincessProof handleBranchInferenceCertificate(
      BranchInferenceCertificate bic, PrincessFormulaCreator creator, SimpleAPI api) {

    // 1. Convert nested inferences into PrincessProofRule objects
    List<? extends BranchInference> externalInferences =
        CollectionConverters.asJava(bic.inferences());

    List<PrincessProofRule> wrappedInferences = new ArrayList<>();

    for (BranchInference inf : externalInferences) {
      PrincessInference infRule = null;
      // ALPHA_INFERENCE
      if (inf instanceof AlphaInference) {
        infRule = new PrincessInference(PrincessBranchCertificate.BranchInference.ALPHA_INFERENCE);
        AlphaInference ai = (AlphaInference) inf;
        Formula ecnapsulatedSplitFormula =
            creator.encapsulateWithTypeOf(api.asIFormula(ai.splitFormula().toConj()));
        infRule.specificFields.put(SPLIT_FORMULA, ecnapsulatedSplitFormula);

      }

      // ANTI_SYMMETRY_INFERENCE
      else if (inf instanceof AntiSymmetryInference) {
        infRule =
            new PrincessInference(
                PrincessBranchCertificate.BranchInference.ANTI_SYMMETRY_INFERENCE);
        AntiSymmetryInference asi = (AntiSymmetryInference) inf;
        Formula encapsulatedLeftInEq =
            creator.encapsulateWithTypeOf(api.asIFormula(asi.leftInEq().toConj()));
        Formula encapsulatedRightInEq =
            creator.encapsulateWithTypeOf(api.asIFormula(asi.rightInEq().toConj()));
        Formula encapsulatedResult =
            creator.encapsulateWithTypeOf(api.asIFormula(asi.result().toConj()));
        infRule.specificFields.put(LEFT_INEQUALITY, encapsulatedLeftInEq);
        infRule.specificFields.put(RIGHT_INEQUALITY, encapsulatedRightInEq);
        infRule.specificFields.put(RESULT, encapsulatedResult);

      }

      // COLUMN_REDUCE_INFERENCE
      else if (inf instanceof ColumnReduceInference) {
        infRule =
            new PrincessInference(
                PrincessBranchCertificate.BranchInference.COLUMN_REDUCE_INFERENCE);
        ColumnReduceInference cri = (ColumnReduceInference) inf;
        Formula encapsulatedOldSymbol =
            creator.encapsulateWithTypeOf(IExpression.ConstantTerm2ITerm(cri.oldSymbol()));
        Formula encapsulatedNewSymbol =
            creator.encapsulateWithTypeOf(IExpression.ConstantTerm2ITerm(cri.newSymbol()));
        Formula encapsulatedDefiningEquation =
            creator.encapsulateWithTypeOf(api.asIFormula(cri.definingEquation().toConj()));
        infRule.specificFields.put(OLD_SYMBOL, cri.oldSymbol());
        infRule.specificFields.put(NEW_SYMBOL, cri.newSymbol());
        infRule.specificFields.put(DEFINING_EQUATION, cri.definingEquation());
        infRule.specificFields.put(SUBST, cri.subst());

      }

      // COMBINE_EQUATIONS_INFERENCE
      else if (inf instanceof CombineEquationsInference) {
        infRule =
            new PrincessInference(
                PrincessBranchCertificate.BranchInference.COMBINE_EQUATIONS_INFERENCE);
        CombineEquationsInference cei = (CombineEquationsInference) inf;
        List<List<Object>> convertedEquations = convertEquations(cei.equations(), api, creator);
        Formula encapsulatedResult =
            creator.encapsulateWithTypeOf(api.asIFormula(cei.result().toConj()));
        infRule.specificFields.put(EQUATIONS, convertedEquations);
        infRule.specificFields.put(RESULT, encapsulatedResult);
      }

      // COMBINE_INEQUALITIES_INFERENCE
      else if (inf instanceof CombineInequalitiesInference) {
        infRule =
            new PrincessInference(
                PrincessBranchCertificate.BranchInference.COMBINE_INEQUALITIES_INFERENCE);
        CombineInequalitiesInference cii = (CombineInequalitiesInference) inf;
        Formula encapsulatedLeftInEq =
            creator.encapsulateWithTypeOf(api.asIFormula(cii.leftInEq().toConj()));
        Formula encapsulatedRightInEq =
            creator.encapsulateWithTypeOf(api.asIFormula(cii.rightInEq().toConj()));
        Formula encapsulatedResult =
            creator.encapsulateWithTypeOf(api.asIFormula(cii.result().toConj()));
        infRule.specificFields.put(LEFT_COEFFICIENT, cii.leftCoeff().bigIntValue());
        infRule.specificFields.put(LEFT_INEQUALITY, encapsulatedLeftInEq);
        infRule.specificFields.put(RIGHT_COEFFICIENT, cii.rightCoeff().bigIntValue());
        infRule.specificFields.put(RIGHT_INEQUALITY, encapsulatedRightInEq);
        infRule.specificFields.put(RESULT, encapsulatedResult);

      }

      // DIRECT_STRENGTHEN_INFERENCE
      else if (inf instanceof DirectStrengthenInference) {
        infRule =
            new PrincessInference(
                PrincessBranchCertificate.BranchInference.DIRECT_STRENGTHEN_INFERENCE);
        DirectStrengthenInference dsi = (DirectStrengthenInference) inf;
        Formula encapsulatedInequality =
            creator.encapsulateWithTypeOf(api.asIFormula(dsi.inequality().toConj()));
        Formula encapsulatedEquation =
            creator.encapsulateWithTypeOf(api.asIFormula(dsi.equation().toConj()));
        Formula encapsulatedResult =
            creator.encapsulateWithTypeOf(api.asIFormula(dsi.result().toConj()));
        infRule.specificFields.put(INEQUALITY, encapsulatedInequality);
        infRule.specificFields.put(EQUATION, encapsulatedEquation);
        infRule.specificFields.put(RESULT, encapsulatedResult);

      }

      // DIV_RIGHT_INFERENCE
      else if (inf instanceof DivRightInference) {
        infRule =
            new PrincessInference(PrincessBranchCertificate.BranchInference.DIV_RIGHT_INFERENCE);
        DivRightInference dri = (DivRightInference) inf;
        Formula encapsulatedDivisibility =
            creator.encapsulateWithTypeOf(api.asIFormula(dri.divisibility().toConj()));
        Formula encapsulatedResult =
            creator.encapsulateWithTypeOf(api.asIFormula(dri.result().toConj()));
        infRule.specificFields.put(DIVISIBILITY, dri.divisibility());
        infRule.specificFields.put(RESULT, dri.result());

      }

      // GROUND_INST_INFERENCE
      else if (inf instanceof GroundInstInference) {
        infRule =
            new PrincessInference(PrincessBranchCertificate.BranchInference.GROUND_INST_INFERENCE);
        GroundInstInference gi = (GroundInstInference) inf;
        Formula encapsulatedQuantifiedFormula =
            creator.encapsulateWithTypeOf(api.asIFormula(gi.quantifiedFormula().toConj()));
        Formula encapsulatedInstanceFormula =
            creator.encapsulateWithTypeOf(api.asIFormula(gi.instance().toConj()));
        Formula encapsulatedResult =
            creator.encapsulateWithTypeOf(api.asIFormula(gi.result().toConj()));
        infRule.specificFields.put(QUANTIFIED_FORMULA, encapsulatedQuantifiedFormula);
        // TODO: Transform LinearCombination objects into JavaSMT objects
        infRule.specificFields.put(INSTANCE_TERMS, CollectionConverters.asJava(gi.instanceTerms()));
        infRule.specificFields.put(INSTANCE_FORMULA, encapsulatedInstanceFormula);
        infRule.specificFields.put(
            DISCHARGED_ATOMS, CollectionConverters.asJava(gi.dischargedAtoms()));
        infRule.specificFields.put(RESULT, encapsulatedResult);
      }

      // MACRO_INFERENCE
      else if (inf instanceof MacroInference) {
        // No fields to store
      }

      // PARTIAL_CERTIFICATE_INFERENCE
      else if (inf instanceof PartialCertificateInference) {
        infRule =
            new PrincessInference(
                PrincessBranchCertificate.BranchInference.PARTIAL_CERTIFICATE_INFERENCE);
        PartialCertificateInference pci = (PartialCertificateInference) inf;
        infRule.specificFields.put(PARTIAL_CERTIFICATE, pci.pCert());

      }

      // PRED_UNIFY_INFERENCE
      else if (inf instanceof PredUnifyInference) {
        infRule =
            new PrincessInference(PrincessBranchCertificate.BranchInference.PRED_UNIFY_INFERENCE);
        PredUnifyInference pu = (PredUnifyInference) inf;
        infRule.specificFields.put(LEFT_ATOM, pu.leftAtom());
        infRule.specificFields.put(RIGHT_ATOM, pu.rightAtom());
        infRule.specificFields.put(RESULT, pu.result());
        infRule.specificFields.put(
            PROVIDED_FORMULAS, CollectionConverters.asJava(pu.providedFormulas()));

      }

      // QUANTIFIER_INFERENCE
      else if (inf instanceof QuantifierInference) {
        infRule =
            new PrincessInference(PrincessBranchCertificate.BranchInference.QUANTIFIER_INFERENCE);
        QuantifierInference qi = (QuantifierInference) inf;
        infRule.specificFields.put(QUANTIFIED_FORMULA, qi.quantifiedFormula());
        infRule.specificFields.put(NEW_CONSTANTS, CollectionConverters.asJava(qi.newConstants()));
        infRule.specificFields.put(RESULT, qi.result());

      }

      // REDUCE_INFERENCE
      else if (inf instanceof ReduceInference) {
        infRule = new PrincessInference(PrincessBranchCertificate.BranchInference.REDUCE_INFERENCE);
        ReduceInference ri = (ReduceInference) inf;
        infRule.specificFields.put(EQUATIONS, CollectionConverters.asJava(ri.equations()));
        infRule.specificFields.put(TARGET_LITERAL, ri.targetLit());
        infRule.specificFields.put(RESULT, ri.result());

      }

      // REDUCE_PRED_INFERENCE
      else if (inf instanceof ReducePredInference) {
        infRule =
            new PrincessInference(PrincessBranchCertificate.BranchInference.REDUCE_PRED_INFERENCE);
        ReducePredInference rpi = (ReducePredInference) inf;
        infRule.specificFields.put(EQUATIONS, CollectionConverters.asJava(rpi.equations()));
        infRule.specificFields.put(TARGET_LITERAL, rpi.targetLit());
        infRule.specificFields.put(RESULT, rpi.result());

      }

      // SIMP_INFERENCE
      else if (inf instanceof SimpInference) {
        infRule = new PrincessInference(PrincessBranchCertificate.BranchInference.SIMP_INFERENCE);
        SimpInference si = (SimpInference) inf;
        infRule.specificFields.put(TARGET_LITERAL, si.targetLit());
        infRule.specificFields.put(RESULT, si.result());

      }

      // THEORY_AXIOM_INFERENCE
      else if (inf instanceof TheoryAxiomInference) {
        infRule =
            new PrincessInference(PrincessBranchCertificate.BranchInference.THEORY_AXIOM_INFERENCE);
        TheoryAxiomInference tai = (TheoryAxiomInference) inf;
        infRule.specificFields.put(THEORY, tai.theory());
        infRule.specificFields.put(AXIOM, tai.axiom());

      } else {
        throw new IllegalArgumentException(
            String.format(
                Locale.ROOT, "Unknown branch inference: %s", inf.getClass().getSimpleName()));
      }

      wrappedInferences.add(infRule);
    }

    // 2. Create the container rule
    PrincessBranchCertificate containerRule = new PrincessBranchCertificate(wrappedInferences);

    // 3. Store common fields for the container certificate itself
    storeCommonFields(bic, containerRule, api, creator);

    return new PrincessProof(containerRule, null);
  }
}
