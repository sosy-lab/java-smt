package org.sosy_lab.java_smt.solvers.bdd;



import com.microsoft.z3.FuncDecl;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.bdd.BddFormula.BddBooleanFormula;
import org.sosy_lab.java_smt.solvers.bdd.BddSort.BddBooleanSort;



abstract class BddFormulaCreator
    extends FormulaCreator<Region, BddSort, NamedRegionManager, FuncDecl> {

  // private final BiMap<String, Region> cache = HashBiMap.create();

  protected BddFormulaCreator(
      NamedRegionManager pEnv,
      BddSort pBoolType) {
    super(pEnv, pBoolType, null, null);
  }

  @Override
  public Region makeVariable(BddSort sort, String varName) {
    if (sort == BddBooleanSort.getInstance()) {
      /*
       * Region result = cache.get(varName); if (result == null) { result =
       * getEnv().createPredicate(); cache.put(varName, result); } return result;
       */
      return getEnv().createPredicate(varName);

    } else {
      throw new AssertionError("implement later");
    }
  }

  // @Override
  @Override
  public Region extractInfo(Formula pT) {
    if (pT instanceof BddBooleanFormula) {
      return ((BddBooleanFormula) pT).getRegion();
      }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + "in Bdd");
    }


    @Override
    @SuppressWarnings("unchecked")
    public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    final FormulaType<?> t;
      if (formula instanceof BooleanFormula) {
        t=FormulaType.BooleanType;
    } else {
      throw new IllegalArgumentException("Formula with unexpected type" + formula.getClass());
    }
    return (FormulaType<T>) t;
    }

  @Override
  public FormulaType<?> getFormulaType(Region pFormula) {
        return FormulaType.BooleanType;
  }


    @Override
    protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Region pTerm,
      FormulaType<TI> pIndexType,
      FormulaType<TE> pElementType) {
      assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType));
    throw new IllegalArgumentException("Cannot create formulas of type in Bdd");
    }

    @Override
    protected <TI extends Formula, TE extends Formula> FormulaType<TE> getArrayFormulaElementType(
        ArrayFormula<TI, TE> pArray) {
    throw new IllegalArgumentException("Cannot create formulas of type in Bdd");

    }

    @Override
    protected <TI extends Formula, TE extends Formula> FormulaType<TI> getArrayFormulaIndexType(
        ArrayFormula<TI, TE> pArray) {
    throw new IllegalArgumentException("Cannot create formulas of type in Bdd");

    }



}


