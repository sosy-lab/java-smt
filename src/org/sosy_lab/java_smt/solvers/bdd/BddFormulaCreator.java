package org.sosy_lab.java_smt.solvers.bdd;



import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.microsoft.z3.FuncDecl;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;


abstract class BddFormulaCreator extends FormulaCreator<Region, BddSort, RegionManager, FuncDecl> {

  private final BddBooleanSort booltype;
  private final RegionManager environment;
  private final BiMap<String, Region> names = HashBiMap.create();

  // TODO contructor parameter?
  protected BddFormulaCreator(
      BddBooleanSort pBool,
      RegionManager pEnv) {
    super(pEnv, pBool, null, null);
  }

  // TODO: hashbimap
  @Override
  public Region makeVariable(BddSort type, String name) {
    return null;
  }


  @Override
  public Region extractInfo(Formula pT) {
      if(pT instanceof BooleanFormula) {
      return ((BooleanFormula) pT).getFormulaInfo();
      }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + "in Bdd");
    }


    @SuppressWarnings("unchecked")
    @Override
    public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
      FormulaType<?> t;
      if (formula instanceof BooleanFormula) {
        t=FormulaType.BooleanType;
    } else if (formula instanceof BitvectorFormula) {
      // TODO how to get the size of a formula?
      t = FormulaType.getBitvectorTypeWithSize(0);
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


