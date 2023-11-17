import ap._
import ap.parser._
import ap.types.Sort.MultipleValueBool

SimpleAPI.withProver(enableAssert = true) { p =>
  import p._
  import IExpression._

  scope {
    SMTLineariser(MultipleValueBool.True === IIntLit(0))
    println
    SMTLineariser(MultipleValueBool.False === IIntLit(0))
    println
    SMTLineariser(MultipleValueBool.True === IIntLit(1))
    println
    SMTLineariser(MultipleValueBool.False === IIntLit(1))
    println
    SMTLineariser(IIntLit(0) === MultipleValueBool.True)
    println
    SMTLineariser(IIntLit(0) === MultipleValueBool.False)
    println
    SMTLineariser(IIntLit(1) === MultipleValueBool.True)
    println
    SMTLineariser(IIntLit(1) === MultipleValueBool.False)
    println
  }
}