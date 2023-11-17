import ap._
import ap.parser._

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._

// calling eval without previously pushing any formulas previously
// led to an exception

val x = createConstant
println(???)
println(eval(x))

}