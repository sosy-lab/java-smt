// A test case corresponding to onlyUnitResolution/adt-totality.pri.
// Previously, this input led to non-termination, because the totality axiom
// for f did not include range constraints about the function result.

import ap._
import ap.parser._

SimpleAPI.withProver(enableAssert = true, genTotalityAxioms = true) { p =>
import p._
import IExpression._

val s : Sort = 0 to 1
val f = createFunction("f", List(s), s)

!! (s.all(x => f(x) =/= x))
?? (s.ex(x => f(x) === 1))

println(???)

}
