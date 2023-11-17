// Simplification of formulas containing predicates

import ap.parser._
import ap.SimpleAPI
import IExpression._

println("starting")

val p = SimpleAPI.spawnWithAssertions
import p._

val c = createConstant("c")
val q = createBooleanVariable("p")

val g1 = all(x => (c === ite(q, x, 4)))
println(pp(simplify(g1)))
val g2 = ex(x => (c === ite(q, x, 4)))
println(pp(simplify(g2)))

println("finished")