// SMT-LIB pretty-printing of formulae containing div or mod

import ap.parser._
import ap.SimpleAPI

println("starting")

val p = SimpleAPI.spawnWithAssertions
import p._
import IExpression._

val x = createConstant("x")

println(smtPP(x / 5))
println(smtPP(x / -5))
println(smtPP(-x / 5))
println(smtPP(-x / -5))
println(smtPP(x % 5))
println(smtPP(x % -5))
println(smtPP(-x % 5))
println(smtPP(-x % -5))

println(smtPP(eps(a => (a >= 0) & ((a === x) | (-a === x)))))

println("finished")
