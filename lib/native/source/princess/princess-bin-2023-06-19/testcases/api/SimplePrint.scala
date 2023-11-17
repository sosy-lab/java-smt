// Some simple tests for pretty-printing of formulas

import ap.parser._

ap.util.Debug.enableAllAssertions(true)

val f = (IIntLit(1) >= IIntLit(0))

println(f)
SMTLineariser(f)
println
