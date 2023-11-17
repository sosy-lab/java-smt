// Check that incrementally added formulae are handled
// correctly, even if formulae are eliminated from the proof

import ap.parser._
import IExpression._
import ap.SimpleAPI

println("starting")

val p = SimpleAPI.spawnWithAssertions
import p._

val a = createBooleanVariable("a")
val x = createConstant("x")
val y = createConstant("y")
val z = createConstant("z")

!! (a <=> (x > 1))
!! (x === y + 1)
!! (z === x + 3)

println(???)
println(partialModel)

scope {
  !! (a)

  println(???)
  println(partialModel)
}

println(???)

scope {
  !! (z === 5)

  println(???)
  println(partialModel)
}

println("finished")
