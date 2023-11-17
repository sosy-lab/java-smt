// A case that previously led to an exception

import ap.parser._
import ap.SimpleAPI

println("starting")

val p = SimpleAPI.spawnWithAssertions
import p._

val x = createBooleanVariable

push

???

println("x")
println(partialModel)
println("y")

!! (x)
???              // here we got an exception

println("finished")
