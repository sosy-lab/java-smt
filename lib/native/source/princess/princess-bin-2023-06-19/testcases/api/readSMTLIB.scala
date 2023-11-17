import ap._
import ap.parser._

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._

scope {
val x = createConstant("x")
!! (x < 100)

// read a file that includes symbol definitions
val Seq(f) = extractSMTLIBAssertions(new java.io.FileReader("testfile.smt2"))
println(pp(f))

!! (f)
println(???) // sat

!! (x < 50)
println(???) // unsat
}

scope {
val x = createConstant("x")
val y = createConstant("y")
!! (x < 100)

// read a file without symbol definitions
val Seq(f) = extractSMTLIBAssertions(new java.io.FileReader("testfile2.smt2"))
println(pp(f))

!! (f)
println(???) // sat

!! (x < 50)
println(???) // unsat
}

scope {
// read a file that includes symbol definitions and some other commands
// that should be ignored
val Seq(f) = extractSMTLIBAssertions(new java.io.FileReader("testfile3.smt2"))
println(pp(f))
}
}
