import ap.SimpleAPI
import ap.parser._

object Hi {
  def main(args: Array[String]) =
    SimpleAPI.withProver { p =>
      import p._
      import IExpression._

      val x = createBooleanVariables(801)
      val y = createBooleanVariables(801)

      for (i <- 0 until 800) {
        push
        !! (x(i) <=> x(i+1))
        !! (y(i) <=> y(i+1))
        !! (x(i) <=> y(i))
      }

      withTimeout(30000) {
        println(???)
      }
//      println(partialModel)
  }
}
