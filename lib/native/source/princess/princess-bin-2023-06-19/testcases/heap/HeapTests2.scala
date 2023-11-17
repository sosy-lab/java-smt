import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.parameters.Param.InputFormat
import ap.types._
import ap.parser._
import ap.theories.{ADT, Heap}
import ap.util.Debug

class PrincessTester (p : SimpleAPI) {
  import p._

  var testCaseCounter = 1;

  private def expect[A](x : A, expected : A) : (A, Boolean) = {
    println(x)
    (x, x == expected)
  }

  abstract sealed class TestStep (val fs : IFormula*)
  case class SatStep(override val fs : IFormula*) extends TestStep
  case class UnsatStep(override val fs : IFormula*) extends TestStep
  case class CommonAssert (override val fs : IFormula*) extends TestStep

  private def printModel {
    val newLine = "\n" + " "*2
    println {"Model:" + newLine +
             (for ((l, v) <- partialModel.interpretation.iterator)
               yield {
                 l + " -> " + v
               }).mkString(newLine)
    }
  }

  private def justAssert(s : TestStep) = {
    for (f <- s.fs) {
      addAssertion(f)
      print("  ")
      PrincessLineariser printExpression f
      println
    }
  }

  private def executeStep(ps : ProverStatus.Value, s : TestStep) : Boolean = {
    var res = false
    scope {
      for (f <- s.fs) {
        addAssertion(f)
        print("  ")
        PrincessLineariser printExpression f
        if (s.fs.last != f) println(" &")
      }
      print(" --> ")
      val (proverResult, passed) = expect(???, ps)
      res = passed
      //if (passed && proverResult == ProverStatus.Sat) printModel
      //else if (passed && proverResult == ProverStatus.Unsat)
      //  println(certificateAsString(Map.empty,
      //    InputFormat.Princess))
    }
    res
  }

  def TestCase(name : String, steps : TestStep*) {
    println("=" * 80)
    println(
      "Test " + testCaseCounter + ": " + name)
    println("-" * 80)
    var stepNo = 1;
    scope {
      for (s <- steps) {
        if (s.isInstanceOf[CommonAssert]) {
          println("-" * 80)
          println("Common assertion: ")
          justAssert(s)
          println("-" * 80)
        } else {
          print("Step " + testCaseCounter + "." + stepNo + " (expected: ")
          stepNo = stepNo + 1
          s match {
            case _ : SatStep => println("Sat)")
              executeStep(ProverStatus.Sat, s)
            case _ : UnsatStep => println("Unsat)")
              executeStep(ProverStatus.Unsat, s)
            case _ => // do nothing as CommonAssert step is already handled
          }
          if (steps.last != s) println("-" * 80)
        }
      }
      println("=" * 80)
      testCaseCounter = testCaseCounter + 1
    }
  }
}


object HeapTests2 extends App {
  Debug enableAllAssertions true

  val NullObjName = "NullObj"
  val ObjSort = Heap.ADTSort(0)
  val StructSSort = Heap.ADTSort(1)
  val heap = new Heap("heap", "addr", ObjSort,
    List("HeapObject", "struct_S"), List(
      ("WrappedInt", Heap.CtorSignature(List(("getInt",
        Heap.OtherSort(Sort.Integer))), ObjSort)),
      ("WrappedS", Heap.CtorSignature(List(("getS", StructSSort)), ObjSort)),
      ("WrappedNode", Heap.CtorSignature(List(("getNode", StructSSort)), ObjSort)),
      ("struct_S", Heap.CtorSignature(List(("x", Heap.OtherSort(Sort.Integer))),
        StructSSort)),
      ("struct_Node", Heap.CtorSignature(List(("R", Heap.AddressCtor)),
        StructSSort)),
      ("defObj", Heap.CtorSignature(List(), ObjSort))),
    defObjCtor)

  def defObjCtor(objectCtors : Seq[IFunction],
                 heapADTs : ADT) : ITerm = {
    import IExpression.toFunApplier
    objectCtors.last()
  }

  val Seq(wrappedInt,
          wrappedS,
          wrappedNode,
          struct_S,
          struct_Node,
          defObj) = heap.userADTCtors
  val Seq(Seq(getInt),
          Seq(getS),
          Seq(getNode),
          Seq(sel_x),
          Seq(sel_R),_*) = heap.userADTSels

  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._
    import heap._
    val h = HeapSort.newConstant("h")
    val h1 = createConstant("h1", HeapSort)
    val h2 = createConstant("h2", HeapSort)
    val ar = allocResSort.newConstant("ar")
    val p1 =  createConstant("p1", AddressSort)
    val p2 =  createConstant("p2", AddressSort)
    val x = createConstant("x")
    val o = createConstant("o", ObjectSort)


    addConstants(List(h, ar))

    import IExpression.{all => forall, _}

    val priTests = new PrincessTester(pr)
    import priTests._

   TestCase (
      "Reading back written value after chain allocation and a write.",
      CommonAssert(
        ar === alloc(newHeap(
                             alloc(emptyHeap(), wrappedInt(0)) // h(0)
                     ), wrappedInt(3))                         // h(0, 3)
      ),
      SatStep(isAlloc(newHeap(ar), newAddr(ar))),
      SatStep(getInt(read(newHeap(ar), newAddr(ar))) === 3),
      UnsatStep(getInt(read(newHeap(ar), newAddr(ar))) =/= 3),
      SatStep(read(newHeap(ar), newAddr(ar)) === wrappedInt(3)),
      CommonAssert(
        h === write(newHeap(ar), newAddr(ar), wrappedInt(50))  // h(0, 50)
      ),
      SatStep(read(h, nthAddr(2)) =/= read(newHeap(ar),nthAddr(2))),
      UnsatStep(read(h, nthAddr(2)) === read(newHeap(ar),nthAddr(2))),
      SatStep(isAlloc(h, newAddr(ar))),
      UnsatStep(getInt(read(h, newAddr(ar))) === 0),
      UnsatStep(getInt(read(h, newAddr(ar))) === 3),
      SatStep(getInt(read(h, newAddr(ar))) =/= 3),
      SatStep(read(h, newAddr(ar)) =/= wrappedInt(3)),
      UnsatStep(getInt(read(h, newAddr(ar))) =/= 50),
      SatStep(getInt(read(h, newAddr(ar))) === 50),
      SatStep(read(h, newAddr(ar)) === wrappedInt(50))
    )

    TestCase(
      "list-001-fail.c-1",
      CommonAssert(h === newHeap(alloc(emptyHeap(), wrappedS(struct_S(0))))),
      CommonAssert(p1 === newAddr(alloc(emptyHeap(), wrappedS(struct_S(0))))),
      CommonAssert(p2 === p1),
      SatStep(p1 === p2)
    )
    TestCase(
      "list-001-fail.c-2",
      SatStep(
        h1 === emptyHeap() &&&
        h === newHeap(alloc(h1, wrappedS(struct_S(0)))) &&&
        p1 === newAddr(alloc(h1, wrappedS(struct_S(0)))) &&&
        p2 === p1 &&&
        x === sel_x(getS(read(h, p2)))// &&&
      )
    )
    TestCase(
      "list-004-fail.c",
      SatStep(
        h1 === newHeap(alloc(emptyHeap(), wrappedNode(struct_Node(0)))) &&&
        p1 === newAddr(alloc(emptyHeap(), wrappedNode(struct_Node(0)))) &&&
        h === newHeap(alloc(h1, p1)) &&&
        h2 === write(h, p1, wrappedNode(struct_Node(p1)))
      )
    )
  }
}
