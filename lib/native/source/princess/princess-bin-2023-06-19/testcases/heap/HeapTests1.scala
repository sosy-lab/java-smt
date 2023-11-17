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


object HeapTests1 extends App {
  Debug enableAllAssertions true

  val NullObjName = "NullObj"
  val ObjSort = Heap.ADTSort(0)
  val StructSSort = Heap.ADTSort(1)

  def defObjCtor(objectCtors : Seq[IFunction],
                 heapADTs : ADT) : ITerm = {
    import IExpression.toFunApplier
    objectCtors.last()
  }

  val heap = new Heap("heap", "addr", ObjSort,
    List("HeapObject", "struct_S"), List(
      ("WrappedInt", Heap.CtorSignature(List(("getInt",
        Heap.OtherSort(Sort.Integer))), ObjSort)),
      ("WrappedS", Heap.CtorSignature(List(("getS", StructSSort)), ObjSort)),
      ("WrappedAddr", Heap.CtorSignature(List(("getAddr", Heap.AddressCtor)), ObjSort)),
      ("struct_S", Heap.CtorSignature(List(("x", Heap.OtherSort(Sort.Integer))),
        StructSSort)),
      ("defObj", Heap.CtorSignature(List(), ObjSort))),
    defObjCtor)

  val Seq(wrappedInt,
          wrappedS,
          wrappedAddr,
          struct_S,
          defObjCtr) = heap.userADTCtors
  val Seq(Seq(getInt),
          Seq(getS),
          Seq(getAddr),
          Seq(sel_x), _*) = heap.userADTSels

  import IExpression.toFunApplier
  val defObj = defObjCtr()

  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._
    import heap._

    val h = createConstant("h", HeapSort)
    val h1 = createConstant("h1", HeapSort)
    val h2 = createConstant("h2", HeapSort)
    val p =  createConstant("p", AddressSort)
    val p1 =  createConstant("p'", AddressSort)
    val ar = createConstant("ar", allocResSort)
    val ar1 = createConstant("ar'", allocResSort)
    val o = createConstant("o", ObjectSort)
    val o1 = createConstant("o'", ObjectSort)
    val r = createConstant("r", addressRangeSort)
    val bar = createConstant("bar", batchAllocResSort)
    val n = createConstant("n", Sort.Nat)

    import IExpression.{all => forall, _}

    val priTests = new PrincessTester(pr)
    import priTests._

    TestCase (
      "All locations on the empty heap are unallocated.",
      UnsatStep(isAlloc(emptyHeap(), p)),
      SatStep(!isAlloc(emptyHeap(), p))
    )

    TestCase (
      "For all heaps, null pointer always points to an unallocated location.",
      UnsatStep(isAlloc(h, nullAddr()))
    )

    TestCase(
      "For all heaps, trying to read the null pointer returns the defined " +
      "object.",
      UnsatStep(read(h, nullAddr()) =/= defObj),
      SatStep(read(h, nullAddr()) === defObj)
    )

    TestCase(
      "For all heaps, writing to the null pointer returns the original heap.",
      UnsatStep(write(h, nullAddr(), o) =/= h),
      SatStep(write(h, nullAddr(), o) === h)
    )

    TestCase (
      "After alloc, the returned pointer points to an allocated address.",
      CommonAssert(alloc(h, o) === ar),
      SatStep(isAlloc(newHeap(ar), newAddr(ar))),
      UnsatStep(!isAlloc(newHeap(ar), newAddr(ar)))
    )

    TestCase (
      "After alloc, previously allocated addresses are the same in both heaps.",
      CommonAssert(
        alloc(h, o) === ar
      ),
      UnsatStep(
        isAlloc(h, p) & !isAlloc(newHeap(ar), p)
      ),
      UnsatStep(
        p =/= newAddr(ar),
        !isAlloc(h, p),
        isAlloc(newHeap(ar), p)
      )
    )

    TestCase(
      "Deterministic allocation",
      UnsatStep(
        AddressSort.all(x => isAlloc(h, x) <=> isAlloc(h1, x)),
        alloc(h, o) === ar,
        alloc(h1, o1) === ar1,
        newAddr(ar) =/= newAddr(ar1)
      )
    )

    /** Test cases for facts about read/write */
    TestCase(
      "Reading from a previously written (alloc.) " +
      "location returns that value.",
      CommonAssert(
        isAlloc(h, p)
      ),
      SatStep(
        read(write(h, p, o), p) === o
      ),
      UnsatStep(
        read(write(h, p, o), p) =/= o
      )
    )

    TestCase(
      "Reading a newly allocated location returns the allocated value",
      CommonAssert(
        ar === alloc(h, o)
      ),
      SatStep(
        read(newHeap(ar), newAddr(ar)) === o
      ),
      UnsatStep(
        read(newHeap(ar), newAddr(ar)) =/= o
      )
    )

    TestCase(
      "Allocation does not modify any of the values on the old heap",
      CommonAssert(
        ar === alloc(h, o),
        p =/= newAddr(ar)
      ),
      SatStep(
        read(newHeap(ar), p) === read(h, p)
      ),
      UnsatStep(
        read(newHeap(ar), p) =/= read(h, p)
      )
    )

    TestCase(
      "Reading a newly allocated location returns the allocated value (v2)",
      CommonAssert(
        alloc(h, o) === ar,
        h1 === newHeap(ar),
        p === newAddr(ar)
      ),
      SatStep(
        read(h1, p) === o
      ),
      UnsatStep(
        read(h1, p) =/= o
      )
    )

    TestCase(
      "Reading an unallocated location returns the defined object",
      CommonAssert(
        !isAlloc(h, p)
      ),
      SatStep(
        read(h, p) === defObj
      ),
      UnsatStep(
        read(h, p) =/= defObj
      )
    )

    TestCase(
      "Writing to a location does not modify the rest of the locations",
      CommonAssert(
        p =/= p1,
        isAlloc(h, p),
        isAlloc(h, p1)
      ),
      SatStep(
        read(write(h, p1, o), p) === read(h, p)
      ),
      UnsatStep(
        read(write(h, p1, o), p) =/= read(h, p)
      )
    )

    TestCase(
      "Writing to an unallocated location returns the same heap.",
      CommonAssert(!isAlloc(h, p)),
      SatStep(write(h, p, o) === h),
      UnsatStep(write(h, p, o) =/= h),

      CommonAssert(h =/= emptyHeap()),
      SatStep(write(h, p, o) === h & h =/= emptyHeap()),
      UnsatStep(write(h, p, o) =/= h),

      CommonAssert(p =/= nullAddr()),
      SatStep(write(h, p, o) === h),
      UnsatStep(write(h, p, o) =/= h)
    )

    TestCase(
      "Allocating and dereferencing pointer to pointer.",
      CommonAssert(alloc(emptyHeap(), wrappedInt(42)) === ar &
                   p === newAddr(ar) & h === newHeap(ar)),
      CommonAssert(alloc(h, wrappedAddr(p)) === ar1 &
                   p1 === newAddr(ar1) & h1 === newHeap(ar1)),
      SatStep(read(h, getAddr(read(h1,p1))) === wrappedInt(42)),
      UnsatStep(read(h, getAddr(read(h1,p1))) =/= wrappedInt(42))
    )

  TestCase(
      "Extensionality over write",
      SatStep(write(h, p, o) === write(write(h, p, o1), p, o)),
      UnsatStep(write(h, p, o) =/= write(write(h, p, o1), p, o))
    )

    TestCase(
      "Extensionality over write (exclude empty heaps)",
      CommonAssert(h =/= emptyHeap()),
      SatStep(write(h, p, o) === write(write(h, p, o1), p, o)),
      UnsatStep(write(h, p, o) =/= write(write(h, p, o1), p, o))
    )

    TestCase(
      "Extensionality over write (exclude empty heaps and null addresses)",
      CommonAssert(h =/= emptyHeap() &
                   p =/= nullAddr()),
      SatStep(write(h, p, o) === write(write(h, p, o1), p, o)),
      UnsatStep(write(h, p, o) =/= write(write(h, p, o1), p, o))
    )

    TestCase(
      "Extensionality over write (only valid writes)",
      CommonAssert(isAlloc(h, p)),
      SatStep(write(h, p, o) === write(write(h, p, o1), p, o)),
      UnsatStep(write(h, p, o) =/= write(write(h, p, o1), p, o))
    )

    TestCase(
      "Extensionality",
      CommonAssert(counter(h) === counter(h1) &
                   h =/= h1),
      SatStep(AddressSort.ex(a =>
        isAlloc(h, a) & (read(h, a) =/= read(h1, a)))),
      UnsatStep(AddressSort.all(a =>
        isAlloc(h, a) & (read(h, a) === read(h1, a))))
    )

    TestCase(
      "ROW-Upward",
      CommonAssert(isAlloc(h, p) & isAlloc(h, p1) & p =/= p1),
      SatStep(write(write(h, p, wrappedInt(1)), p1, wrappedInt(42)) === h1 &
              write(write(h, p, wrappedInt(2)), p1, wrappedInt(42)) === h2),
      UnsatStep(write(write(h, p, wrappedInt(1)), p1, wrappedInt(42)) ===
                write(write(h, p, wrappedInt(2)), p1, wrappedInt(42)))
    )

    TestCase(
      "batchAlloc tests - 1",
      CommonAssert(n > 0 & batchAlloc(emptyHeap(), o, n) === bar),
      SatStep(addrRangeStart(newAddrRange(bar)) =/= nullAddr()),
      UnsatStep(addrRangeStart(newAddrRange(bar)) === nullAddr()),
      SatStep(addrRangeSize(newAddrRange(bar)) === n),
      UnsatStep(addrRangeSize(newAddrRange(bar)) =/= n),
      UnsatStep(within(newAddrRange(bar), nullAddr()))
    )

    TestCase(
      "batchAlloc tests - 2",
      CommonAssert(
        batchAlloc(h, wrappedInt(3), 10) ===
          batchAllocResCtor(h1, r) &
          write(h1, nth(r, 3), wrappedInt(42)) === h2),
      SatStep(read(h2, nth(r, 0)) === wrappedInt(3)),
      UnsatStep(read(h2, nth(r, 0)) =/= wrappedInt(3)),
      SatStep(read(h2, nth(r, 5)) === wrappedInt(3)),
      UnsatStep(read(h2, nth(r, 5)) =/= wrappedInt(3)),
      SatStep(read(h2, nth(r, 9)) === wrappedInt(3)),
      UnsatStep(read(h2, nth(r, 9)) =/= wrappedInt(3)),
      SatStep(isAlloc(h2, nth(r, 9))),
      UnsatStep(!isAlloc(h2, nth(r, 9))),
      UnsatStep(isAlloc(h2, nth(r, 10))),
      SatStep(!isAlloc(h2, nth(r, 10))),
      SatStep(nth(r, 10) === nullAddr()),
      UnsatStep(nth(r, 10) =/= nullAddr()),
      SatStep(read(h2, nth(r, 10)) === defObj),
      UnsatStep(within(r, nth(r, 10))),
      UnsatStep(read(h2, nth(r, 10)) =/= defObj),
      SatStep(read(h2, nth(r, 3)) === wrappedInt(42)),
      UnsatStep(read(h2, nth(r, 3)) =/= wrappedInt(42))
    )

    TestCase(
      "Reading from a previously batch-written (alloc.) " +
        "location returns that value.",
      CommonAssert(
        isAlloc(h, p) & within(r, p) &
          isAlloc(h, addrRangeStart(r)) &
          isAlloc(h, nth(r, addrRangeSize(r)-1)) // h is allocated for the whole address range
      ),
      SatStep(
        read(batchWrite(h, r, o), p) === o
      ),
      UnsatStep(
        read(batchWrite(h, r, o), p) =/= o
      )
    )

    TestCase(
      "batchWrite to a location does not modify the rest of the locations",
      CommonAssert(
        isAlloc(h, p) & !within(r, p) & addrRangeSize(r) > 0 &
          isAlloc(h, nth(r, addrRangeSize(r)-1)) // h is allocated for the whole address range
      ),
      SatStep(
        read(batchWrite(h, r, o), p) === read(h, p)
      ),
      UnsatStep(
        read(batchWrite(h, r, o), p) =/= read(h, p)
      )
    )

    TestCase(
      "batchWrite to a range that contains an unallocated location " +
        "returns the same heap.",
      CommonAssert(
        within(r, p) & !isAlloc(h, p)
      ),
      SatStep(batchWrite(h, r, o) === h),
      UnsatStep(batchWrite(h, r, o) =/= h),

      CommonAssert(h =/= emptyHeap()),
      SatStep(batchWrite(h, r, o) === h & h =/= emptyHeap()),
      UnsatStep(batchWrite(h, r, o) =/= h),

      CommonAssert(p =/= nullAddr()),
      SatStep(batchWrite(h, r, o) === h),
      UnsatStep(batchWrite(h, r, o) =/= h)
    )

    TestCase(
      "Extensionality over batchWrite (exclude empty heaps)",
      CommonAssert(h =/= emptyHeap()),
      SatStep(batchWrite(h, r, o) === batchWrite(batchWrite(h, r, o1), r, o)),
      UnsatStep(batchWrite(h, r, o) =/=
        batchWrite(batchWrite(h, r, o1), r, o))
    )

    TestCase(
      "Extensionality over batchWrite (exclude empty heaps and empty address ranges)",
      CommonAssert(h =/= emptyHeap() & addrRangeSize(r) > 0),
      SatStep(batchWrite(h, r, o) === batchWrite(batchWrite(h, r, o1), r, o)),
      UnsatStep(batchWrite(h, r, o) =/=
        batchWrite(batchWrite(h, r, o1), r, o))
    )

    TestCase(
      "Extensionality over batchWrite (only valid writes)",
      CommonAssert(addrRangeSize(r) > 0 & p === nth(r, addrRangeSize(r)-1) ),
       SatStep(batchWrite(h, r, o) === batchWrite(batchWrite(h, r, o1), r, o)),
      UnsatStep(batchWrite(h, r, o) =/=
        batchWrite(batchWrite(h, r, o1), r, o))
    )

  }
}
