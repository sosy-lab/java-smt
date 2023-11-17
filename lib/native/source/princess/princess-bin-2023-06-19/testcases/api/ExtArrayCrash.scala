
import ap.util.Debug
import ap.SimpleAPI


 val PRINCESS_CRASH_QUERY =
      "(declare-fun a@2 () (_ BitVec 32))\n" +
          "(declare-fun b@2 () (_ BitVec 32))\n" +
          "(declare-fun p1@2 () (_ BitVec 32))\n" +
          "(declare-fun p2@2 () (_ BitVec 32))\n" +
          "(declare-fun p1@3 () (_ BitVec 32))\n" +
          "(declare-fun p2@3 () (_ BitVec 32))\n" +
          "(declare-fun p1@4 () (_ BitVec 32))\n" +
          "(declare-fun |f::v@2| () (_ BitVec 32))\n" +
          "(declare-fun |f::__retval__@2| () (_ BitVec 32))\n" +
          "(declare-fun __ADDRESS_OF_a@ () (_ BitVec 32))\n" +
          "(declare-fun __ADDRESS_OF_b@ () (_ BitVec 32))\n" +
          "(declare-fun *int@1 () (Array (_ BitVec 32) (_ BitVec 32)))\n" +
          "(declare-fun *int@2 () (Array (_ BitVec 32) (_ BitVec 32)))\n" +
          "(declare-fun *int@3 () (Array (_ BitVec 32) (_ BitVec 32)))\n" +
          "(declare-fun *int@4 () (Array (_ BitVec 32) (_ BitVec 32)))\n" +
          "(declare-fun *int@5 () (Array (_ BitVec 32) (_ BitVec 32)))\n" +
          "(define-fun abbrev_9 () Bool (and (and (and (and (and (and (and (and (and (and (=" +
          " a@2 (_ bv0 32)) (and (and (bvslt (_ bv0 32) __ADDRESS_OF_a@) (= (bvurem" +
          " __ADDRESS_OF_a@ (_ bv4 32)) (bvurem (_ bv0 32) (_ bv4 32)))) (bvslt (_ bv0 32)" +
          " (bvadd __ADDRESS_OF_a@ (_ bv4 32))))) (and (= b@2 (_ bv0 32)) (and (and (bvslt" +
          " (bvadd __ADDRESS_OF_a@ (_ bv4 32)) __ADDRESS_OF_b@) (= (bvurem __ADDRESS_OF_b@ (_" +
          " bv4 32)) (bvurem (_ bv0 32) (_ bv4 32)))) (bvslt (_ bv0 32) (bvadd __ADDRESS_OF_b@" +
          " (_ bv4 32)))))) (= p1@2 (_ bv0 32))) (= p2@2 (_ bv0 32))) (and (= p1@3" +
          " __ADDRESS_OF_a@) (= (select *int@1 __ADDRESS_OF_a@) a@2))) (and (= p2@3" +
          " __ADDRESS_OF_b@) (= (select *int@1 __ADDRESS_OF_b@) b@2))) (= *int@2 (store *int@1" +
          " __ADDRESS_OF_b@ (_ bv1 32)))) (= *int@3 (store *int@2 __ADDRESS_OF_a@ (_ bv5 32))))" +
          " (= *int@4 (store *int@3 __ADDRESS_OF_a@ (bvsub (select *int@3 __ADDRESS_OF_a@) (_" +
          " bv1 32))))) (= |f::v@2| (bvsub (bvadd (select *int@4 p1@3) (select *int@4 p2@3))" +
          " (select *int@4 __ADDRESS_OF_a@)))))\n" +
          "(assert (or (and (and (and (or (and (and (and abbrev_9 (= |f::v@2| (_ bv1 32))) (=" +
          " p1@4 p2@3)) (= |f::__retval__@2| |f::v@2|)) (and (and (and abbrev_9 (not (=" +
          " |f::v@2| (_ bv1 32)))) (= |f::__retval__@2| (_ bv0 32))) (= p1@4 p1@3))) (= *int@5" +
          " (store *int@4 __ADDRESS_OF_a@ |f::__retval__@2|))) (not (= (select *int@5" +
          " __ADDRESS_OF_a@) (_ bv0 32)))) (not (= p1@4 p2@3))) (and (and (or (and (and (and" +
          " abbrev_9 (= |f::v@2| (_ bv1 32))) (= p1@4 p2@3)) (= |f::__retval__@2| |f::v@2|))" +
          " (and (and (and abbrev_9 (not (= |f::v@2| (_ bv1 32)))) (= |f::__retval__@2| (_ bv0" +
          " 32))) (= p1@4 p1@3))) (= *int@5 (store *int@4 __ADDRESS_OF_a@ |f::__retval__@2|)))" +
          " (= (select *int@5 __ADDRESS_OF_a@) (_ bv0 32)))))"


Debug.enableAllAssertions(true);

// create formula in one API
val api = SimpleAPI.spawnWithAssertions
val parserResult =
  api.extractSMTLIBAssertionsSymbols(new java.io.StringReader(PRINCESS_CRASH_QUERY), true);
val assertion = parserResult._1.head

// add symbols to a second API
val api2 = SimpleAPI.spawnWithAssertions

val syms =
  api.order.sort(parserResult._3.keySet).toVector
val reorderedSyms =
  List(syms(11), syms(6), syms(8), syms(9), syms(7), syms(15), syms(10), syms(0), syms(14), syms(1), syms(5), syms(12), syms(2), syms(3), syms(4), syms(13))

api2.addConstantsRaw(reorderedSyms);

// and solver the original query in the second API
api2.push
api2.addAssertion(assertion);
println(api2.checkSat(true))  // crash!

api.shutDown
api2.shutDown
