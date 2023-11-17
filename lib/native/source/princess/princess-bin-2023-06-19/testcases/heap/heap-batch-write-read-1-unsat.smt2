(set-logic Heap)

(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (simple 0)) (
  (
   (WrappedInt (getInt Int))
   (WrappedAddr (getAddr Addr))
   (Wrappedsimple (getsimple simple))
   (defObj)
  )
  (
   (simple (x Int))
  )
))

(declare-const H  Heap)
(declare-const H2 Heap)
(declare-const AR AddrRange)
(declare-const A1 Addr)

(assert (= H       (batchAllocHeap emptyHeap (WrappedInt 42) 3)))
(assert (= AR (batchAllocAddrRange emptyHeap (WrappedInt 42) 3)))
(assert (not (= (getInt (read H (AddrRangeStart AR))) 42)))

(check-sat) ; should be unsat
