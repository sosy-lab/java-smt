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

(declare-const H Heap)
(declare-const AR AddrRange)

(assert (= (BatchAllocResHeap H AR) (batchAlloc emptyHeap (WrappedInt 42) 3)))
(assert (= (getInt (read H (AddrRangeStart AR))) 42))
(assert (not (is-WrappedInt (read H (AddrRangeStart AR)))))

(check-sat) ; should be unsat
