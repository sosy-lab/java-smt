(set-logic Heap)

(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (simple 0)) (
  (
   (Wrappedsimple (getsimple simple))
   (WrappedInt (getInt Int))
   (defObj)
  )
  (
   (simple (range AddrRange))
  )
))

(declare-const h1 Heap)
(declare-const h2 Heap)
(declare-const a Addr)
(declare-const ar AddrRange)

(assert (= (BatchAllocResHeap h1 ar) (batchAlloc emptyHeap (WrappedInt 1) 3)))
(assert (= (AllocResHeap h2 a) (alloc h1 (Wrappedsimple (simple ar)))))
(assert (not (= (WrappedInt 2) (read h2 (AddrRangeStart (range (getsimple (read h2 a))))))))

(check-sat) ; should be sat
