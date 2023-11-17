(set-logic Heap)

(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (simple 0)) (
  (
   (WrappedInt (getInt Int))
   (Wrappedsimple (getsimple simple))
   (defObj)
  )
  (
   (simple (x Int))
  )
))

(declare-const H Heap)
(declare-const A Addr)

; (assert (= (AllocResHeap H A) (alloc emptyHeap (WrappedInt 10))))
(assert (= H (allocHeap emptyHeap (WrappedInt 42))))
(assert (= A (allocAddr emptyHeap (WrappedInt 42))))
(assert (not (and (is-WrappedInt (read H A)) (= (getInt (read H A)) 42))))

(check-sat) ; should be unsat
