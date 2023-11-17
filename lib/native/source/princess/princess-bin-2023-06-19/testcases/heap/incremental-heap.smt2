(set-logic Heap)

(declare-heap heap addr HeapObject
 defObj
 ((HeapObject 0) (simple 0)) (
  (
   (WrappedInt (getInt Int))
   (WrappedAddr (getAddr addr))
   (Wrappedsimple (getsimple simple))
   (defObj)
  )
  (
   (simple (x Int))
  )
))

(declare-const H heap)
(declare-const H2 heap)
(declare-const A addr)
(declare-const A2 addr)

(assert (= (AllocResheap H A) (alloc emptyheap (WrappedInt 10))))

(push 1)
(assert (not (and (is-WrappedInt (read H A)) (= (getInt (read H A)) 10))))
(check-sat) ; should be unsat
(pop 1)

(assert (= (AllocResheap H2 A2) (alloc H (Wrappedsimple (simple 42)))))

(push 1)
(assert (= A A2))
(check-sat) ; should be unsat
(pop 1)

(push 1)
(assert (< (getInt (read H2 A)) (x (getsimple (read H2 A2)))))
(check-sat) ; should be sat
(get-model)
(pop 1)

