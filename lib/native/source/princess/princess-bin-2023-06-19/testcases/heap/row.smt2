(set-logic Heap)

(declare-heap Heap Addr HeapObject
 (AnInt 0)
 ((HeapObject 0)) (
  (
   (AnInt (getInt Int))
  )
))

(declare-const H Heap)
(declare-const a1 Addr)
(declare-const a2 Addr)
(declare-const x Int)
(declare-const y Int)

(assert (valid H a1))
(assert (valid H a2))

(assert (= (write (write H a1 (AnInt x)) a2 (AnInt 42))
           (write (write H a1 (AnInt y)) a2 (AnInt 42))))
(assert (not (= a1 a2)))
(assert (not (= x y)))

(check-sat) ; should be unsat
