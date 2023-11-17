(set-logic Heap)

(set-option :produce-interpolants true)

(declare-heap heap addr HeapObject
 (AnInt 0)
 ((HeapObject 0)) (
  (
    (AnInt (getInt Int))
  )
))

(declare-const h heap)
(declare-const h2 heap)
(declare-const a addr)
(declare-const o HeapObject)

(assert (and (valid h a) (= h2 (write h a (AnInt 42)))))
(assert (and (= o (read h2 a)) (= o (AnInt 43))))
(check-sat)
