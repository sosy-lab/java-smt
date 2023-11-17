; Case in which previously the variable o was missing in the model

(set-logic ALL)

(define-sort Pointer () Int)

(declare-datatypes ((Obj 0) (struct_S 0)) (
    ((WrappedInt (getInt Int)) (WrappedS (getS struct_S)))
    ((struct_S (field_x Int)))
  ))

(declare-datatypes ((Heap 0)) (
    ((Heap (counter Int) (contents (Array Pointer Obj))))
  ))

(declare-const emptyArray (Array Pointer Obj))
(define-fun emptyHeap () Heap (Heap 1 emptyArray))
(define-fun defaultObj () Obj (WrappedInt 0))

(define-fun alloc ((h Heap) (obj Obj) (h1 Heap) (p Pointer)) Bool
    (let ((H (counter h)) (A (contents h)))
     (and (= p H) (= h1 (Heap (+ H 1) (store A H obj))))))

(define-fun read ((h Heap) (p Pointer)) Obj
       (select (contents h) p))

(declare-const h1 Heap)
(declare-const h2 Heap)
(declare-const p1 Pointer)
(declare-const o Obj)

(assert (alloc h1 (WrappedInt 42) h2 p1))

(assert (= o (read h2 p1)))

(check-sat)
(get-model)

