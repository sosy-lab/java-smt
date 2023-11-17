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
   (simple (value Int))
  )
))

(declare-const H heap)
(declare-const H1 heap)
(declare-const H2 heap)
(declare-const H3 heap)
(declare-const x addr)
(declare-const y addr)
(declare-const z addr)
(declare-const obj HeapObject)

(define-fun is-int ((H heap) (x addr)) Bool (and (valid H x) (is-WrappedInt (read H x))))

(push 1)
(assert (not (= (is-int H x) (is-WrappedInt (read H x)))))
(check-sat)  ; should be unsat
(pop 1)

(set-option :produce-interpolants true)

(push 1)    ; check swapping of two numbers

(assert (! (and (is-int H x) (is-int H y) (is-int H z)) :named P1))
(assert (! (and (distinct x z) (distinct y z)) :named P2))

(assert (! (= H1 (write H z (read H x))) :named A))
(assert (! (= H2 (write H1 x (read H1 y))) :named B))
(assert (! (= H3 (write H2 y (read H2 z))) :named C))

(assert (! (not (and (= (read H x) (read H3 y)) (= (read H y) (read H3 x)))) :named Prop))

(check-sat)  ; should be unsat

(get-interpolants (and P1 P2) A B C Prop)

(pop 1)
