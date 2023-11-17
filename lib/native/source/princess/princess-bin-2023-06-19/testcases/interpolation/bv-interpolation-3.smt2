;
; Bit-vector interpolation example
;

(set-logic QF_BV)

(set-option :produce-interpolants true)

(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))

(assert (bvugt a (bvadd b (_ bv2 16))))
(assert (bvugt b a))
(assert (bvult b (_ bv1000 16)))

(check-sat)
(get-interpolants)
