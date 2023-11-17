;
; Bit-vector interpolation example
;

(set-logic AUFLIA)

(set-option :produce-interpolants true)

(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

(assert (bvugt a (bvmul b (_ bv2 8))))
(assert (bvult a (bvadd (bvmul b (_ bv2 8)) (_ bv2 8))))
(assert (bvugt (f (bvsub a (_ bv1 8))) (f (bvmul (_ bv2 8) b))))

(check-sat)
(get-interpolants)
