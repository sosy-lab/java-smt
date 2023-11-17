;
; bvor interpolation example
;

(set-logic QF_BV)

(set-option :produce-interpolants true)


(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

(assert (= b (bvor a (_ bv4 8))))
(assert (= b (_ bv11 8)))

(check-sat)
(get-interpolants)
