(set-logic QF_BV)

(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
(declare-fun e () (_ BitVec 16))

(assert (= (concat c d) e))
(assert (bvult e (_ bv2000 16)))
(assert (bvugt ((_ extract 15 8) e) (_ bv5 8)))

(check-sat)

