(set-logic QF_BV)
(set-info :status sat)

(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

(assert (bvsge c d))
(assert (bvsgt x (_ bv0 8)))
(assert (not (bvsgt (bvsdiv c x) (bvsdiv d x))))

(check-sat)

