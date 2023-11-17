(set-logic QF_BV)
(set-info :status unsat)

(declare-fun c () (_ BitVec 32))
(declare-fun d () (_ BitVec 32))

(assert (bvsge c d))
(assert (not (bvsge (bvsdiv c (_ bv11 32)) (bvsdiv d (_ bv11 32)))))

(check-sat)