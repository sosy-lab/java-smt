(set-logic QF_BV)
(set-info :status unsat)

(declare-fun c () (_ BitVec 6))
(declare-fun d () (_ BitVec 6))
(declare-fun x () (_ BitVec 6))

(assert (bvsge c d))
(assert (bvsgt x (_ bv0 6)))
(assert (not (bvsge (bvsdiv c x) (bvsdiv d x))))

(check-sat)
