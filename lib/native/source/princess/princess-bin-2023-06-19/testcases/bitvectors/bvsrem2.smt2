(set-logic QF_BV)
(set-info :status unsat)

(declare-fun c () (_ BitVec 32))
(define-fun D () (_ BitVec 32) (_ bv11 32))

(assert (not (= c (bvadd (bvmul D (bvsdiv c D))
                         (bvsrem c D)))))

(check-sat)
