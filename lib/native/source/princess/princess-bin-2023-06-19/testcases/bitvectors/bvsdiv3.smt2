(set-logic QF_BV)
(set-info :status unsat)

(declare-fun s () (_ BitVec 4))
(define-fun t () (_ BitVec 4) (_ bv14 4))
  
(assert (bvsge s (_ bv0 4)))
(assert (bvslt t (_ bv0 4)))
(assert (not (= (bvsdiv s t) (bvneg (bvudiv s (bvneg t))))))

(check-sat)
