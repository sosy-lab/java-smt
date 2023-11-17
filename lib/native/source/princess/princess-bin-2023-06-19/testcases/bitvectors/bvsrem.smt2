(set-logic QF_BV)
(set-info :status unsat)

(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))

(assert (not (= (bvsrem s t)
(let ((?msb_s ((_ extract 3 3) s))
            (?msb_t ((_ extract 3 3) t)))
        (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
             (bvurem s t)
        (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
             (bvneg (bvurem (bvneg s) t))
        (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
             (bvurem s (bvneg t))
             (bvneg (bvurem (bvneg s) (bvneg t)))))))
                 )))

(check-sat)
