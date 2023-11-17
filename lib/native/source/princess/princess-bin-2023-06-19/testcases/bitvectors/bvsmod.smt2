(set-logic QF_BV)
(set-info :status unsat)

(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))

(assert (not (= (bvsmod s t)
      (let ((?msb_s ((_ extract 3 3) s))
            (?msb_t ((_ extract 3 3) t)))
        (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
              (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
          (let ((u (bvurem abs_s abs_t)))
            (ite (= u (_ bv0 4))
                 u
            (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                 u
            (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                 (bvadd (bvneg u) t)
            (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                 (bvadd u t)
                 (bvneg u))))))))
                 )))

(check-sat)
