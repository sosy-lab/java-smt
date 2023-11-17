
(set-logic AUFLIA)

(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun p () Bool)

(assert (not (exists ((y Int))
                (= (* 2 y)
                   (ite (exists ((x Int))
                                (= a (ite p (* 2 x) (* (+ 1 1) x))))
                        a (+ a 1))))))

(check-sat)
