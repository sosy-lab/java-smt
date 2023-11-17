
(set-logic AUFLIA)

(declare-fun a () Int)
(declare-fun b () Int)

(assert (not (exists ((y Int))
                (= (* 2 y)
                   (ite (exists ((x Int)) (= a (* 2 x))) a (+ a 1))))))

(check-sat)
