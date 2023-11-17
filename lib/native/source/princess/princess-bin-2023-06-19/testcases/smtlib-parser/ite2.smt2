
(set-logic AUFLIA)

(declare-fun a () Bool)
(declare-fun b () Bool)

(assert (not (= (= a b) (ite a b (not b)))))

(check-sat)
