(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (= a (str.cons (char.from-int 65) b)))
(assert (= b (str.++ d a)))

(check-sat)