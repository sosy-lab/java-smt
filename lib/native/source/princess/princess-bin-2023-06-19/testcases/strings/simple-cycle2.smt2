(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(declare-fun e () String)

(assert (= a (str.++ b (str.++ c e))))
(assert (= b (str.++ d a)))

(assert (not (= e "")))

(check-sat)