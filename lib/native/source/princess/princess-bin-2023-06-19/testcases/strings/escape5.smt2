(set-logic QF_S)

(declare-fun T_163 () String)
(declare-fun T_162 () String)

(assert (= T_163 (str.++ T_162 "\""></scr")))

(check-sat)
