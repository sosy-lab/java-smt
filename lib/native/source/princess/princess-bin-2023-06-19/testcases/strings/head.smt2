(set-logic QF_)

(declare-fun x () String)

(assert (not (= "" x)))
(assert (> (str.head_code x ) 65))
(assert (< (str.head_code x ) 67))

(check-sat)
