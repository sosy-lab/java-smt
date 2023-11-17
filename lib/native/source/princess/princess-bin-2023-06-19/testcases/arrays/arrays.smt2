(set-logic AUFLIA)

(declare-fun arr () (Array Int Int))

(assert (= (store arr 1 2) arr))
(assert (not (= (select arr 1) 2)))

(check-sat)
(exit)
