(set-logic AUFLIA)

(declare-fun arr () (Array Int Bool))

(assert (= (store arr 1 true) arr))
(assert (not (select arr 2)))

(check-sat)
(get-model)
