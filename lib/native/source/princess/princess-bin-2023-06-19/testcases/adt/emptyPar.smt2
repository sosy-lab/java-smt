(declare-datatypes ((T 0)) ((par () ((T (a Int) (b Int))))))

(declare-const x T)

(assert (> (a x) 0))

(check-sat)
(get-model)
