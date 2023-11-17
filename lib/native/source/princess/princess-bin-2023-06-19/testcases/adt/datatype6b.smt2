

(declare-datatype List ( (nil) (cons (head Int) (tail List)) ))

(declare-const a List)
(declare-const b List)

(assert (not (= a b)))
(check-sat)
(get-model)

