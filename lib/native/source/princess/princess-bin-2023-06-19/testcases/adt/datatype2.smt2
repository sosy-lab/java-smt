
(declare-datatype List ( (nil) (cons (head Int) (tail List)) ))

(declare-fun x () List)
(declare-fun y () Int)
(declare-fun y2 () Int)
(declare-fun z () List)

(push 1)
(assert (= x (cons 1 (cons 2 nil))))
(assert (< (head x) 0))
(check-sat)
(pop 1)

(push 1)
(assert (not (= x nil)))
(assert (not (= x (cons (head x) (tail x)))))
(check-sat)
(pop 1)

(push 1)
(assert (= (cons 1 (cons y nil)) (cons y2 (cons 2 nil))))
(check-sat)
(get-value (y y2))
(pop 1)

(push 1)
(assert (= (cons 1 (cons 2 z)) (cons 1 x)))
(check-sat)
(assert (= x z))
(check-sat)
(pop 1)
