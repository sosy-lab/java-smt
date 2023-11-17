
(declare-datatype List ( (nil) (cons (head Real) (tail List)) ))

(declare-fun l () List)

(assert (> (_size l) 3))

(check-sat)