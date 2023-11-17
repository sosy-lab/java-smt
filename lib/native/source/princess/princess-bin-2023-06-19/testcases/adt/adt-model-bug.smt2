
(declare-sort T1 0)
(declare-datatypes ((ListT1 0)) (((insertT1 (headT1 T1) (tailT1 ListT1)) nilT1)))

(define-fun lengthT1 ((x ListT1)) Int (- (_size x) 1))

(declare-const x ListT1)
(assert (= (lengthT1 x) 3))
(check-sat)
(get-model)
