

(declare-datatype List ( (nil) (cons (head Int) (tail List)) ))
(declare-datatype Tree ( (leaf) (node (data List) (left Tree) (right Tree)) ))

(declare-const t Tree)

(assert (> (_size t) 5))
(check-sat)
(get-model)

