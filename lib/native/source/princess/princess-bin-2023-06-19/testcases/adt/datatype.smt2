
(declare-datatype Color ( (red) (green) (blue) ))

(declare-fun x () Color)
(declare-fun y () Color)

(assert (= red green))
(check-sat)