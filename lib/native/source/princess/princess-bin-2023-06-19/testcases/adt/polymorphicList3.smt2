
(declare-datatypes ( ( List 1) ) (
  (par (T) ( ( nil ) ( cons ( car T ) ( cdr ( List T )) )))))

(declare-const l (List Int))
(declare-const l3 (List (List Int)))

(assert (not (is-nil l3)))
(assert (not (is-nil (cdr l3))))
(assert (= (_size l3) (_size (car l3))))
(assert (= (car l3) l))
(assert (< (car (car l3)) 0))

(check-sat)
(get-model)
