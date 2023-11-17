
(declare-datatypes ( ( List 1) ) (
  (par (T) ( ( nil ) ( cons ( car T ) ( cdr ( List T )) )))))

(declare-const l (List Int))
(declare-const l2 (List Bool))
(declare-const l3 (List (List Int)))

(assert (not (is-nil l)))
(assert (not (is-nil l2)))
(assert (car l2))
(assert (not (is-nil l3)))
(assert (= (car l3) l))

(check-sat)
(get-model)
