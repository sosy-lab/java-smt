
(declare-datatypes ( ( List 1) ) (
  (par (T) ( ( nil ) ( cons ( car T ) ( cdr ( List T )) )))))

;(declare-const l (List Int))
;(declare-const l2 (List Bool))
;(declare-const l3 (List (List Int)))

   (define-fun l3 () (List (List Int)) (cons (cons 10 (as nil (List Int))) (as nil (List (List Int)))))
   (define-fun l2 () (List Bool) (cons false (as nil (List Bool))))
   (define-fun l () (List Int) (cons 10 (as nil (List Int))))

(assert (not (is-nil l)))
(assert (not (is-nil l2)))
(assert (not (is-nil l3)))
(assert (distinct (car l3) l))

(check-sat)

