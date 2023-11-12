(define-sort A () (Array Int Int Int))
(define-fun bag-union ((x A) (y A)) A
  ((_ map (+ (Int Int) Int)) x y))
(declare-const s1 A)
(declare-const s2 A)
(declare-const s3 A)
(assert (= s3 (bag-union s1 s2)))
(assert (= (select s1 0 0) 5))
(assert (= (select s2 0 0) 3))
(assert (= (select s2 1 2) 4))
(check-sat)
(get-model)

