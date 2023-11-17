(set-info :source |
  Example used in the LPAR 2008 paper
  "A Constraint Sequent Calculus for First-Order Logic
   with Linear Integer Arithmetic"
 |)

(set-logic AUFLIA)
(declare-fun a () Int)
(declare-fun p (Int) Int)

(assert (forall ((x Int)) (= (p (* 2 x)) 0)))
(assert (forall ((x Int)) (= (p (+ (* 2 x) 1)) 1)))

(assert (= (p a) 0))
(assert (= (p (+ a 10)) 1))

(check-sat)
