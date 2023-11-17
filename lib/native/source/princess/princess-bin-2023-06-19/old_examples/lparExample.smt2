(set-info :source |
  Example used in the LPAR 2008 paper
  "A Constraint Sequent Calculus for First-Order Logic
   with Linear Integer Arithmetic"
 |)

(set-logic AUFLIA)
(declare-fun a () Int)
(declare-fun p (Int) Bool)

(assert (forall ((x Int)) (p (* 2 x))))
(assert (forall ((x Int)) (not (p (+ (* 2 x) 1)))))

(assert (p a))
(assert (not (p (+ a 10))))

(check-sat)