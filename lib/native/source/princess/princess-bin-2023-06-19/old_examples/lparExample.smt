(benchmark lpar

 :notes "Example used in the LPAR 2008 paper A Constraint Sequent Calculus for First-Order Logic with Linear Integer Arithmetic"

 :logic AUFLIA
 :extrafuns ((a Int))
 :extrapreds ((p Int))

 :assumption (forall (?x Int) (p (* 2 ?x)))
 :assumption (forall (?x Int) (not (p (+ (* 2 ?x) 1))))

 :assumption (p a)
 :assumption (not (p (+ a 10)))

 :formula true)