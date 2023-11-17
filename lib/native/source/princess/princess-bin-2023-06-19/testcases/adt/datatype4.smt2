(set-option :produce-models true)

(declare-datatypes () (
  (Term 
    (int (iv Int)) 
    (list (lv TList)) 
    (tuple (tv TList)) 
    (fn (fv Int))) 
  (TList 
    (nil) 
    (cons (th Term) (tail TList))) 
))

(declare-const x1 Term)
(declare-const x2 Term)
(declare-const x3 Term)
(declare-const x4 Term)
(declare-const x5 Term)
(declare-const x67 Term)
(declare-const x7 Term)
(declare-const x8 Term)
(declare-const x9 Term)
(declare-const x10 Term)
(declare-const x11 Term)

(assert (not (= (list nil) x1)))
(assert (and (is-list x1) (is-cons (lv x1))))
(assert (and (is-list x1) (is-cons (lv x1)) (= x2 (th (lv x1)))))
(assert (and (is-list x1) (is-cons (lv x1)) (= x3 (list (tail (lv x1))))))
(assert (not (= (int 42) x2)))
(assert (and (is-list (list nil)) (= x4 (list (cons x2 (lv (list nil)))))))
(assert (not (= (list nil) x3)))
(check-sat)
