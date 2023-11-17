(set-logic QF_S)

(declare-datatype Tree ( (leaf) (node (left Tree) (data String) (right Tree)) ))

(define-fun-rec cat ((t Tree)) String
  (ite (is-leaf t) ""
       (str.++ (cat (left t)) (data t) (cat (right t)))))

(define-fun-rec nonEmpty ((t Tree)) Bool
  (or (is-leaf t)
      (and (is-node t)
           (not (= (data t) ""))
           (nonEmpty (left t))
           (nonEmpty (right t)))))

(declare-const a String)
(declare-const b String)
(declare-const c String)
(declare-const t Tree)

(assert (= (str.++ a b c) "Hello World"))

(assert (= (cat t) "Hello World"))
(assert (nonEmpty t))
;(assert (> (_size t) 5))
(assert (< (_size t) 10))

(check-sat)