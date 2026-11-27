(set-logic HORN)

(declare-fun fun (Int) Bool)

(assert
  (forall ((x Int))
    (=>
      (fun x)
      (fun (ite (<= x 0) (- x) x)))))
