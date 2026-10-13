(set-logic HORN)
(declare-fun fun (Int Int) Bool)

(assert (forall ((m Int))
          (=> (> m 100) (fun m (- m 10)))))

(assert (forall ((m Int) (n Int) (p Int))
           (=> (and (<= m 100) (fun (+ m 11) p) (fun p n)) (fun m n))))

(assert (forall ((m Int) (n Int))
            (=> (and (fun m n) (<= m 101)) (= n 91))))
