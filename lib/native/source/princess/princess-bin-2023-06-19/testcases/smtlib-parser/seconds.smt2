

(assert
  (forall ((?t Int))
    (=>
      (>= ?t 0)
      (exists ((?h Int) (?m Int) (?s Int))
        (and
          (= ?t (+ (* 9 ?h) (* 3 ?m) ?s))
          (>= ?h 0)
          (>= ?m 0) (< ?m 3)
          (>= ?s 0) (< ?s 3)
        )))))

(check-sat)
(exit)
