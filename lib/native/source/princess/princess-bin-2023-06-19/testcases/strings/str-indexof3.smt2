

(declare-const w String)
(declare-const n Int)

(assert
   (distinct
      (= (str.indexof "abcabcabc" "abc" n) n)
      (or (= n 0) (= n 3) (= n 6) (= n (- 1)))))
(check-sat)
