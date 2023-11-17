; Example that previously led to an exception when parsing
; the data-type declaration

(declare-datatype |List[Int]| (
  (nil)
  (cons (head Int) (tail |List[Int]|))
))

(declare-const l |List[Int]|)

(assert (not (= l nil)))
(assert (= (_size l) 1))

(check-sat)

