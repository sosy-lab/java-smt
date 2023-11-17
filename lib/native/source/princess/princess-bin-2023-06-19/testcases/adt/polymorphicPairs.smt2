
(declare-datatypes ( ( Pair 2 ) ) (
  (par (S T) ( ( Pair ( fst S ) ( snd T ) )))))
(declare-datatypes ( ( Either 2 ) ) (
  (par (S T) ( ( Left ( left S ) ) ( Right ( right T ) )))))

(declare-const x (Pair Int Bool))
(declare-const y (Either Int Bool))

(assert (is-Left y))
(assert (= (left y) (fst x)))

(check-sat)
(get-model)
