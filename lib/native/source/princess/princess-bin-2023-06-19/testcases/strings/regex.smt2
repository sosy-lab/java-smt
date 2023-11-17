

(declare-const R RegLan)

(assert (= R re.none))

(check-sat)
(get-model)
