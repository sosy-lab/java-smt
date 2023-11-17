

(declare-const w String)

(assert (distinct (str.prefixof "ab" w)
                  (str.in_re w (re.++ (str.to_re "ab") re.all))))

(check-sat)
