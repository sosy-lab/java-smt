
(assert (not (<= 1 (str.to_int "0"))))

(check-sat)
(exit)
