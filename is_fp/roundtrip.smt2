(define-fun is-fp-repr ((n Real)) Bool
  (let ((asfp ((_ to_fp 11 53) RTZ n)))
       (= n (fp.to_real asfp))))

(declare-const a Real)

(assert (is-fp-repr a))

(check-sat)
(get-model)
