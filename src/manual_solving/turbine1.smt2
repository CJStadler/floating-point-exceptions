(define-fun DBL_MAX () Real
179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0)

(define-fun DBL_MIN () Real
0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000222507385850720138309023271733240406421921598046233183055332741688720443481391819585428315901251102056406733973103581100515243416155346010885601238537771882113077799353200233047961014744258363607192156504694250373420837525080665061665815894872049117996859163964850063590877011830487479978088775374994945158045160505091539985658247081864511353793580499211598108576)

;; Check if the result of a multiplication, addition, or subtraction overflowed.
(define-fun check_overflow ((result Real)) Bool
  (> (abs result) DBL_MAX))

;; Check if the result of a multiplication, addition, or subtraction underflowed.
(define-fun check_underflow ((result Real)) Bool
  (and (> (abs result) 0.0)
       (< (abs result) DBL_MIN)))

(define-fun div_invalid ((num Real) (denom Real)) Bool
  (and (= denom 0.0) (= num 0.0)))

(define-fun div_by_zero ((num Real) (denom Real)) Bool
  (and (= denom 0.0) (not (= num 0.0))))

(define-fun div_overflow ((num Real) (denom Real)) Bool
  (> (abs num) (* (abs denom) DBL_MAX)))

(define-fun div_underflow ((num Real) (denom Real)) Bool
  (and (> (abs num) 0.0)
       (< (abs num) (* (abs denom) DBL_MIN))))

(declare-const v Real)
(declare-const w Real)
(declare-const r Real)

;; Check (r * r)
(define-fun t1 () Real (* r r))

(push)
(assert (check_overflow t1))
(check-sat)
(get-model)
(pop)

(push)
(assert (check_underflow t1))
(check-sat)
(get-model)
(pop)

;; Check (2.0 / t1)
(define-fun t2 () Real (/ 2.0 t1))

(push)
(assert (div_invalid 2.0 t1))
(check-sat)
(get-model)
(pop)

(push)
(assert (div_by_zero 2.0 t1))
(check-sat)
(get-model)
(pop)

(push)
(assert (div_overflow 2.0 t1))
(check-sat)
(get-model)
(pop)

(push)
(assert (div_underflow 2.0 t1))
(check-sat)
(get-model)
(pop)

;; Check (3 + t2)
(define-fun t3 () Real (+ 3.0 t2))

(push)
(assert (check_overflow t3))
(check-sat)
(get-model)
(pop)

(push)
(assert (check_underflow t3))
(check-sat)
(get-model)
(pop)

