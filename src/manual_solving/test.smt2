(define-fun DBL_MAX () Real
179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0)

(define-fun DBL_MIN () Real
0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000222507385850720138309023271733240406421921598046233183055332741688720443481391819585428315901251102056406733973103581100515243416155346010885601238537771882113077799353200233047961014744258363607192156504694250373420837525080665061665815894872049117996859163964850063590877011830487479978088775374994945158045160505091539985658247081864511353793580499211598108576)

(define-fun mult_overflow ((a Real) (b Real)) Bool
  (> (abs (* a b)) DBL_MAX))

(define-fun mult_underflow ((a Real) (b Real)) Bool
  (and (> (abs (* a b)) 0.0)
       (< (abs (* a b)) DBL_MIN)))

(declare-const v Real)
(declare-const w Real)
(declare-const r Real)

(assert (not (mult_overflow r r)))

(push)
(assert (mult_underflow r r))
(check-sat)
(get-model)
(pop)
