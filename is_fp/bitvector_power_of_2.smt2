(define-fun is-power-of-two ((y (_ BitVec 64))) Bool 
  (= #x0000000000000000 (bvand y (bvsub y #x0000000000000001))))

(declare-const a Int)
(assert (> a (^ 2 -1074)))
(assert (< a (^ 2 1074)))
(assert (> a 2))
(assert (< a (^ 2 64)))
(assert (is-power-of-two ((_ int2bv 64) a)))

(check-sat)
(get-model)
