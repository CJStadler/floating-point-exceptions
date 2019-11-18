(declare-const N Real)
(declare-const M Int)
(declare-const E Int)

(assert (= N (* M (^ 2 E))))

(assert (> N 1))

(check-sat)
(get-model)
