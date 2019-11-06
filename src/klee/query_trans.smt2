; start Z3 query
(assert (not false))
(check-sat)
(reset)
; end Z3 query

; start Z3 query
(declare-fun a_ackermann!0 () Real)

(assert (let ((a!1 (not (= a_ackermann!0
                           (fp.to_real ((_ to_fp 11 53) #x3ff0000000000000))))))
  (not a!1)))
(check-sat)
(get-value (a_ackermann!0))
(reset)
; end Z3 query

; start Z3 query
(declare-fun a_ackermann!33 () Real)

(assert (not (= a_ackermann!33
                (fp.to_real ((_ to_fp 11 53) #x3ff0000000000000)))))
(assert (let ((a!1 (not (= a_ackermann!33
                           (fp.to_real ((_ to_fp 11 53) #x4000000000000000))))))
  (not a!1)))
(check-sat)
(get-value (a_ackermann!33))
(reset)
; end Z3 query
