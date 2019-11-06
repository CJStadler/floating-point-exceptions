; start Z3 query
(assert (not false))
(check-sat)
(reset)
; end Z3 query

; start Z3 query
(declare-fun a_ackermann!0 () (_ BitVec 32))
; (define-fun a_float () (_ FloatingPoint 8 24) ((_ to_fp 8 24) a_ackermann!0))
; (define-fun a_real () Real (fp.to_real a_float))

(assert (let ((a!1 (not (fp.eq ((_ to_fp 11 53) roundNearestTiesToEven
                                                ((_ to_fp 8 24) a_ackermann!0))
                               ((_ to_fp 11 53) #x3ff0000000000000)))))
  (not a!1)))
(check-sat)
(get-value (a_ackermann!0))
; (get-value (a_real))
(reset)
; end Z3 query

; start Z3 query
(declare-fun a_ackermann!33 () (_ BitVec 32))
; (define-fun a_float () (_ FloatingPoint 8 24) ((_ to_fp 8 24) a_ackermann!33))
; (define-fun a_real () Real (fp.to_real a_float))

(assert (not (fp.eq ((_ to_fp 11 53) roundNearestTiesToEven
                                     ((_ to_fp 8 24) a_ackermann!33))
                    ((_ to_fp 11 53) #x3ff0000000000000))))
(assert (let ((a!1 (not (fp.eq ((_ to_fp 11 53) roundNearestTiesToEven
                                                ((_ to_fp 8 24) a_ackermann!33))
                               ((_ to_fp 11 53) #x4000000000000000)))))
  (not a!1)))
(check-sat)
(get-value (a_ackermann!33))
; (get-value (a_real))
(reset)
; end Z3 query
