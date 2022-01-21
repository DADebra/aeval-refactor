; Invariant declaration
(declare-fun ANY_INV () Bool)

; Non-terminal declarations
(declare-fun iconst () Int)
(declare-fun ivar () Int)
(declare-fun ivar1 () Int)
(declare-fun ivar2 () Int)
(declare-fun bvar () Bool)
(declare-fun term () Int)
(declare-fun mterm () Int)
(declare-fun doub () Int)
(declare-fun fla () Bool)
(declare-fun concr () Bool)

(assert (= ivar INT_VARS))
(assert (= ivar1 INT_VARS))
(assert (= ivar2 INT_VARS))
(assert (= iconst INT_CONSTS))
(assert (= fla (either
  (<= ivar iconst)
  (<  ivar iconst)
  (>  ivar iconst)
  (>= ivar iconst)
  (=  ivar iconst)
  (<= ivar1 ivar2)
  (< ivar1 ivar2)
  (> ivar1 ivar2)
  (>= ivar1 ivar2)
  (= ivar1 ivar2)
)))
(assert (= ANY_INV (either (or fla fla) fla)))

;(assert (constraint false))
;(assert (constraint (expands fla "(< (* iconst ivar1) (* iconst ivar2))")))
(assert (constraint (distinct_under "fla" ivar1 ivar2)))
;(assert (constraint (equal_under "fla" ivar1 ivar2)))
;(assert (constraint (not_under "fla" ivar1)))
;(assert (constraint (and (= ivar1 ivar2) (equal ivar1) (equal ivar2))))
;(assert (constraint (xor (= iconst (* 1 1)) (equal iconst (* 1 1)))))

;(assert (constraint (=> (expands "fla") (assert (> iconst 0)))))

(check-sat)
