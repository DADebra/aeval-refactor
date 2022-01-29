
(declare-fun ANY_INV () Bool)

(declare-fun iterm () Int)
(declare-fun iterm2 () Int)
(declare-fun ics () Int)
(declare-fun ivs () Int)

(assert (= ics (either 0 1 2)))
(assert (= ivs (either _FH_inv_0 _FH_inv_1)))

(assert (= iterm (either (+ iterm iterm) ics ivs)))
(assert (= iterm2 (either (+ ics ivs) (+ ivs ics))))

;(assert (= iterm (* INT_CONSTS INT_VARS)))

(assert (= ANY_INV (= iterm iterm2)))
;(assert (= ANY_INV (= iterm 0)))

;(assert (= iterm (either 0 1 2 3)))

;(assert (= ANY_INV (= (+ iterm iterm iterm) 0)))
