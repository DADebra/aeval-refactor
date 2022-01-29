
(declare-fun ANY_INV () Bool)

(declare-fun iterm () Int)

;(assert (= iterm (Int_either_4 (* INT_CONSTS INT_VARS) (+ iterm iterm) INT_CONSTS INT_VARS)))

;(assert (= iterm (* INT_CONSTS INT_VARS)))

;(assert (= ANY_INV (= iterm iterm)))

(assert (= iterm (either 0 1 2 3)))

(assert (= ANY_INV (= (+ iterm iterm iterm) 0)))
