
(declare-fun ANY_INV () Bool)

(declare-fun iterm () Int)
(declare-fun iterm1 () Int)
(declare-fun iterm2 () Int)
(declare-fun iterm3 () Int)
(declare-fun iterm4 () Int)

;(assert (= iterm (Int_either_4 (* INT_CONSTS INT_VARS) (+ iterm iterm) INT_CONSTS INT_VARS)))

;(assert (= iterm (* INT_CONSTS INT_VARS)))

;(assert (= ANY_INV (= iterm iterm)))

(assert (= iterm4 (either 1 2 3 4)))
(assert (= iterm3 (either 1 2 3)))
(assert (= iterm2 (either 1 2)))
(assert (= iterm1 (either 0)))

(assert (= ANY_INV (either
  (= (+ iterm4 iterm3 iterm2) 0)
  (= (+ iterm2 iterm3 iterm4) 0)
  (= (+ iterm3 iterm2 iterm4) 0)
  (= (+ iterm4 iterm2 iterm3) 0)
  (= (+ iterm4 iterm3) 0)
  (= (+ iterm3 iterm4) 0)
  (= (+ iterm1 iterm3) 0)
  (= (+ iterm4 iterm1) 0)
)))
