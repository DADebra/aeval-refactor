
(declare-fun ANY_INV () Bool)

(declare-fun iterm () Int)
(declare-fun iterm2 () Int)
(declare-fun iterm3 () Int)
(declare-fun ics () Int)
(declare-fun ivs () Int)

(assert (= ics (either 0 1 2)))
(assert (= ivs (either _FH_inv_0 _FH_inv_1)))

(assert (= iterm (either ics ivs (+ iterm iterm))))

(assert (= ANY_INV (= iterm iterm)))
