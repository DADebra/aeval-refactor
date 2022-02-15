; Sample LIA CFG for Freqhorn.

; Invariant declaration
(declare-fun ANY_INV () Bool)

; Non-terminal declarations
(declare-fun iconst () Int)
(declare-fun ivar () Int)
(declare-fun bvar () Bool)
(declare-fun term () Int)
(declare-fun mterm () Int)
(declare-fun fla () Bool)

(assert (= ivar INT_VARS))
(assert (= iconst INT_CONSTS))

(assert (= term (either ivar (* iconst ivar) (+ term term))))
(assert (= mterm (either iconst ivar (* iconst ivar) (+ mterm mterm) (mod term iconst))))
(assert (= fla (either (= mterm mterm) (< mterm mterm) (not fla) (or fla fla))))
(assert (= ANY_INV (either fla (=> fla fla))))

(check-sat)
