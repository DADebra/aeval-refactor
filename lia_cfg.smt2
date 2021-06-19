; Sample LIA CFG for Freqhorn.

; Invariant declaration
(declare-fun ANY_INV () Bool)

; Non-terminal declarations
(declare-fun iconst () Int)
(declare-fun ivar () Int)
(declare-fun bvar () Bool)
(declare-fun term () Int)
(declare-fun fla () Bool)

(assert (= ivar INT_VARS))
(assert (= iconst INT_CONSTS))
(assert (= term (Int_either_5 iconst ivar (* iconst ivar) (+ term term) (mod term iconst))))
(assert (= fla (Bool_either_4 (= term term) (< term term) (not fla) (or fla fla))))
(assert (= ANY_INV (Bool_either_2 (=> fla fla) fla)))

(check-sat)
