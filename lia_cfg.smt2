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

(assert (= term (Int_either_3 ivar (* iconst ivar) (+ term term))))
(assert (= mterm (Int_either_5 iconst ivar (* iconst ivar) (+ mterm mterm) (Int_prio (mod term iconst) 0.1))))
(assert (= fla (Bool_either_4 (= mterm mterm) (< mterm mterm) (not fla) (or fla fla))))
(assert (= ANY_INV (Bool_either_2 fla (Bool_prio (=> fla fla) 0.2))))

(check-sat)
