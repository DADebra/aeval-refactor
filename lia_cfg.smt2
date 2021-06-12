; Sample CFG for Freqhorn.

; Declaration of invariant. Required. Must match the name of an invariant
;   in the input file. There must only be one invariant per grammar file.
;   Sort must be "Bool".
(declare-fun ANY_INV () Bool)

; Special variables:

; Freqhorn will treat these as terminals and not expand them;
;   they have whatever sort is specified by the invariant in the input file.
; _FH_0 is the first argument to the invariant, _FH_1 is the second, etc.
; Defined by Freqhorn (DO NOT DEFINE HERE).
;(declare-fun _FH_0 () Int)

; Will expand to all variables of given sort.
; Parameterized sorts (e.g. Array) are defined with below pattern;
;   "$" replaces the parenthesis, and "_" replaces the spaces.
; Defined by Freqhorn (DO NOT DEFINE HERE).
;(declare-fun INT_VARS () Int)
;(declare-fun BOOL_VARS () Bool)
;(declare-fun $ARRAY_INT_INT$_VARS () (Array Int Int))

; Non-terminal declarations
(declare-fun iconst () Int)
(declare-fun ivar () Int)
(declare-fun bvar () Bool)
(declare-fun term () Int)

(assert (= ivar INT_VARS))
(assert (= iconst INT_CONSTS))
(assert (= term (Int_either_5 iconst ivar (* iconst ivar) (+ term term) (mod term iconst))))
(assert (= ANY_INV (Bool_either_4 (= term term) (< term term) (not ANY_INV) (or ANY_INV ANY_INV))))

(check-sat)
