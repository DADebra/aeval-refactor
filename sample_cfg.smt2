; Sample CFG for Freqhorn.

; Non-terminal declarations
(declare-fun iconst () Int)
(declare-fun ivar () Int)
(declare-fun bvar () Bool)
(declare-fun term () Int)

; Declaration of invariant. Required. Must match the name of an invariant
;   in the input file. There must only be one invariant per grammar file.
; Sort must be "Bool".
(declare-fun inv () Bool)

; Generic declaration of invariant. Optional. Will match any invariant
;   specified in the input file and not declared by any passed grammar.
; Sort must be "Bool".
;(declare-fun ANY_INV () Bool)

; Special variables:

; Freqhorn will treat these as terminals and not expand them;
;   they have whatever sort is specified by the invariant in the input file.
; They're the variables (arguments) to the invariant
; For invariant "(declare-rel inv (Int Int))", _FH_inv_0 is the first argument to the invariant (of sort Int), _FH_inv_1 is the second, etc.
; Defined by Freqhorn (DO NOT DEFINE HERE).
;(declare-fun _FH_inv_0 () Int)

; Will expand to all variables of given sort.
; Parameterized sorts (e.g. Array) are defined with below pattern;
;   "$" replaces the parenthesis, and "_" replaces the spaces.
; Defined by Freqhorn (DO NOT DEFINE HERE).
;(declare-fun INT_VARS () Int)
;(declare-fun BOOL_VARS () Bool)
;(declare-fun $ARRAY_INT_INT$_VARS () (Array Int Int))

; Expands to all integer constants found in the input file.
; Defined by Freqhorn (DO NOT DEFINE HERE).
;(declare-fun INT_CONSTS () Int)

; Used to indicate that a non-terminal can expand to any
;   of the given arguments. The expansion is picked randomly,
;   with a uniform distribution.
; E.g. (assert (= iconst (either 0 -1 1))) means iconst can be
;   expanded to 0, -1, or 1 randomly.
; Defined by Freqhorn (DO NOT DEFINE HERE).
;(declare-fun either (Int Int Int) Int)
;(declare-fun either (
;   (Array Int Int) (Array Int Int) (Array Int Int) ) (Array Int Int))

(assert (= ivar INT_VARS))
(assert (= iconst (either 0 -1 1)))
(assert (= term (either iconst ivar (* iconst ivar) (+ term term))))
(assert (= inv (either (= term term) (< term term) (not inv) (or inv inv))))

(check-sat)
