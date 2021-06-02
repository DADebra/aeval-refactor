; For bench_horn/gcd_2.smt2

; These are special functions; Freqhorn will randomly pick
;   one of the arguments to be the value.
; The naming scheme isn't important; the function name must,
;   however, contain "either".
; E.g., (ieither2 0 1) will sometimes expand to 0, sometimes to 1.
(declare-fun ieither2 (Int Int) Int)
(declare-fun ieither3 (Int Int Int) Int)
(declare-fun ieither4 (Int Int Int Int) Int)

(declare-fun beither2 (Bool Bool) Bool)
(declare-fun beither3 (Bool Bool Bool) Bool)
(declare-fun beither4 (Bool Bool Bool Bool) Bool)
(declare-fun beither5 (Bool Bool Bool Bool Bool) Bool)
(declare-fun beither6 (Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun beither7 (Bool Bool Bool Bool Bool Bool Bool) Bool)

(declare-fun iconst () Int)
(declare-fun ivar () Int)
(declare-fun bconst () Bool)
(declare-fun bvar () Bool)
(declare-fun term () Int)

; Special variable; the root of the CFG. Must be named "inv"
(declare-fun inv () Bool)

;(define-fun-rec term () Int
;    (ieither4 iconst ivar (* iconst ivar) (+ term term))
;)
;
;(define-fun-rec inv () Bool
;    (beither7 bconst bvar (= term term) (< term term) (not inv) (and inv inv) (or inv inv))
;)

; Freqhorn will treat these as terminals and not expand them
(declare-fun _FH_0 () Int)
(declare-fun _FH_1 () Int)
(declare-fun _FH_2 () Int)
(declare-fun _FH_3 () Int)

; Might work in the future
;(assert (= ivar CHC_VARS))
;(assert (= iconst NAT_NUMBERS))

(assert (= ivar (ieither4 _FH_0 _FH_1 _FH_2 _FH_3)))
(assert (= bconst (beither2 true false)))
(assert (= iconst (ieither3 0 -1 1)))
(assert (= term (ieither4 iconst ivar (* iconst ivar) (+ term term))))
(assert (= inv (beither4 (= term term) (< term term) (not inv) (or inv inv))))

(check-sat)
