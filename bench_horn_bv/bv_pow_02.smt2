(declare-var b (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var it (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))
(declare-var it1 (_ BitVec 16))

; K-induction succeeded after 16 iterations

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

(define-fun bvultb ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (bvult a b) #x0001 #x0000))

; same as bv_pow_01.smt2, but i in the loop guard is bounded by 2^15 now

(rule (=> (and (= i #x0001) (= it #x0000) (bvuge b #x0000) (bvult b #x8000)) (inv b i it)))

(rule (=>
  (and
    (inv b i it)
    (bvult i #x8000)
    (= it1 (bvadd it (bvand (bvneg (bvultb #x0000 (bvand i b))) i)))
    (= i1  (bvshl i #x0001))
    (= b1 b))
  (inv b1 i1 it1)))

;(rule (=> (and (inv b i it) (not (bvult i #x8000)) (not (= i #x8000))) fail))

(rule (=> (and (inv b i it) (= i #x8000) (not (= b it))) fail))

(query fail)
