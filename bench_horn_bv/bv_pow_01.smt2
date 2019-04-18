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

; calculates the sum of powers of 2 based on the binary representation of a number and proves that it equals the number

; limitation: #x8000 = 2^15 = 32768
; if b >= 2^15 then i might exceed 2^15 and thus i1 may overflow, and thus the verification is not reliable

(rule (=> (and (= i #x0001) (= it #x0000) (bvuge b #x0000) (bvult b #x8000)) (inv b i it)))

(rule (=>
  (and
    (inv b i it)
    (bvule i b)
    (= it1 (bvadd it (bvand (bvneg (bvultb #x0000 (bvand i b))) i)))
    (= i1  (bvshl i #x0001))
    (= b1 b))
  (inv b1 i1 it1)))

(rule (=> (and (inv b i it) (bvugt i b) (not (= b it))) fail))

(query fail)
