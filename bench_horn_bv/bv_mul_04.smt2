(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var q (_ BitVec 16))
(declare-var r (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var q1 (_ BitVec 16))
(declare-var r1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

(define-fun bvite ((a (_ BitVec 16)) (b (_ BitVec 16)) (c (_ BitVec 16))) (_ BitVec 16)
  (bvor (bvand (bvneg a) b) (bvand c (bvsub a #x0001))))

(define-fun bvultb ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (bvult a b) #x0001 #x0000))

; same as bv_mul_03.smt2 but the loop guard is based on the counter i \in [0, a]
; bad for k-induction

(rule (=> (and (bvugt a #x0000) (bvult a #x0100) (bvugt b #x0000) (bvult b #x0100) (= q #x0000) (= r a) (= i #x0000)) (inv a b q r i)))

(rule (=>
  (and
    (inv a b q r i)
    (bvule i a)
    (= a1 a)
    (= b1 b)
    (= i1 (bvadd i #x0001))
    (= q1 (bvite (bvultb r b) q (bvadd q #x0001)))
    (= r1 (bvite (bvultb r b) r (bvsub r b))))
  (inv a1 b1 q1 r1 i1)))

(rule (=> (and (inv a b q r i) (not (= a (bvadd r (bvmul b q))))) fail))

(query fail)
