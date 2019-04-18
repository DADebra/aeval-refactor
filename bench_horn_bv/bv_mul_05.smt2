(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var r (_ BitVec 16))
(declare-var q (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))
(declare-var r1 (_ BitVec 16))
(declare-var q1 (_ BitVec 16))
(declare-var rtmp (_ BitVec 16))

; K-induction succeeded after 17 iterations

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

(define-fun bvultb ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (bvult a b) #x0001 #x0000))

; constant time division

(rule (=> (and (= i #x8000) (= r #x0000) (= q #x0000)) (inv a b i r q)))

(rule (=>
  (and
    (inv a b i r q)
    (not (= i #x0000))
    (= a1 a)
    (= b1 b)
    (= rtmp (bvor (bvshl r #x0001) (bvultb #x0000 (bvand i a))))
    (= r1 (ite (bvuge rtmp b) (bvsub rtmp b) rtmp))
    (= q1 (ite (bvuge rtmp b) (bvor q i) q))
    (= i1  (bvlshr i #x0001)))
  (inv a1 b1 i1 r1 q1)))

(rule (=> (and (inv a b i r q) (= i #x0000) (not (= a (bvadd r (bvmul b q))))) fail))

(query fail)
