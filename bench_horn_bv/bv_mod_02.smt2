(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var r (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))
(declare-var r1 (_ BitVec 16))
(declare-var rtmp (_ BitVec 16))

; K-induction succeeded after 17 iterations

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

(define-fun bvultb ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (bvult a b) #x0001 #x0000))

; constant time division

(rule (=> (and (= i #x8000) (= r #x0000)) (inv a b i r)))

(rule (=>
  (and
    (inv a b i r)
    (not (= i #x0000))
    (= a1 a)
    (= b1 b)
    (= rtmp (bvor (bvshl r #x0001) (bvultb #x0000 (bvand i a))))
    (= r1 (ite (bvuge rtmp b) (bvsub rtmp b) rtmp))
    (= i1  (bvlshr i #x0001)))
  (inv a1 b1 i1 r1)))

(rule (=> (and (inv a b i r) (= i #x0000) (not (= r (bvurem a b)))) fail))

(query fail)
