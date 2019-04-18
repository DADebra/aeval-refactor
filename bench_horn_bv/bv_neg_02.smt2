(declare-var a (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var n (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))
(declare-var n1 (_ BitVec 16))

; K-induction succeeded after 16 iterations

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

; two's complement

(rule (=> (and (= i #x0001) (= n #x0000)) (inv a i n)))

(rule (=>
  (and
    (inv a i n)
    (bvule i #x8000)
    (= a1 a)
    (or
      (and (= (bvand i a) #x0000) (= n1 (bvor n i)))
      (and (not (= (bvand i a) #x0000)) (= n1 n))
    )
    (= i1 (ite (= i #x8000) #xffff (bvshl i #x0001))))
  (inv a1 i1 n1)))

(rule (=> (and (inv a i n) (= i #xffff) (not (= #x0000 (bvadd (bvor a n) #x0001)))) fail))

(query fail)
