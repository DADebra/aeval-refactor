(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var c Bool)
(declare-var d (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))
(declare-var c1 Bool)
(declare-var d1 (_ BitVec 16))

; K-induction succeeded after 17 iterations

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) Bool (_ BitVec 16)))

(rule (=> (and (= i #x0001) (not c) (= d #x0000)) (inv a b i c d)))

(rule (=>
  (and
    (inv a b i c d)
    (bvule i #x8000)
    (= a1 a)
    (= b1 b)
    (or
      (and (= (bvand i a) #x0000) (= (bvand i b) #x0000) (not c) (not c1) (= d1 d))
      (and (= (bvand i a) #x0000) (= (bvand i b) #x0000) c (not c1) (= d1 (bvor d i)))
      (and (= (bvand i a) #x0000) (= (bvand i b) i) (not c) (not c1) (= d1 (bvor d i)))
      (and (= (bvand i a) i) (= (bvand i b) #x0000) (not c) (not c1) (= d1 (bvor d i)))
      (and (= (bvand i a) i) (= (bvand i b) #x0000) c c1 (= d1 d))
      (and (= (bvand i a) #x0000) (= (bvand i b) i) c c1 (= d1 d))
      (and (= (bvand i a) i) (= (bvand i b) i) (not c) c1 (= d1 d))
      (and (= (bvand i a) i) (= (bvand i b) i) c c1 (= d1 (bvor d i)))
    )
    (= i1 (ite (= i #x8000) #xffff (bvshl i #x0001))))
  (inv a1 b1 i1 c1 d1)))

(rule (=> (and (inv a b i c d) (= i #xffff) (not (= d (bvadd a b)))) fail))

(query fail)
