(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var lt Bool)
(declare-var found Bool)
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))
(declare-var lt1 Bool)
(declare-var found1 Bool)

; K-induction succeeded after 16 iterations

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) Bool Bool))

; bitwise < of two numbers

(rule (=> (and (= i #x8000) (not lt) (not found)) (inv a b i lt found)))

(rule (=>
  (and
    (inv a b i lt found)
    (not (= i #x0000))
    (not found)
    (= a1 a)
    (= b1 b)
    (= found1 (or found (not (= (bvand i a) (bvand i b)))))
    (= lt1 (= (bvand i a) #x0000))
    (= i1  (bvlshr i #x0001)))
  (inv a1 b1 i1 lt1 found1)))

(rule (=> (and (inv a b i lt found) found (not (= lt (bvult a b)))) fail))

(query fail)
