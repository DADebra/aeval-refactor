(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var eq Bool)
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))
(declare-var eq1 Bool)

; K-induction succeeded after 17 iterations

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) Bool))

; bitwise equality of two numbers

(rule (=> (and (= i #x0001) eq) (inv a b i eq)))

(rule (=>
  (and
    (inv a b i eq)
    (bvule i #x8000)
    (= a1 a)
    (= b1 b)
    (= eq1 (and eq (= (bvand i a) (bvand i b))))
    (= i1 (ite (= i #x8000) #xffff (bvshl i #x0001))))
  (inv a1 b1 i1 eq1)))

(rule (=> (and (inv a b i eq) (= i #xffff) (not (= eq (= a b)))) fail))

(query fail)
