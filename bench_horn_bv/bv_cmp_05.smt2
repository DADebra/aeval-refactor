(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var ai (_ BitVec 16))
(declare-var bi (_ BitVec 16))
(declare-var eq Bool)
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))
(declare-var ai1 (_ BitVec 16))
(declare-var bi1 (_ BitVec 16))
(declare-var eq1 Bool)

; K-induction succeeded after 17 iterations

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) Bool))

; constant time bitwise equality of two numbers

(rule (=> (and (= i #x8000) (= a ai) (= b bi) eq) (inv a b i ai bi eq)))

(rule (=>
  (and
    (inv a b i ai bi eq)
    (not (= i #x0000))
    (= eq1 (and eq
      (or
        (and (= (bvand #x0001 ai) #x0000)
          (= (bvand #x0001 bi) #x0000))
        (and (not (= (bvand #x0001 ai) #x0000))
          (not (= (bvand #x0001 bi) #x0000))))))
    (= a1 a)
    (= b1 b)
    (= ai1 (bvlshr ai #x0001))
    (= bi1 (bvlshr bi #x0001))
    (= i1  (bvlshr i #x0001)))
  (inv a1 b1 i1 ai1 bi1 eq1)))

(rule (=> (and (inv a b i ai bi eq) (= i #x0000) (not (= eq (= a b)))) fail))

(query fail)
