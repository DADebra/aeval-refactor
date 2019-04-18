(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var ai (_ BitVec 16))
(declare-var bi (_ BitVec 16))
(declare-var eq (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))
(declare-var ai1 (_ BitVec 16))
(declare-var bi1 (_ BitVec 16))
(declare-var eq1 (_ BitVec 16))

; K-induction succeeded after 17 iterations

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

; constant time bitwise equality of two numbers, result as bv

(define-fun last_bit_eq ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (= (bvxor (bvand #x0001 a) (bvand #x0001 b)) #x0000) #x0001 #x0000))

(rule (=> (and (= i #x8000) (= a ai) (= b bi) (= eq #x0001)) (inv a b i ai bi eq)))

(rule (=>
  (and
    (inv a b i ai bi eq)
    (not (= i #x0000))
    (= eq1 (bvand eq (last_bit_eq ai bi)))
    (= a1 a)
    (= b1 b)
    (= ai1 (bvlshr ai #x0001))
    (= bi1 (bvlshr bi #x0001))
    (= i1  (bvlshr i #x0001)))
  (inv a1 b1 i1 ai1 bi1 eq1)))

(rule (=> (and (inv a b i ai bi eq) (= i #x0000) (not (= (= eq #x0001) (= a b)))) fail))

(query fail)
