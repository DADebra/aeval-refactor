(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var i (_ BitVec 16))
(declare-var j (_ BitVec 16))
(declare-var at (_ BitVec 16))
(declare-var jt (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var i1 (_ BitVec 16))
(declare-var j1 (_ BitVec 16))
(declare-var at1 (_ BitVec 16))

; K-induction succeeded after 16 iterations, 10 sec

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

(define-fun bvultb ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (bvult a b) #x0001 #x0000))

; fast calculation of a*b using the sum of powers of 2

(rule (=> (and (= i #x0000) (= j #x0001) (= at a)
    (bvuge a #x0000) (bvule a #x0100) (bvuge b #x0000) (bvule b #x0100)) (inv a b i j at)))

(rule (=>
  (and
    (inv a b i j at)
    (bvule j b)
    (= i1  (bvadd i  (bvand (bvneg (bvultb #x0000 (bvand j b))) at)))
    (= j1  (bvshl j  #x0001))
    (= at1 (bvshl at #x0001)))
  (inv a b i1 j1 at1)))

(rule (=> (and (inv a b i j at) (bvugt j b) (not (= i (bvmul a b)))) fail))

(query fail)

