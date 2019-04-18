(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var r (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var r1 (_ BitVec 16))

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

; does not work with k-induction

(rule (=> (and (bvugt a #x0000) (bvult a #x0100) (bvugt b #x0000) (bvult b #x0100) (= r a)) (inv a b r)))

(rule (=>
  (and
    (inv a b r)
    (bvuge r b)
    (= a1 a)
    (= b1 b)
    (= r1 (bvsub r b)))
  (inv a1 b1 r1)))

(rule (=> (and (inv a b r) (bvult r b) (not (= r (bvurem a b)))) fail))

(query fail)
