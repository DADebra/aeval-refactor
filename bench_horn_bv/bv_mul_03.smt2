(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var q (_ BitVec 16))
(declare-var r (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var q1 (_ BitVec 16))
(declare-var r1 (_ BitVec 16))

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

(rule (=> (and (bvugt a #x0000) (bvult a #x0100) (bvugt b #x0000) (bvult b #x0100) (= q #x0000) (= r a)) (inv a b q r)))

(rule (=>
  (and
    (inv a b q r)
    (bvuge r b)
    (= a1 a)
    (= b1 b)
    (= q1 (bvadd q #x0001))
    (= r1 (bvsub r b)))
  (inv a1 b1 q1 r1)))

; does not work after adding (bvult r b) to the last rule (but it should)

(rule (=> (and (inv a b q r) (not (= a (bvadd r (bvmul b q))))) fail))

(query fail)
