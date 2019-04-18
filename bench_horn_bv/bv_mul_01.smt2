(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var c (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var c1 (_ BitVec 16))

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

(rule (=> (and (bvuge a #x0000) (= b #x0000) (= c #x0000)) (inv a b c)))

(rule (=>
  (and
    (inv a b c)
    (bvuge a #x0000)    ; k-induction needs this invariant
    (= c1 (bvadd c a))
    (= a1 a)
    (= b1 (bvadd b #x0001)))
  (inv a1 b1 c1)))

(rule (=> (and (inv a b c) (not (= c (bvmul a b)))) fail))

(query fail)
