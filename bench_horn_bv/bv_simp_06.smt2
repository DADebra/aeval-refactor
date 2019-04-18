(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var c (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))
(declare-var c1 (_ BitVec 16))

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))

(rule (=> (and (= a #x0000) (= b #x0000)) (inv a b c)))

(rule (=>
  (and
    (inv a b c)
    (= c1 c)
    (= a1 (bvadd a c))
    (= b1 (bvsub b c)))
  (inv a1 b1 c1)))

(rule (=> (and (inv a b c) (not (= a (bvneg b)))) fail))

(query fail)
