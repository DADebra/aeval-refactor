(declare-var a (_ BitVec 16))
(declare-var b (_ BitVec 16))
(declare-var a1 (_ BitVec 16))
(declare-var b1 (_ BitVec 16))

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16) (_ BitVec 16)))

(rule (=> (and (= a #x0000) (= b #x0000)) (inv a b)))

(rule (=>
  (and
    (inv a b)
    (= a1 (bvadd a #x0001))
    (= b1 (bvsub b #x0001)))
  (inv a1 b1)))

(rule (=> (and (inv a b) (not (= a (bvneg b)))) fail))

(query fail)
