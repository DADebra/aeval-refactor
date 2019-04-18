(declare-var b (_ BitVec 16))
(declare-var b1 (_ BitVec 16))

(declare-rel fail ())
(declare-rel inv ((_ BitVec 16)))

(rule (=> (= b #xf000) (inv b)))

(rule (=> (and (inv b) (bvult b #xffff) (= b1 (bvadd b #x0001))) (inv b1)))

(rule (=> (and (inv b) (not (bvuge b #xf000))) fail))

(query fail)
