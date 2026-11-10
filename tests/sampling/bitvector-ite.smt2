; Original reproducer from https://github.com/meelgroup/csb/issues/14.
(set-logic QF_BV)
(declare-const Z.cond1 Bool)
(declare-const Z.cond2 Bool)
(declare-const Z.a (_ BitVec 2))
(declare-const Z.b (_ BitVec 2))
(declare-const Z.c (_ BitVec 2))
(declare-const Z.result (_ BitVec 32))
(assert
  (and
    (and
      (and true (= Z.result (concat (concat #b00 #x0000000)
        (ite Z.cond1 Z.a (ite Z.cond2 Z.b Z.c)))))
      (not (= ((_ extract 1 1) Z.a) #b1)))
    (and (not (= ((_ extract 1 1) Z.b) #b1))
         (not (= ((_ extract 1 1) Z.c) #b1)))))
(check-sat)
