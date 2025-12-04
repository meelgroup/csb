(set-logic QF_BV)

(declare-const p Bool)
(declare-const q Bool)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))

(declare-weight p 0.8)
(declare-weight -p 1.0)
(declare-weight q 0.3)
(declare-weight -q 0.7)

; If p then x+y = 10, if q then x+y = 5 (mod 16).
(assert (=> p (= (bvadd x y) #xA))) ; 0x0A = 10
(assert (=> q (= (bvadd x y) #x5))) ; 0x05 = 5
(assert (decor p q))

(check-sat)