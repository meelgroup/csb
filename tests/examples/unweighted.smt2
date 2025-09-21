(set-logic QF_BV)

(declare-const p Bool)
(declare-const q Bool)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))

(declare-projvar p)
(declare-projvar q)

; If p then x+y = 10, if q then x+y = 5 (mod 16).
(assert (=> p (= (bvadd x y) #xA))) ; 0x0A = 10
(assert (=> q (= (bvadd x y) #x5))) ; 0x05 = 5

(check-sat)