; RUN: %solver -s %s | %OutputCheck %s
; CHECK: ^unsat
; CHECK-NEXT: ^\(c1 c2\)

(set-option :produce-unsat-cores true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (! (bvugt x #x10) :named c1))
(assert (! (bvult x #x05) :named c2))
(assert (! (= x x) :named c3))
(check-sat)
(get-unsat-core)
(exit)
