; RUN: %solver --model-count %s | %OutputCheck %s
; CHECK: s mc

(set-logic QF_BV)
(declare-fun a () Bool)
(declare-weight a 0.3)
(declare-weight -a 0.4)
(check-sat)
