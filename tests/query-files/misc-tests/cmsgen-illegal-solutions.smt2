; Regression test for https://github.com/meelgroup/csb/issues/14
; CMSGen used to return solutions violating (v1 or not v2), i.e. v1 = false
; and v2 = true.
; RUN: %solver -s -n 1000 %s > %t.out
; Models must have been produced.
; RUN: test "$(grep -c '^(model' %t.out)" -eq 1000
; The forbidden assignment (v1 = false, v2 = true) must never appear.
; RUN: tr '\n' ' ' < %t.out > %t.flat
; RUN: not grep -E 'v1\| \(\) Bool false \) *\( define-fun \|v2\| \(\) Bool true' %t.flat

(set-logic QF_BV)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)
(assert (or v1 (not v2)))
(check-sat)
