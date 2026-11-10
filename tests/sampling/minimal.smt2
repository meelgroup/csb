; Reduced reproducer from https://github.com/meelgroup/csb/issues/14.
(set-logic QF_BV)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)
(assert (or v1 (not v2)))
(check-sat)
