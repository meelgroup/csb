; False assignments must survive conversion from the CMSGen model.
(set-logic QF_BV)
(declare-const yes Bool)
(declare-const no Bool)
(declare-const copy Bool)
(assert yes)
(assert (not no))
(assert (= copy no))
(check-sat)
