(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T2_184 () (_ BitVec 16))
(declare-fun T1_184 () (_ BitVec 8))
(declare-fun T1_185 () (_ BitVec 8))
(assert (and true (= T2_184 (bvor (bvshl ((_ zero_extend 8) T1_185) (_ bv8 16)) ((_ zero_extend 8) T1_184))) (not (= (_ bv1 16) T2_184))))
(check-sat)
(exit)
