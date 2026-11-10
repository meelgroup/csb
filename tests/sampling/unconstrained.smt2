; Model completion must sample all declared bits, including widths above 64.
(set-logic QF_BV)
(declare-const flag Bool)
(declare-const other Bool)
(declare-const wide (_ BitVec 65))
(declare-const byte (_ BitVec 8))
(assert true)
(check-sat)
(get-model)
