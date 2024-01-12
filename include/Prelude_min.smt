; disable model-based quantifier instantiation (avoid loops)
(set-option :smt.mbqi false)

; for polymorphic types:
(declare-sort TVar 0)
