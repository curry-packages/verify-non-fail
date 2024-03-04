; disable model-based quantifier instantiation (avoid loops)
(set-option :smt.mbqi false)

; For functional types:
(declare-datatypes ( (Func 2) )
  ((par (T1 T2) ( (mk-func (argument T1) (result T2))))))

