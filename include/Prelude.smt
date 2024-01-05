; disable model-based quantifier instantiation (avoid loops)
(set-option :smt.mbqi false)

; For polymorphic types:
(declare-sort TVar 0)

; Unit type:
(declare-datatypes () ((Unit (unit))))

; Pair type:
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

; For functional types:
(declare-datatypes (T1 T2) ((Func (mk-func (argument T1) (result T2)))))

; Maybe type:
(declare-datatypes (T) ((Maybe (Nothing) (Just (just T)))))

; Either type:
(declare-datatypes (T1 T2) ((Either (Left (left T1)) (Right (right T2)))))
  
; Ordering type:
(declare-datatypes () ((Ordering (LT) (EQ) (GT))))

; Dict type (to represent dictionary variables):
(declare-datatypes (T) ((Dict (Dict (dict T)))))

