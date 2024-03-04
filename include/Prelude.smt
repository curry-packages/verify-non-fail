; disable model-based quantifier instantiation (avoid loops)
(set-option :smt.mbqi false)

; For functional types:
(declare-datatypes ( (Func 2) )
  ((par (T1 T2) ( (mk-func (argument T1) (result T2))))))

; Unit type:
(declare-datatypes ( (Unit 0) ) ( ((unit))))

; Pair type:
(declare-datatypes ( (Pair 2) )
  ((par (T1 T2) ( (mk-pair (first T1) (second T2)) ))))

; Maybe type:
(declare-datatypes ( (Maybe 1) ) ((par (T) ( (Nothing) (Just (just T)) ))))

; Either type:
(declare-datatypes ( (Either 2) )
  ((par (T1 T2) ( (Left (left T1)) (Right (right T2))))))

; Ordering type:
(declare-datatypes ( (Ordering 0) ) (( (LT) (EQ) (GT) )))

; Dict type (to represent dictionary variables):
(declare-datatypes ( (Dict 1) ) ((par (T) ( (Dict (dict T)) ))))

