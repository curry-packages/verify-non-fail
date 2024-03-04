; IS
;   (v1 > 0) && ((v1 > 0) && (case (MkPair v1 v1) of
;   MkPair v8 v9 -> not ((v8 + v9) > 0)))
; UNSATISFIABLE?

; disable model-based quantifier instantiation (avoid loops)
(set-option :smt.mbqi false)

; For functional types:
(declare-datatypes ( (Func 2) )
  ((par (T1 T2) ( (mk-func (argument T1) (result T2))))))


; User-defined datatypes:
(declare-datatypes
 ((TestTuple_Pair 2))
 ((par
   (T0 T1)
   ((TestTuple_MkPair (sel1-TestTuple_MkPair T0) (sel2-TestTuple_MkPair T1))))))

; Polymorphic sorts:


; Free variables:
(declare-const x1 Int)
(declare-const x42 (TestTuple_Pair Int Int))

(assert (= x42 (TestTuple_MkPair x1 x1)))

; Boolean formula of assertion (known properties):
(assert
 (and (> x1 0) (> x1 0) (match
                         x42
                         (((TestTuple_MkPair x8 x9) (not (> (+ x8 x9) 0)))))))

; check satisfiability:
(check-sat)
