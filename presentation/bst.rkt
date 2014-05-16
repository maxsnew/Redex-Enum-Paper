#lang racket

(require redex)

(define-language bst
  (t ::= leaf
            (node val t t))
  (val  ::= natural))

(define-relation bst
  [(leq? val_1 val_2)
   ,((term val_1) . <= . (term val_2))])

(define-relation bst
  [(increasing? val_1 val_2 val_3)
   ,((term val_1) . <= . (term val_2))
   ,((term val_2) . <= . (term val_3))])

(define-judgment-form bst
  #:mode (ordered? I)
  [(ordered? leaf)]
  [(ordered? (node val leaf leaf))]
  [(leq? val_1 val_2)
   (ordered? (node val_1 t_1 t_2))
   -------------
   (ordered? (node val_2 (node val_1 t_1 t_2) leaf))]
  [(leq? val_1 val_2)
   (ordered? (node val_2 t_1 t_2))
   --------------
   (ordered? (node val_1 leaf (node val_2 t_1 t_2)))]
  [(increasing? val_1 val_2 val_3)
   ----------------
   (ordered? (node val_2 
                   (node val_1 t_1 t_2)
                   (node val_3 t_3 t_4)))])

(define (==> p q)
  (or (not p) q))

(define-metafunction bst
  [(insert val leaf)
   (node val leaf leaf)]
  [(insert val_1 (node val_2 t_1 t_2))
   (node val_2 (insert val_1 t_1) t_2)
   (where #t ,((term val_1) . <= . (term val_2)))]
  [(insert val_1 (node val_2 t_1 t_2))
   (node val_1 t_1 (insert val_2 t_2)) ;; Bug !
   ])

(redex-check bst (val_1 t_1)
             (==> (judgment-holds (ordered? t_1))
                  (judgment-holds (ordered? (insert val_1 t_1))))
             #:attempts 10000)