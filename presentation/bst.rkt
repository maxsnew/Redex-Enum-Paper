#lang racket

(require redex pict)

(define-language bst

  (t   ::= leaf
           (node opcnn t t))
  
  (opcnn ::= natural
             +inf.0))

(define-judgment-form bst
  #:mode (ordered? I I I)
  [(leq? opcnn_1 opcnn_2)
   ----------------------
   (ordered? leaf opcnn_1 opcnn_2)]
  [(ordered? t_1 opcnn_2 opcnn_1)
   (ordered? t_2 opcnn_1 opcnn_3)
   (leq? opcnn_2 opcnn_1 opcnn_3)
   ----------------
   (ordered? (node opcnn_1 t_1 t_2) opcnn_2 opcnn_3)])

(define-metafunction bst
  [(insert opcnn leaf)
   (node opcnn leaf leaf)]
  [(insert opcnn_1 (node opcnn_2 t_1 t_2))
   (node opcnn_1 (insert opcnn_2 t_1) t_2) ;; Bug !
   (side-condition (term (leq? opcnn_1 opcnn_2)))]
  [(insert opcnn_1 (node opcnn_2 t_1 t_2))
   (node opcnn_2 t_1 (insert opcnn_1 t_2))])

(define-relation bst
  [(leq? opcnn ...)
   ,(apply <= (term (opcnn ...)))])

(define (find-bugs)
  (redex-check 
   bst
   (opcnn t)
   (implies (judgment-holds (ordered? t 0 +inf.0))
            (judgment-holds (ordered? (insert opcnn t)
                                      0 +inf.0)))))