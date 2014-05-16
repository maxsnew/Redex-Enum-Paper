#lang racket

(require redex pict)

(define-language bst

  (t   ::= leaf
           (node ext-nat t t))
  
  (ext-nat ::= natural
               +inf.0))

(define-judgment-form bst
  #:mode (bound-ordered? I I I)
  [(leq? ext-nat_1 ext-nat_2)
   ----------------------
   (bound-ordered? leaf ext-nat_1 ext-nat_2)]
  [(bound-ordered? t_1 ext-nat_2 ext-nat_1)
   (bound-ordered? t_2 ext-nat_1 ext-nat_3)
   (leq? ext-nat_2 ext-nat_1 ext-nat_3)
   ----------------
   (bound-ordered? (node ext-nat_1 t_1 t_2) ext-nat_2 ext-nat_3)])

(define-metafunction bst
  [(insert ext-nat leaf)
   (node ext-nat leaf leaf)]
  [(insert ext-nat_1 (node ext-nat_2 t_1 t_2))
   (node ext-nat_1 (insert ext-nat_2 t_1) t_2) ;; Bug !
   (side-condition (term (leq? ext-nat_1 ext-nat_2)))]
  [(insert ext-nat_1 (node ext-nat_2 t_1 t_2))
   (node ext-nat_2 t_1 (insert ext-nat_1 t_2))])

(define-relation bst
  [(leq? ext-nat ...)
   ,(apply <= (term (ext-nat ...)))])

(define (find-bugs)
  (redex-check 
   bst
   (ext-nat t)
   (implies (judgment-holds (bound-ordered? t 0 +inf.0))
            (judgment-holds (bound-ordered? (insert ext-nat t)
                                      0 +inf.0)))))

(define (show-ordered)
  (scale (render-judgment-form bound-ordered?) 1.5))
(define (show-insert)
  (scale (render-metafunction insert) 1.5))