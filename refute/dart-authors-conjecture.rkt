#lang racket
(require redex/reduction-semantics)
(provide try-dart)

(define (try-dart)
  ;; START
  (define-language empty-language)
  (redex-check 
   empty-language
   (integer_x integer_y)
   (let ([x (term integer_x)]
         [y (term integer_y)])
     (not (and (not (= x y))
               (= (* x 2) (+ x 10))))))
  ;; STOP
  )
