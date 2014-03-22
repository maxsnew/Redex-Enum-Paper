#lang racket
(require redex/reduction-semantics)
(provide try-isabelle)

(define-language empty-language)

(define (try-isabelle)
  ;; START
  (define (nth l n)
    (with-handlers ([exn:fail? void])
      (list-ref l n)))
  (redex-check
   empty-language
   ((any_1 ...) (any_2 ...) natural)
   (let ([xs (term (any_1 ...))]
         [ys (term (any_2 ...))]
         [n (term natural)])
     (equal? (nth (append xs ys) (+ (length xs) n))
             (nth xs n))))
  ;; STOP
  )
