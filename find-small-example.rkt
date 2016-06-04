#lang racket
#|

This searches for a counterexample
ala the discussion in section 2

|#

(require "testing.scrbl"
         "util.rkt"
         data/enumerate/lib)

(define (try-it name e)
  (let/ec k
    (for ([i (in-naturals)])
      (unless (zero? i) (when (zero? (modulo i 100000)) (printf "~a ...\n" (add-commas i))))
      (define t (from-nat e i))
      (when (and (not (bst? t)) (not-quite-bst? t))
        (printf "found counterexample in ~a at ~a\n" name i)
        (k (void))))))

(try-it 'bt/e bt/e)
(try-it 'un-bt/e un-bt/e)
