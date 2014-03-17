#lang racket
(require redex/reduction-semantics)

(define-language L)

(define (prop xs ys n)
  (equal? (with-handlers ([exn:fail? void])
            (list-ref (append xs ys) (+ (length xs) n)))
          (with-handlers ([exn:fail? void])
            (list-ref xs n))))

(define (try)
  (redex-check
   L
   ((any_1 ...) (any_2 ...) natural)
   (prop (term (any_1 ...))
         (term (any_2 ...))
         (term natural))))

(define results
  (for/list ([x (in-range 1000)])
    (define sp (open-output-string))
    (parameterize ([current-output-port sp])
      (try))
    (define m (regexp-match #rx"counterexample found after ([0-9]+) attempts"
                            (get-output-string sp)))
    (cond
      [m (string->number (list-ref m 1))]
      [else #f])))

(define successes (filter number? results))
(printf "~a failures\n" (- (length results) (length successes)))
(printf "~a successes\n" (length successes))
(printf "~a average attempts for each success\n"
        (/ (apply + successes) (length successes) 1.))
