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

(define redex-results
  (for/list ([x (in-range 1000)])
    (define sp (open-output-string))
    (parameterize ([current-output-port sp])
      (try))
    (define m (regexp-match #rx"counterexample found after ([0-9]+) attempts"
                            (get-output-string sp)))
    (cond
      [m (string->number (list-ref m 1))]
      [else #f])))

(define (report-results results)
  (define successes (filter number? results))
  (printf "~a failures\n" (- (length results) (length successes)))
  (printf "~a successes\n" (length successes))
  (unless (null? successes)
    (printf "~a average attempts for each success\n"
            (/ (apply + successes) (length successes) 1.))))

(define quickcheck-results
  (cond
    [(file-exists? "isabelle-authors-conjecture")
     (for/list ([x (in-range 1000)])
       (when (zero? (modulo x 50)) (display ".") (flush-output))
       (define sp (open-output-string))
       (define lst
         (process*/ports sp 
                         (open-input-string "")
                         sp
                         "isabelle-authors-conjecture"))
       ((list-ref lst 4) 'wait)
       (define m
         (regexp-match #rx"Falsifiable [(]after ([0-9]+) tests"
                       (get-output-string sp)))
       (cond
         [m (string->number (list-ref m 1))]
         [else
          (unless (regexp-match #rx"OK, passed [0-9]+ tests."
                                (get-output-string sp))
            (eprintf "could not parse quickcheck's output:\n~a"
                     (get-output-string sp))
            (exit -1))
          #f]))]
    [else
     (eprintf "Please compile isabelle-authors-conjecture.hs (ghc isabelle-authors-conjecture.h)\n")
     '()]))
(printf "\n")

(printf "redex\n")
(report-results redex-results)
(printf "\nquickcheck\n")
(report-results quickcheck-results)
