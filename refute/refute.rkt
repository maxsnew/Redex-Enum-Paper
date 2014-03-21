#lang racket
(require redex/reduction-semantics)

(define-language L)

(define (try-isabelle)
  (redex-check
   L
   ((any_1 ...) (any_2 ...) natural)
   (let ([xs (term (any_1 ...))]
         [ys (term (any_2 ...))]
         [n (term natural)])
     (equal? (with-handlers ([exn:fail? void])
               (list-ref (append xs ys) (+ (length xs) n)))
             (with-handlers ([exn:fail? void])
               (list-ref xs n))))))

(define (try-dart)
  (redex-check 
   L
   (integer_x integer_y)
   (let ([x (term integer_x)]
         [y (term integer_y)])
     (not (and (not (= x y))
               (= (* x 2) (+ x 10)))))))

(define (build-redex-results try)
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
            (/ (apply + successes) (length successes) 1.)))
  (printf "\n"))

(define (build-quickcheck-results file)
  (cond
    [(file-exists? file)
     (begin0
       (for/list ([x (in-range 1000)])
         (when (zero? (modulo x 50)) (display ".") (flush-output))
         (define sp (open-output-string))
         (define lst
           (process*/ports sp 
                           (open-input-string "")
                           sp
                           file))
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
            #f]))
       (printf "\n"))]
    [else
     (eprintf "Please compile ~a.hs (run `ghc ~a.hs`)\n" file file)
     '()]))

(printf "dart conjecture redex\n")
(report-results (build-redex-results try-dart))

(printf "dart conjecture quickcheck\n")
(report-results (build-quickcheck-results "dart-authors-conjecture"))


(printf "isabelle conjecture redex\n")
(report-results (build-redex-results try-isabelle))

(printf "isabelle conjecture quickcheck\n")
(report-results (build-quickcheck-results "isabelle-authors-conjecture"))
