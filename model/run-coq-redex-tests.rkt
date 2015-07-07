#lang at-exp racket

(require (prefix-in m: "redex-model.rkt" )
         (prefix-in m: "redex-model-test.rkt" )
         racket/runtime-path
         redex/reduction-semantics
         rackunit/log
         (prefix-in d: data/enumerate/lib))

;; this file gets overwritten
(define-runtime-path scratch.v "scratch.v")

(define (check fn) (and (file-exists? fn) 
                        (string->path fn)))
(define coqc
  (or (find-executable-path "coqc")
      (check "/opt/local/bin/coqc")))

(unless coqc (error 'run-coq-redex-tests.rkt "couldn't find coqc"))

(struct test-case (e n v) #:transparent)

;; builds a list of test cases for the nats up to `n'
(define/contract (build-test-cases e n)
  (-> m:e/unfair? exact-nonnegative-integer? (listof test-case?))
  (for/list ([i (in-range n)])
    (build-test-case e i)))

  ;; build-test-case : enum[redex-model-term] nat -> test-case?
(define (build-test-case e n)
  (test-case e n (d:from-nat (term (m:to-enum ,e)) n)))

(define (run-tests . arg-test-cases) 
  (define test-cases (flatten arg-test-cases))
  (define coq-results (run-some-in-coq test-cases))
  (for ([a-test-case (in-list test-cases)]
        [coq-result (in-list coq-results)])
    (match* (a-test-case coq-result)
      [((test-case redex-e orig-n val) 
        (cons (cons coq-v coq-trace)
              (cons coq-n _coq-backwards-trace)))
       (define-values (redex-v redex-trace) (m:from-nat+trace redex-e orig-n))
       (define (check-it failed? fmt-str . args)
         (test-log! failed?)
         (unless failed?
           (eprintf "FAILED:\n enum: ~s\n n: ~s\n val: ~s\n ~a\n\n"
                    redex-e 
                    orig-n 
                    val
                    (apply format fmt-str args))))
       (check-it (equal? orig-n coq-n) "different nats; coq-n ~a" coq-n)
       (check-it (equal? coq-v val) "different values; coq-v ~a" coq-v)
       (check-it (equal? redex-v val) "different values; redex-v ~a" redex-v)
       (check-it (equal? coq-trace redex-trace)
                 "different traces:\n    coq ~s\n  redex ~s" 
                 coq-trace
                 redex-trace)])))

(define coq-prefix
  @list{Unset Printing Notations.
        Set Printing Depth 10000.
        Require Import Enum.All.

        Definition from_nat @"{ty}" @"(e: Enum ty)" n :=
          proj1_sig (Enumerates_from_dec e n).

        Definition to_nat @"{ty}" @"(e : Enum ty)" v :=
          proj1_sig (Enumerates_to_dec e v).

        Definition SwapConsBij' : Bijection (nat * nat) (nat * nat) :=
          SwapConsBij.
        Definition Nat_To_Map_Of_Swap_Zero_With i :=
          E_Map (SwapWithZeroBijection i) E_Nat.

})

(define (run-some-in-coq test-cases)
  (define results
    (run-coq
     (λ (port)
       (define (o str) (display str port))
       (define (o-enum e)
         (match e
           [`(below/e ∞) (o "E_Nat")]
           [`(or/e ,e1 ,e2)
            (o "(E_Sum ")
            (o-enum e1)
            (o " ")
            (o-enum e2)
            (o ")")]
           [`(cons/e ,e1 ,e2)
            (o "(E_Pair ")
            (o-enum e1)
            (o " ")
            (o-enum e2)
            (o ")")]
           [`(unfair-cons/e ,e1 ,e2)
            (o "(E_Unfair_Pair ")
            (o-enum e1)
            (o " ")
            (o-enum e2)
            (o ")")]
           [`(map/e swap-cons swap-cons ,e)
            (o "(E_Map SwapConsBij' ")
            (o-enum e)
            (o ")")]
           [`(dep/e inf ,e nat->map-of-swap-zero-with)
            (o "(E_Dep ")
            (o-enum e)
            (o " Nat_To_Map_Of_Swap_Zero_With)")]
           [`(trace/e ,i ,e)
            (o "(E_Trace ")
            (o (match i
                 [0 "zero"]
                 [1 "one"]
                 [2 "two"]
                 [3 "three"]))
            (o " ")
            (o-enum e)
            (o ")")]))

       (define (o-v e v)
         (match* (e v)
           [(`(below/e ∞) (? number?))
            (o (format "~a" v))]
           [(`(,(or 'cons/e 'unfair-cons/e) ,e1 ,e2) (cons a b))
            (o "(pair ")
            (o-v e1 a)
            (o " ")
            (o-v e2 b)
            (o ")")]
           [(`(map/e ,f-in ,f-out ,e) v)
            (o-v e v)]
           [(`(dep/e inf ,e nat->map-of-swap-zero-with) (cons i j))
            (o "(pair ")
            (o-v e i)
            (o " ")
            (o-v `(below/e ∞) j)
            (o ")")]
           [(`(or/e ,e1 ,e2) (cons 0 b))
            (o "(inl ")
            (o-v e1 b)
            (o ")")]
           [(`(or/e ,e1 ,e2) (cons 1 b))
            (o "(inr ")
            (o-v e2 b)
            (o ")")]
           [(`(trace/e ,i ,e) v)
            (o-v e v)]))
       
       (for ([a-run (in-list test-cases)])
         (match a-run
           [(test-case e n v)
            (fprintf port "Eval compute in (from_nat ")
            (o-enum e)
            (o " ")
            (o (format "~a" n))
            (o " , ")

            (fprintf port "to_nat ")
            (o-enum e)
            (o " ")
            (o-v e v)
            (o ").\n")])))))
  results)

;; for debugging system* calls
(define (psystem* . args)
  (for ([arg (in-list args)])
    (display arg)
    (display " "))
  (displayln "")
  (apply system* args))

(define (run-coq print-suffix)
  (call-with-output-file scratch.v
    (λ (port)
      (for ([s (in-list coq-prefix)])
        (display s port))
      (newline port)
      (newline port)
      (print-suffix port))
    #:exists 'replace)

  (define sp (open-output-string))
  (parameterize ([current-input-port (open-input-string "")]
                 [current-output-port sp])
    (define command-line
      (list (format "~a" coqc)
            "-R"
            (format "~a"
                    (simplify-path
                     (let-values ([(base name dir?) (split-path scratch.v)])
                       (build-path base "coq"))))
            "Enum"
            (format "~a" scratch.v)))
    (apply system* command-line))
  (define resultsp (open-input-string (get-output-string sp)))
  (with-handlers ([exn:fail? (λ (x)
                               (eprintf "failed to convert:\n")
                               (display (get-output-string sp) (current-error-port))
                               (newline (current-error-port))
                               (raise x))])

    (properly-parenthesize-and-convert-results
     (let loop ()
       (define r (read resultsp))
       (if (eof-object? r)
           '()
           (cons r (loop)))))))

(define (properly-parenthesize-and-convert-results lst)
  (let loop ([lst lst])
    (cond
      [(null? lst) '()]
      [else
       (unless (equal? (car lst) '=)
         (error 'properly-parenthesize-results "expected an = at ~s" 
                (car lst)))
       (define-values (next-one rest)
         (splitf-at (cdr lst) (λ (x) (not (equal? x ':)))))
       (unless (pair? rest)
         (error 'properly-parenthesize-results "expected a :, but lst terminated"))
       (define-values (its-type rest2)
         (splitf-at rest (λ (x) (not (equal? x '=)))))
       (cons (to-racket next-one) (loop rest2))])))

(struct coq-pair (l r) #:transparent)
(struct coq-none () #:transparent)

;; converts the `read` version of a value from Coq into the corresponding Racket value
(define (to-racket exp)
  
  (define (coq-null? e)
    (match e
      [`nil #t]
      [_ #f]))
  
  (let loop ([exp exp])
    (match exp
      [`(pair ,a ,b) (cons (loop a) (loop b))]
      [`(cons ,a ,b) (cons (loop a) (loop b))]
      [`nil '()]
      [`(Tracing ,ts ...)
       (for/hash ([t (in-list ts)]
                  [i (in-naturals)]
                  #:unless (coq-null? t))
         (define nums (loop t))
         (values i
                 (if (list? nums)
                     (apply set nums)
                     nums)))]
      [`(S ,n) (+ (loop n) 1)]
      [`O 0]
      [`(Some ,v) (loop v)]
      [`(None) (coq-none)]
      ;; V_Pairs are just 'cons' pairs in the Redex model
      [`(pair ,a ,b) (cons (loop a) (loop b))]
      [`(inr ,v) 
       ;; right sums in the Coq model match up to the `or r' rule in the Redex model
       (cons 1 (loop v))]
      [`(inl ,v) 
       ;; left sums in the Coq model match up to the `or l' rule in the Redex model
       (cons 0 (loop v))])))

(run-tests
 (build-test-cases '(below/e ∞) 100)
 (build-test-cases '(cons/e (below/e ∞) (below/e ∞)) 100)
 (build-test-cases '(unfair-cons/e (below/e ∞) (below/e ∞)) 100)
 (build-test-cases '(or/e (below/e ∞) (below/e ∞)) 100)
 (build-test-cases '(cons/e (cons/e (trace/e 0 (below/e ∞))
                                    (trace/e 1 (below/e ∞)))
                            (cons/e (trace/e 2 (below/e ∞))
                                    (trace/e 3 (below/e ∞))))
                   100)
 (build-test-cases '(or/e (cons/e (trace/e 0 (below/e ∞))
                                  (trace/e 1 (below/e ∞)))
                          (trace/e 2 (below/e ∞)))
                   100)
 (build-test-cases '(map/e swap-cons swap-cons (cons/e (below/e ∞) (below/e ∞)))
                   100)
 (build-test-cases '(dep/e inf (below/e ∞) nat->map-of-swap-zero-with)
                   100))

;; missing dep/e
