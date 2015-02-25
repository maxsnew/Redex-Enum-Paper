#lang at-exp racket

(require (prefix-in m: "model.rkt" )
         racket/runtime-path
         redex/reduction-semantics
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
  (-> m:e? exact-nonnegative-integer? (listof test-case?))
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
        (coq-pair (coq-pair coq-v coq-trace)
                  (coq-pair coq-n _coq-backwards-trace)))
       (define-values (redex-v redex-trace) (m:from-nat+trace redex-e orig-n))
       (define (fail fmt-str . args)
         (eprintf "FAILED:\n enum: ~s\n n: ~s\n val: ~s\n ~a\n\n"
                  redex-e 
                  orig-n 
                  val
                  (apply format fmt-str args)))
       (unless (equal? orig-n coq-n)
         (fail "different nats; coq-n ~a" coq-n))
       (unless (equal? coq-v val)
         (fail "different values; coq-v ~a" coq-v))
       (unless (equal? redex-v val)
         (fail "different values; redex-v ~a" redex-v))
       (unless (equal? coq-trace redex-trace)
         (fail "different traces:\n    coq ~s\n  redex ~s" 
               coq-trace
               redex-trace))])))

(define coq-prefix
  @list{Unset Printing Notations.
        Set Printing Depth 10000.
        Require Import Enum.
        
        Definition from_nat e n := 
          proj1_sig (Enumerates_from_dec e n).
          
        Definition to_nat e v :=
          match (Enumerates_to_dec e v) with
           | inleft x => Some (proj1_sig x)
           | inright _ => None
          end.})

(define (run-some-in-coq test-cases)
  (define results
    (run-coq
     (λ (port)
       (define (o str) (display str port))
       (define (o-enum e)
         (match e
           [`natural/e (o "E_Nat")]
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
           [`(map/e ,f1 ,f2 ,e)
            (o "(E_Map ")
            (match* (f1 f2)
              [(`(add ,i1) `(add ,i1)) 1]
              [(_ _) 2])]
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
           [(`natural/e (? number?))
            (o (format "(V_Nat ~a)" v))]
           [(`(cons/e ,e1 ,e2) (cons a b))
            (o "(V_Pair ")
            (o-v e1 a)
            (o " ")
            (o-v e2 b)
            (o ")")]
           ;; map goes here
           ;; dep goes here
           [(`(or/e ,e1 ,e2) (cons 0 b))
            (o "(V_Sum_Left ")
            (o-v e1 b)
            (o ")")]
           [(`(or/e ,e1 ,e2) (cons 1 b))
            (o "(V_Sum_Right ")
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
    (system* coqc 
             "-R"
             (simplify-path (let-values ([(base name dir?) (split-path scratch.v)])
                              (build-path base 'up "model")))
             "Enum"
             scratch.v))
  (define resultsp (open-input-string (get-output-string sp)))
  (define raw-results
    (let loop ()
      (define r (read resultsp))
      (if (eof-object? r)
          '()
          (cons r (loop)))))
  (properly-parenthesize-and-convert-results raw-results))

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
      [`(pair ,a ,b) (coq-pair (loop a) (loop b))]
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
      [`(V_Nat ,n) (loop n)]
      ;; V_Pairs are just 'cons' pairs in the Redex model
      [`(V_Pair ,a ,b) (cons (loop a) (loop b))]
      [`(V_Sum_Right ,v) 
       ;; right sums in the Coq model match up to the `or r' rule in the Redex model
       (cons 1 (loop v))]
      [`(V_Sum_Left ,v) 
       ;; left sums in the Coq model match up to the `or l' rule in the Redex model
       (cons 0 (loop v))])))

(run-tests
 (build-test-cases 'natural/e 100)
 (build-test-cases '(cons/e natural/e natural/e) 100)
 (build-test-cases '(or/e natural/e natural/e) 100)
 (build-test-cases '(cons/e (cons/e (trace/e 0 natural/e)
                                    (trace/e 1 natural/e))
                            (cons/e (trace/e 2 natural/e)
                                    (trace/e 3 natural/e)))
                   100))

    ;; missing map/e, dep/e ...