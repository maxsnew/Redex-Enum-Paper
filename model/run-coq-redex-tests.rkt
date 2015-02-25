#lang at-exp racket

(require "model.rkt" racket/runtime-path)

;; this file gets overwritten
(define-runtime-path scratch.coq "scratch.v")

(define (check fn) (and (file-exists? fn) 
                        (string->path fn)))
(define coqc
  (or (find-executable-path "coqc")
      (check "/opt/local/bin/coqc")))

(unless coqc (error 'run-coq-redex-tests.rkt "couldn't find coqc"))

(define coq-prefix
  @list{Unset Printing Notations.
        Set Printing Depth 10000.
        Require Import Enum.
        
        Definition show_one (e : Enum) (n : nat) : Value * Trace :=
          proj1_sig (Enumerates_from_dec e n).

        Eval compute in show_one (E_Trace zero E_Nat) 5.
        Eval compute in show_one (E_Sum E_Nat E_Nat) 5.})

(call-with-output-file scratch.coq
  (λ (port)
    (for ([line (in-list coq-prefix)])
      (display line port)
      (newline port)))
  #:exists 'replace)

(define (run-file)
  (define sp (open-output-string))
  (parameterize ([current-input-port (open-input-string "")]
                 [current-output-port sp])
    (system* coqc 
             "-R"
             (simplify-path (let-values ([(base name dir?) (split-path scratch.coq)])
                              (build-path base 'up "model")))
             "Enum"
             scratch.coq))
  (define resultsp (open-input-string (get-output-string sp)))
  (define raw-results
    (let loop ()
      (define r (read resultsp))
      (if (eof-object? r)
          '()
          (cons r (loop)))))
  raw-results)

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

(define (to-racket exp)
  (let loop ([exp exp])
    (match exp
      [`(pair ,a ,b) (coq-pair (loop a) (loop b))]
      [`(cons ,a ,b) (cons (loop a) (loop b))]
      [`nil '()]
      [`(S ,n) (+ (loop n 1))]
      [O 0])))
    
(properly-parenthesize-and-convert-results (run-file))
