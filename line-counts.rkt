#lang racket

(provide get-line-count
         get-counterexample
         get-error
         get-diff
         counterexample-size)

(define type->base-files
  (hash 'stlc "stlc/stlc-base.rkt"
        'poly-stlc "poly-stlc/poly-stlc-base.rkt"
        'stlc-sub "stlc-sub/stlc-sub-base.rkt"
        'rbtrees "rbtrees/rbtrees-base.rkt"
        'list-machine "list-machine/list-machine-base.rkt"
        'delim-cont "delim-cont/delim-cont-base.rkt"
        'rvm "rvm/verification-base.rkt"))

(define (get-line-count type)
  (define path (bmark-path (hash-ref type->base-files type)))
  (number->string (line-count path)))

(define (bmark-path file)
  (collection-file-path file "redex" "examples" "benchmark"))

(define (line-count path)
  (call-with-input-file path
    (λ (in)
      (length
       (for/list ([line (in-lines in)]
                  #:unless (white-space/comment? line))
         'line)))))

(define (white-space/comment? line)
  (or (regexp-match? #rx"^[ \t]*$" line)
      (regexp-match? #rx"^;.*$" line)))

(define (counterexample-size type num)
  (define cx (get-counterexample type num))
  (count-pairs cx))

(define (get-counterexample type num)
  (define base (hash-ref type->base-files type))
  (define path (bmark-path (regexp-replace "base" base (number->string num))))
  (dynamic-require path 'small-counter-example))

(define (count-pairs sexp)
  (cond
    [(pair? sexp)
     (+ 1 
        (count-pairs (car sexp))
        (count-pairs (cdr sexp)))]
    [else 0]))

(define (get-diff type num)
  (define base (hash-ref type->base-files type))
  (define path (bmark-path (regexp-replace "/.*base.rkt" base 
                                           (string-append "/"
                                                          (number->string num)
                                                          ".diff"))))
  (call-with-input-file path
    (λ (in)
      (apply string-append
             (add-between
              (for/list ([l (in-lines in)]) l)
              "\n")))))

(define (get-error type num)
  (define base (hash-ref type->base-files type))
  (define path (bmark-path (regexp-replace "base" base (number->string num))))
  (dynamic-require path 'the-error))
  