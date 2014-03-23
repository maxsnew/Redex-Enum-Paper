#lang racket

(provide get-line-count
         get-counterexample
         get-error
         get-diff
         get-category
         get-counterexample-size
         all-types/nums)

;; the "get" functions all have the interface
;; symbol natural -> the data
;; symbol is 'stlc etc., and the nat is the bug number
;; (except get-line count, which gets the base file LOC)

(define type->base-files
  (hash 'stlc "stlc/stlc-base.rkt"
        'poly-stlc "poly-stlc/poly-stlc-base.rkt"
        'stlc-sub "stlc-sub/stlc-sub-base.rkt"
        'rbtrees "rbtrees/rbtrees-base.rkt"
        'list-machine "list-machine/list-machine-base.rkt"
        'delim-cont "delim-cont/delim-cont-base.rkt"
        'rvm "rvm/verification-base.rkt"))

(define type->numof
  (hash 'stlc 9
        'poly-stlc 9
        'stlc-sub 9
        'list-machine 3
        'rbtrees 3
        ;; delim cont should be 3!
        ;; but 3 needs a counterexample
        ;; also it has never been found
        'delim-cont 2))

(define rvm-nums '(2 3 4 5 6 14 15))

(define all-types/nums
  (for*/list ([t (in-list (hash-keys type->base-files))]
              [n (if (equal? t 'rvm)
                     (in-list rvm-nums)
                     (in-range 1 (add1 (hash-ref type->numof t))))])
    (list t n)))


(define type->num->cat
  (hash 
   'stlc 
   ; stlc: 1S 2M 3S 4S 5S 6M 7M 8? 9S
   (hash 1 'S
         2 'M
         3 'S
         4 'S
         5 'S
         6 'M
         7 'M
         8 '?
         9 'S)
   'poly-stlc
   ; poly-stlc: 1S 2M 3S 4S 5S 6M 7M 8? 9S
   (hash 1 'S
         2 'M
         3 'S
         4 'S
         5 'S
         6 'M
         7 'M
         8 '?
         9 'S)
   'stlc-sub
   ; stlc-sub: 1S 2S 3S 4M 5SM
   (hash 1 'S
         2 'S
         3 'S
         4 'MD ;; adjusted to MD as Robby and Jay disagreed
         5 'SM
         6 'S
         7 'S
         8 'S
         9 'SM)
   'list-machine
   ; list-machine: 1S 2M 3S
   (hash 1 'S
         2 'M
         3 'S)
   'rbtrees
   ; rbtrees: 1SD 2SM 3SMD
   (hash 1 'SD
         2 'SM
         3 'SMD)
   'delim-cont
   ; delim-cont: 1M 2M 3SD
   (hash 1 'M
         2 'M
         3 'SD)
   'rvm
   ; rvm: 2? 3D 4M 5M 6M 14M 15S
   (hash 2 '?
         3 'D
         4 'M
         5 'M
         6 'M
         14 'M
         15 'S)))

(define (get-category type num)
  (hash-ref (hash-ref type->num->cat type) num))

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
      (regexp-match? #rx"^[ \t]*;.*$" line)))

(define (get-counterexample-size type num)
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
  