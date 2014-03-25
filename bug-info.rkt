#lang racket
(require math/statistics)

(provide get-line-count
         get-counterexample
         get-error
         get-diff
         get-category
         get-counterexample-size
         all-types/nums
         type->num->cat
         get-p-value/mean/stddev)

;; the "get" functions all have the interface
;; symbol natural -> the data
;; symbol is 'stlc etc., and the nat is the bug number
;; (except get-line count, which gets the base file LOC)

(define type->files
  (hash 'stlc '("stlc/stlc-base.rkt")
        'poly-stlc '("poly-stlc/poly-stlc-base.rkt")
        'stlc-sub '("stlc-sub/stlc-sub-base.rkt")
        'rbtrees '("rbtrees/rbtrees-base.rkt")
        'list-machine '("list-machine/list-machine-base.rkt")
        'delim-cont '("delim-cont/delim-cont-base.rkt")
        'rvm '("rvm/verification-base.rkt"
               "../racket-machine/grammar.rkt"
               "../racket-machine/reduction.rkt")))
(define (type->base-file type) (car (hash-ref type->files type)))


;; the order of this list is intended to match the
;; order of the subsections in the benchmark section
(define type->numof/order
  '((stlc 9)
    (poly-stlc 9)
    (stlc-sub 9)
    (list-machine 3)
    (rbtrees 3)
    (delim-cont 3)
    (rvm there-is-no-number-here)))

(define rvm-nums '(2 3 4 5 6 14 15))

(define all-types/nums
  (for*/list ([t (in-list (map car type->numof/order))]
              [n (if (equal? t 'rvm)
                     (in-list rvm-nums)
                     (in-range 1 (add1 (cadr (assoc t type->numof/order)))))])
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
         8 'U
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
         8 'U
         9 'S)
   'stlc-sub
   ; stlc-sub: 1S 2S 3S 4M 5SM
   (hash 1 'S
         2 'S
         3 'S
         4 'D
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
   (hash 1 'M
         2 'M
         3 'S)
   'delim-cont
   ; delim-cont: 1M 2M 3SD
   (hash 1 'M
         2 'M
         3 'S)
   'rvm
   ; rvm: 2? 3D 4M 5M 6M 14M 15S
   (hash 2 'M
         3 'D
         4 'M
         5 'M
         6 'M
         14 'M
         15 'S)))

(define (get-category type num)
  (hash-ref (hash-ref type->num->cat type) num))

(define (get-line-count type)
  (number->string
   (for/sum ([file (in-list (hash-ref type->files type))])
     (define path (bmark-path file))
     (line-count path))))

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
  (count-depth cx))

(define (get-counterexample type num)
  (define base (type->base-file type))
  (define path (bmark-path (regexp-replace "base" base (number->string num))))
  (dynamic-require path 'small-counter-example))

(define (get-diff type num)
  (define base (type->base-file type))
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
  (define base (type->base-file type))
  (define path (bmark-path (regexp-replace "base" base (number->string num))))
  (dynamic-require path 'the-error))

(define (get-p-value/mean/stddev type)
  (define base-file (bmark-path (type->base-file type)))
  (define exp
    (call-with-input-file base-file
      (λ (port)
        (parameterize ([read-accept-reader #t])
          (read port)))))
  (define pick-an-index-arguments
    (flatten
     (let loop ([exp exp])
       (match exp
         [`(pick-an-index ,n) (list n)]
         [(? list?)
          (map loop exp)]
         [_ '()]))))
  
  (cond
    [(= 1 (length pick-an-index-arguments))
     (define p-value (car pick-an-index-arguments))
     (define mean/stddev (hash-ref avg/stddev-table type))
     (values p-value
             (list-ref mean/stddev 0)
             (list-ref mean/stddev 1))]
    [else
     (error 'get-p-value "found ~a p-values~a"
            (length pick-an-index-arguments)
            (if (null? pick-an-index-arguments)
                ""
                (format ": ~s" pick-an-index-arguments)))]))

(define (build-avg/stddev-table)
  (parameterize ([pretty-print-exact-as-decimal #t]
                 [pretty-print-columns 80])
    (pretty-print
     (for/hash ([(type v) (in-hash type->files)])
       (values type (build-avg/stddev-table-entry type))))))

(define (build-avg/stddev-table-entry type)
  (define base-file (bmark-path (type->base-file type)))
  (define generate-enum-term (dynamic-require base-file 'generate-enum-term))
  (define terms
    (for/list ([i (in-range 10000)])
      (generate-enum-term)))
  (define depths (map count-depth terms))
  (define sizes (map count-size terms))
  (list (mean depths) (stddev depths) (mean sizes) (stddev sizes)))

(define (count-depth l)
  (cond
    [(list? l) (+ 1 (apply max 0 (map count-depth l)))]
    [else 1]))

(define (count-size l)
  (cond
    [(list? l) (apply + 1 (map count-size l))]
    [else 1]))

(module+ test
  (require rackunit)
  (check-equal? (count-depth 1) 1)
  (check-equal? (count-depth '(1)) 2)
  (check-equal? (count-depth '((1))) 3)
  (check-equal? (count-depth '((1) (1))) 3)
  (check-equal? (count-depth '((1) (1) (1) (1 1 1 1 1 1))) 3)
  (check-equal? (count-size 1) 1)
  (check-equal? (count-size '(1)) 2)
  (check-equal? (count-size '((1))) 3)
  (check-equal? (count-size '((1) (1))) 5)
  (check-equal? (count-size '((1) (1) (1) (1 1 1 1 1 1))) 14))

; (build-avg/stddev-table) ;; run this to recompute the table
(define avg/stddev-table
  #hash((list-machine . (3.9256 0.7572744812813911  13.0908 4.471057521437182))
        (stlc         . (3.4735 2.862358773808762   14.1735 20.76807159439701))
        (poly-stlc    . (3.9584 3.001178008715911   17.3118 23.658537164414877))
        (stlc-sub     . (3.454  2.8536089430754172  14.0571 20.59367474711592))
        (rbtrees      . (4.3012 6.984588646441535   15.8224 17.856753855054396))
        (delim-cont   . (3.5616 1.7361467219103344  11.6961 9.77507773830981))
        (rvm          . (2.9441 1.6180158188349087  16.1823 21.343417409355983))))
