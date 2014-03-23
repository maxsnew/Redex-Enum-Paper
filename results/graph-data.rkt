#lang racket/base


;                                                       
;                                                       
;                                                       
;                                                       
;  ;;;  ;;;  ;;;                    ;;;                 
;  ;;;  ;;;  ;;;                                        
;   ;;  ;;;  ;; ;;;;;  ;;; ;;;; ;;  ;;; ;;; ;;   ;; ;;; 
;   ;; ;; ;; ;;;;;;;;; ;;;;;;;;;;;; ;;; ;;;;;;; ;;;;;;; 
;   ;; ;; ;; ;;;;  ;;; ;;;  ;;; ;;; ;;; ;;; ;;; ;;; ;;; 
;   ;;;;; ;;;;;  ;;;;; ;;;  ;;; ;;; ;;; ;;; ;;; ;;; ;;; 
;    ;;;; ;;;;;;;; ;;; ;;;  ;;; ;;; ;;; ;;; ;;; ;;; ;;; 
;    ;;;   ;;; ;;; ;;; ;;;  ;;; ;;; ;;; ;;; ;;; ;;;;;;; 
;    ;;;   ;;;  ;;;;;; ;;;  ;;; ;;; ;;; ;;; ;;;  ;; ;;; 
;                                                   ;;; 
;                                               ;;;;;;  
;                                                       
;                                                       
;; this is copied code from redex/examaples/benchmark/graph-data

(require racket/list
         racket/match
         math/statistics
         math/distributions
         redex/examples/benchmark/apply-diffs)

(provide process-data
         load-raw
         type-colors)


(define all-types '(grammar search search-gen search-gen-enum search-gen-ref search-gen-enum-ref enum ordered))
(define colors  '(1 4 5 6 7 8 2 3))    
(define type-colors
  (for/hash ([t all-types] [c colors])
    (values t c)))


(define (load-raw filenames)
  (define raw-data
    (apply append
           (for/list ([f filenames])
             (call-with-input-file f
               (λ (in)
                 (read in))))))
  (let loop ([fixed-data '()]
                 [rest raw-data])
        (cond
          [(null? rest) fixed-data]
          [((length rest) . >= . 3)
           (loop (cons (take rest 3) fixed-data)
                 (drop rest 3))]
          [else
           (error 'data "is the wrong length!")])))

(define (process-data data)
  (let loop ([d data]
             [sorted-times (hash)]) 
    (match d
      [(cons (list name type time) rest)
       (loop rest
             (hash-set sorted-times (cons name type)
                       (cons (/ time 1000)
                             (hash-ref sorted-times (cons name type)
                                       (λ () '())))))]
      ['()
       (for/fold ([dstats '()] [name-avgs (for/hash ([b (in-list (all-bug-files))])
                                            (values b '()))])
         ([(name/type times) (in-hash sorted-times)]
          #:unless (and ((length times) . < . (min-trials))
                        (not (equal? (cdr name/type) 'ordered))))
         (define name (last (regexp-split #rx"/" (car name/type))))
         (values
          (cons (list (car name/type)
                      (cdr name/type)
                      (mean times)
                      (if (equal? (cdr name/type) 'ordered)
                          0
                          (error-bar times))) dstats)
          (cond 
            [(equal? (cdr name/type) (order-by))
             (hash-set name-avgs name (mean times))]
            [(list? (hash-ref name-avgs name '()))
             (hash-set name-avgs 
                       name
                       (cons (mean times) (hash-ref name-avgs name '())))]
            [else name-avgs])))])))
(define min-trials (make-parameter 2))
(define (error-bar times)
  (define sdev (stddev times #:bias #t))
  (define this-z (if (> (length times) 30)
                     z
                     (hash-ref t-inv-cdf-97.5 (sub1 (length times)))))
  (if (confidence-interval)
      (/ (* z sdev) (sqrt (length times)))
      (/ (stddev times #:bias #t) (sqrt (length times)))))





(define types (make-parameter '()))
(define names '("adhoc random" "search" "backjumping" "backjumping, ordered space" "backjumping, with refresh"
                               "backjumping, ordered space with refresh" "uniform random"
                               "in-order enumeration"))
(define symbols '(circle triangle square asterisk diamond plus   5star diamond))
(define type-names
  (for/hash ([t all-types] [n names])
    (values t n)))
(define type-symbols
  (for/hash ([t all-types] [s symbols])
    (values t s)))

(define confidence-interval (make-parameter #f))
(define order-by (make-parameter #f))
(define max-t (make-parameter #f))
(define offset? (make-parameter #f))
(define min-y (make-parameter 0.01))

(define output-file (make-parameter #f))


(define (bug-file? f)
    (define m (regexp-match #rx"^.*/(.*-[0-9]\\.rkt)$"
                            (path->string f)))
    (and m
        (second m)))

(define (all-bug-files)
  (sort
   (flatten
    (for/list ([d (in-list (get-directories directories))])
      (for/list ([f (in-directory d)]
                 #:when (bug-file? f))
        (bug-file? f))))
   string<?))

(define z (inv-cdf (normal-dist) 0.975))


(define t-inv-cdf-97.5
  (hash 1 12.706
        2 4.303
        3 3.182
        4 2.776
        5 2.571
        6 2.447
        7 2.365
        8 2.306
        9 2.262
        10 2.228
        11 2.201
        12 2.129
        13 2.160
        14 2.145
        15 2.131
        16 2.120
        17 2.110
        18 2.101
        19 2.093
        20 2.086
        21 2.080
        22 2.074
        23 2.069
        24 2.064
        25 2.060
        26 2.056
        27 2.052
        28 2.048
        29 2.045
        30 2.042))

