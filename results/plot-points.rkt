#lang racket

(provide plot-points-from-directory
         maximum-bugs-found
         (contract-out
          [way-betters
           (-> (hash/c (apply or/c (hash-keys type-syms))
                       (listof string?)))]))
(require racket/draw
         pict
         plot
         redex/benchmark/private/graph-data
         "process-data.rkt"
         "plot-lines.rkt")

(define type-syms
  (hash 'grammar 'triangle
        'ordered 'asterisk
        'ordered-mildly-unfair 'otimes
        'ordered-brutally-unfair 'oasterisk
        'enum 'plus
        'enum-mildly-unfair 'circle
        'enum-brutally-unfair 'oplus))
        
(define (plot-points-from-directory [output #f])
  (define-values (all-names data-stats name-avgs max-non-f-value-from-list-ref-d2)
    (apply values (read-data-for-directory)))

  (set! data-stats (sort data-stats <
                         #:key (λ (x) (hash-ref order (list-ref x 1)))))
  (parameterize ([type-names type-name->description]
                 [plot-width 600]
                 [plot-height 500]
                 [plot-x-label #f]
                 [type-symbols (λ (x) (hash-ref type-syms x))]
                 [plot-y-label "Average Number of Seconds to Find Bug"])
    (define pict
      (make-plot/data-stats/name-avgs data-stats name-avgs all-names
                                      max-non-f-value-from-list-ref-d2
                                      #t))
    (cond
      [output
       (define dc (new pdf-dc% [output output] [interactive #f] [use-paper-bbox #f] [as-eps #t]))
       (send dc start-doc "")
       (send dc start-page)
       (draw-pict pict dc 0 0)
       (send dc end-page)
       (send dc end-doc)]
      [else pict])))

(define (maximum-bugs-found)
  (define-values (all-names data-stats name-avgs max-non-f-value-from-list-ref-d2)
    (apply values (read-data-for-directory)))
  (define ht (make-hash))
  (for ([data-stat (in-list data-stats)])
    (define k (list-ref data-stat 1))
    (hash-set! ht k (+ (hash-ref ht k 0) 1)))
  (apply max (hash-values ht)))

(define (way-betters)
  (define-values (all-names data-stats name-avgs max-non-f-value-from-list-ref-d2)
    (apply values (read-data-for-directory)))

  ;; info : [bug -o> (listof (cons generator time))]
  (define info (make-hash))
  
  (for ([data-stat (in-list data-stats)])
    (define bug (list-ref data-stat 0))
    (define gen-method (list-ref data-stat 1))
    (define time-taken (list-ref data-stat 2))
    (hash-set! info bug (cons (cons gen-method time-taken) (hash-ref info bug '()))))

  (define (<< a b)
    (define amag (/ (log a) (log 10)))
    (define bmag (/ (log b) (log 10)))
    (< (+ amag 1) bmag))

  (define ans (make-hash))
  
  (for ([(bug time/gens) (in-hash info)])
    (define best (argmin cdr time/gens))
    (define sorted (sort time/gens < #:key cdr))
    (define much-better?
      (and (> (length time/gens) 1)
           (for/and ([i (in-list time/gens)])
             (or (equal? (car i) (car best))
                 (<< (cdr best) (cdr i))))))
    (when much-better?
      (hash-set! ans (car best) (cons bug (hash-ref ans (car best) '())))))

  ans)
  
(module+ main
  (plot-points-from-directory "points-plot.pdf"))