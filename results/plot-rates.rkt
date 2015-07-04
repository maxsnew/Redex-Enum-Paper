#lang racket
(require plot/pict
         pict
         rackunit
         racket/gui/base
         "plot-lines.rkt"
         "process-data.rkt")

(provide rate-plots)

(define rates (read-rate-for-directory))

;; this merges different benchmark/bug names
;; into related sets and those sets are then averaged
(define (name-merge name)
  (regexp-replace #rx"-[0-9]+$" name ""))


(define merged-names
  (sort
   (set->list
    (for/set ([rate (in-list rates)])
      (name-merge (list-ref rate 0))))
   string<?))

(define (harmonic-mean lst)
  (/ (length lst)
     (apply + (map / lst))))
(check-equal? (harmonic-mean '(40 60)) 48)

;; the table
(define name-gen->rate-ht (make-hash))

;; step one: fill the table -- maps to lists of numbers
(for ([rate (in-list rates)])
  (define key (cons (name-merge (list-ref rate 0))
                    (list-ref rate 1)))
  (hash-set! name-gen->rate-ht
             key
             (cons (list-ref rate 2) (hash-ref name-gen->rate-ht key '()))))

;; step two: replace the lists with averages
(for ([key (in-list (hash-keys name-gen->rate-ht))])
  (hash-set! name-gen->rate-ht key
             (harmonic-mean (hash-ref name-gen->rate-ht key))))

(define (name-gen->rate name gen)
  (hash-ref name-gen->rate-ht (cons name gen) #f))
  
(define (mk-plot which legend?)

  (define (mk-hist gen offset line-color color style lab)
    (discrete-histogram
     #:color color
     #:style style
     #:x-min offset
     #:line-color line-color
     #:label (and legend? lab)
     #:skip 4
     (for/list ([merged-name (in-list merged-names)])
       (vector merged-name (or (name-gen->rate merged-name gen) 0)))))

  (parameterize ([plot-x-tick-label-angle 45]
                 [plot-x-tick-label-anchor 'right])
    (plot-pict
     #:legend-anchor 'top-right
     #:x-label (type-name->generic-description which)
     #:y-label "Examples Tested per Second"
     #:width 300
     #:height 300
     (list (mk-hist which
                    0 "black" "white" 'solid "Fair")
           (mk-hist (string->symbol (format "~a-mildly-unfair" which))
                    1 "blue" "navy" 'bdiagonal-hatch "Mildly Unfair")
           (mk-hist (string->symbol (format "~a-brutally-unfair" which))
                    2 "red" "firebrick" 'solid "Brutally Unfair")))))


(define (rate-plots)
  (hc-append 20
             (mk-plot 'ordered #t)
             (mk-plot 'enum #f)))

(module+ main (rate-plots))