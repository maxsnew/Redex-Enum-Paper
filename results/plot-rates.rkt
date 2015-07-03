#lang racket
(require plot
         pict
         "plot-lines.rkt"
         "process-data.rkt")

(provide rate-plots)

(define rates (read-rate-for-directory))
(define names
  (sort
   (set->list
    (for/set ([rate (in-list rates)])
      (list-ref rate 0)))
   string<?))

(define name-gen->rate-ht (make-hash))
(for ([rate (in-list rates)])
  (hash-set! name-gen->rate-ht
             (cons (list-ref rate 0) (list-ref rate 1))
             (list-ref rate 2)))

(define (name-gen->rate name gen)
  (hash-ref name-gen->rate-ht (cons name gen) #f))
  
(define (mk-plot which)

  (define (mk-hist gen offset)
    (discrete-histogram
     #:color (case offset
               [(0) 0]
               [(1) "gray"]
               [(2) "black"])
     #:x-min offset
     #:skip 4
     (for/list ([name (in-list names)])
       (vector name (or (name-gen->rate name gen) 0)))))

  (parameterize ([plot-x-tick-label-angle 75]
                 [plot-x-tick-label-anchor 'right])
    (plot-pict
     #:x-label (type-name->generic-description which)
     #:y-label "Examples per second"
     #:width 600
     #:height 300
     (list (mk-hist which 0)
           (mk-hist (string->symbol (format "~a-mildly-unfair" which)) 1)
           (mk-hist (string->symbol (format "~a-brutally-unfair" which)) 2)))))


(define (rate-plots)
  (vc-append 20
             (mk-plot 'enum)
             (mk-plot 'ordered)))
