#lang racket

(require redex/examples/benchmark/graph-data
         racket/runtime-path
         pict)

(provide res-plot-4hour)

(define-runtime-path 4-hour "4-hour/4-hour-all.rktd")

(define (res-plot-4hour)
  (scale
   (plot-results (list (path->string 4-hour)))
   0.5))

(define (plot-results fname)
  (parameterize ([confidence-interval #t]
                 [order-by 'grammar]
                 [types '(grammar enum ordered)])
    (make-plot fname)))