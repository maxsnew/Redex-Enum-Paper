#lang racket

(require "plot-lines.rkt"
         redex/examples/benchmark/graph-data
         racket/runtime-path
         pict)

(provide (all-defined-out))

(define-runtime-path 4-hour "4-hour")
(define-runtime-path 24-hour "24-hour")

(define (res-plot-4hour)
  (scale
   (plot-results
    (dir->files 4-hour))
   0.5))

(define (dir->files d)
  (for/list ([f (in-directory d)]) 
    (path->string (path->complete-path f))))

(define (res-plot-24hour)
  (scale
   (plot-results
    (dir->files 24-hour))
   0.5))

(define (plot-results fnames)
  (parameterize ([confidence-interval #t]
                 ;[order-by 'grammar]
                 [types '(grammar enum ordered)])
    (make-plot fnames)))

(define (line-plot-4hour)
  (plot-from-files (dir->files 4-hour)))

(define (line-plot-24hour)
  (plot-from-files (dir->files 24-hour)))